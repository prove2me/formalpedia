-- Prove2me | solution 1 for GEPPGrowth.Main.lemma_4_6
-- status  : ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-26T21:49:48.509967+00:00
-- url     : https://prove2.me/submissions/53499d94-9837-4097-98fd-9efb341203ff

import Mathlib
import Definitions.Def_GEPPGrowth_Main_Process

open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators Matrix

noncomputable section

namespace GEPPLemma46

open GEPPGrowth.Main

/-- The orthogonal group `O(n)` as a compact topological group. -/
abbrev OG (n : ℕ) := Matrix.orthogonalGroup (Fin n) ℝ

instance (n : ℕ) : CompactSpace (OG n) := by
  have hK : IsCompact ((Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => Set.Icc (-1 : ℝ) 1 :
      Set (Matrix (Fin n) (Fin n) ℝ))) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  have hc : IsCompact ((OG n : Set (Matrix (Fin n) (Fin n) ℝ))) := by
    refine hK.of_isClosed_subset (isClosed_unitary (R := Matrix (Fin n) (Fin n) ℝ)) fun U hU => ?_
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
    intro i j
    have := entry_norm_bound_of_unitary hU i j
    rw [Real.norm_eq_abs] at this
    exact abs_le.1 this
  exact isCompact_iff_compactSpace.1 hc

instance (n : ℕ) : MeasurableSpace (OG n) := borel _
instance (n : ℕ) : BorelSpace (OG n) := ⟨rfl⟩

/-- Normalized Haar measure on `O(n)`. -/
def haarO (n : ℕ) : Measure (OG n) := Measure.haarMeasure ⊤

instance (n : ℕ) : IsProbabilityMeasure (haarO n) := ⟨by
  have := Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (OG n)))
  rwa [TopologicalSpace.PositiveCompacts.coe_top] at this⟩

instance (n : ℕ) : (haarO n).IsMulLeftInvariant := by
  unfold haarO; infer_instance

lemma OG_tr_mul {n : ℕ} (O : OG n) :
    (O : Matrix (Fin n) (Fin n) ℝ)ᵀ * (O : Matrix (Fin n) (Fin n) ℝ) = 1 := by
  exact (Matrix.mem_orthogonalGroup_iff' _ _).1 O.2

lemma OG_mul_tr {n : ℕ} (O : OG n) :
    (O : Matrix (Fin n) (Fin n) ℝ) * (O : Matrix (Fin n) (Fin n) ℝ)ᵀ = 1 := by
  exact (Matrix.mem_orthogonalGroup_iff _ _).1 O.2

lemma upper_mul_diag {p : ℕ} {A B : Mat p} (hA : ∀ i j, j < i → A i j = 0)
    (hB : B.BlockTriangular id) (i : Fin p) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hA i k h, zero_mul]
    · rw [hB h, mul_zero]
  · simp

/-- Uniqueness of the thin QR factorization with positive diagonal. -/
lemma thinQR_unique {n p : ℕ} {G Q₁ Q₂ : Matrix (Fin n) (Fin p) ℝ} {R₁ R₂ : Mat p}
    (h₁ : ThinQR G Q₁ R₁) (h₂ : ThinQR G Q₂ R₂) : Q₁ = Q₂ ∧ R₁ = R₂ := by
  obtain ⟨hG1, hQ1, hU1, hD1⟩ := h₁
  obtain ⟨hG2, hQ2, hU2, hD2⟩ := h₂
  have hb1 : R₁.BlockTriangular id := fun i j h => hU1 i j h
  have hb2 : R₂.BlockTriangular id := fun i j h => hU2 i j h
  have hdet1 : R₁.det ≠ 0 := by
    rw [Matrix.det_of_isUpperTriangular hb1]; exact (Finset.prod_pos fun i _ => hD1 i).ne'
  have hdet2 : R₂.det ≠ 0 := by
    rw [Matrix.det_of_isUpperTriangular hb2]; exact (Finset.prod_pos fun i _ => hD2 i).ne'
  let : Invertible R₁ := Matrix.invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.2 hdet1)
  let : Invertible R₂ := Matrix.invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.2 hdet2)
  have hgram : R₁ᵀ * R₁ = R₂ᵀ * R₂ := by
    have e : ∀ (Q : Matrix (Fin n) (Fin p) ℝ) (R : Mat p), Qᵀ * Q = 1 → (Q * R)ᵀ * (Q * R) = Rᵀ * R :=
      fun Q R hQ => by
        rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Qᵀ, hQ, Matrix.one_mul]
    rw [← e Q₁ R₁ hQ1, ← e Q₂ R₂ hQ2, ← hG1, ← hG2]
  set T := R₁ * R₂⁻¹ with hTdef
  have hTup : T.BlockTriangular id := hb1.mul (Matrix.blockTriangular_inv_of_blockTriangular hb2)
  have hTT : Tᵀ * T = 1 := by
    rw [hTdef, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc R₁ᵀ, hgram,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.transpose_mul, Matrix.mul_assoc,
      Matrix.mul_inv_of_invertible, Matrix.transpose_one, Matrix.one_mul]
  let : Invertible T := invertibleOfLeftInverse _ _ hTT
  have hTinv : T⁻¹ = Tᵀ := Matrix.inv_eq_left_inv hTT
  have hTlo : ∀ i j, i < j → T i j = 0 := fun i j h => by
    have := Matrix.blockTriangular_inv_of_blockTriangular hTup h
    rwa [hTinv] at this
  have hoff : ∀ i j, i ≠ j → T i j = 0 := fun i j h => by
    rcases lt_or_gt_of_ne h with h | h
    · exact hTlo i j h
    · exact hTup h
  have hinvd : ∀ i, 0 < R₂⁻¹ i i := fun i => by
    have h1 := congrFun (congrFun (Matrix.mul_inv_of_invertible R₂) i) i
    rw [upper_mul_diag hU2 (Matrix.blockTriangular_inv_of_blockTriangular hb2) i,
      Matrix.one_apply_eq] at h1
    exact pos_of_mul_pos_right (h1 ▸ one_pos) (hD2 i).le
  have hTd : ∀ i, T i i = 1 := fun i => by
    have hpos : 0 < T i i := by
      rw [hTdef, upper_mul_diag hU1 (Matrix.blockTriangular_inv_of_blockTriangular hb2) i]
      exact mul_pos (hD1 i) (hinvd i)
    have h1 := congrFun (congrFun hTT i) i
    rw [Matrix.mul_apply, Finset.sum_eq_single i (fun k _ hk => by
      rw [Matrix.transpose_apply, hoff k i hk, zero_mul]) (by simp),
      Matrix.transpose_apply, Matrix.one_apply_eq] at h1
    nlinarith
  have hT1 : T = 1 := by
    ext i j
    by_cases h : i = j
    · subst h; rw [hTd, Matrix.one_apply_eq]
    · rw [hoff i j h, Matrix.one_apply_ne h]
  have hR : R₁ = R₂ := by
    rw [← Matrix.inv_mul_cancel_right_of_invertible R₁ (A := R₂), ← hTdef, hT1, Matrix.one_mul]
  subst hR
  refine ⟨?_, rfl⟩
  rw [← Matrix.mul_inv_cancel_right_of_invertible Q₁ (A := R₁), ← hG1, hG2,
    Matrix.mul_inv_cancel_right_of_invertible]

abbrev E (k : ℕ) := EuclideanSpace ℝ (Fin k)

instance (k : ℕ) : SigmaFinite (stdGaussian (E k)) := IsFiniteMeasure.toSigmaFinite _

/-- An orthogonal matrix as a linear isometry of `ℝⁿ`. -/
def rotL {n : ℕ} (O : OG n) : E n ≃ₗᵢ[ℝ] E n :=
  ((Matrix.toEuclideanLin (O : Matrix (Fin n) (Fin n) ℝ)).isometryOfInner fun x y => by
    simp only [Matrix.toEuclideanLin_apply,
      EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
    rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, OG_tr_mul,
      Matrix.vecMul_one]).toLinearIsometryEquiv rfl

lemma rotL_apply {n : ℕ} (O : OG n) (v : E n) :
    rotL O v = toLp 2 ((O : Matrix (Fin n) (Fin n) ℝ) *ᵥ ofLp v) := rfl

/-- Transposing an array of i.i.d. `N(0,1)` entries preserves its law. -/
lemma transpose_mp (m n : ℕ) :
    MeasurePreserving (fun (x : Fin n → Fin m → ℝ) j i => x i j)
      (Measure.pi fun _ => Measure.pi fun _ => gaussianReal 0 1)
      (Measure.pi fun _ => Measure.pi fun _ => gaussianReal 0 1) := by
  have hm : Measurable (fun (x : Fin n → Fin m → ℝ) j i => x i j) := by fun_prop
  refine ⟨hm, (Measure.pi_eq_generateFrom (fun _ => generateFrom_pi) (fun _ => isPiSystem_pi)
    (fun _ => Measure.FiniteSpanningSetsIn.pi fun _ => (gaussianReal 0 1).toFiniteSpanningSetsIn)
    fun s hs => ?_).symm⟩
  choose u hu hus using hs
  have hs' : s = fun j => Set.pi Set.univ (u j) := funext fun j => (hus j).symm
  subst hs'
  have hu' : ∀ j i, MeasurableSet (u j i) := fun j i => hu j i (Set.mem_univ _)
  have hpre : (fun (x : Fin n → Fin m → ℝ) j i => x i j) ⁻¹'
      Set.pi Set.univ (fun j => Set.pi Set.univ (u j)) =
      Set.pi Set.univ (fun i => Set.pi Set.univ (fun j => u j i)) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
    exact forall_comm
  rw [Measure.map_apply hm (MeasurableSet.univ_pi fun j => MeasurableSet.univ_pi (hu' j)), hpre,
    Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  exact Finset.prod_comm

/-- Left multiplication by an orthogonal matrix preserves the law of a Gaussian matrix. -/
lemma gauss_rot {n p : ℕ} (O : OG n) :
    MeasurePreserving (fun G : Matrix (Fin n) (Fin p) ℝ => (O : Matrix (Fin n) (Fin n) ℝ) * G)
      (GaussianMatrix.gaussianMatrix n p) (GaussianMatrix.gaussianMatrix n p) := by
  let τ : (Fin n → Fin p → ℝ) → (Fin p → E n) := fun G j => toLp 2 (fun i => G i j)
  let σ : (Fin p → E n) → (Fin n → Fin p → ℝ) := fun z i j => ofLp (z j) i
  have hA : MeasurePreserving (fun (x : Fin p → Fin n → ℝ) j => toLp 2 (x j))
      (Measure.pi fun _ => Measure.pi fun _ => gaussianReal 0 1)
      (Measure.pi fun _ => stdGaussian (E n)) :=
    measurePreserving_pi _ _ fun _ => ⟨by fun_prop, map_pi_eq_stdGaussian⟩
  have hτ : MeasurePreserving τ (GaussianMatrix.gaussianMatrix n p)
      (Measure.pi fun _ => stdGaussian (E n)) := hA.comp (transpose_mp p n)
  have hσm : Measurable σ := by fun_prop
  have hσ : MeasurePreserving σ (Measure.pi fun _ => stdGaussian (E n))
      (GaussianMatrix.gaussianMatrix n p) := by
    refine ⟨hσm, ?_⟩
    rw [← hτ.map_eq, Measure.map_map hσm hτ.measurable]
    exact Measure.map_id
  have hρ : MeasurePreserving (fun (z : Fin p → E n) j => rotL O (z j))
      (Measure.pi fun _ => stdGaussian (E n)) (Measure.pi fun _ => stdGaussian (E n)) :=
    measurePreserving_pi _ _ fun _ => ⟨(rotL O).continuous.measurable, stdGaussian_map (rotL O)⟩
  have h := (hσ.comp hρ).comp hτ
  have e : ((σ ∘ fun (z : Fin p → E n) j => rotL O (z j)) ∘ τ) =
      fun G : Matrix (Fin n) (Fin p) ℝ => (O : Matrix (Fin n) (Fin n) ℝ) * G := by
    funext G i j
    simp [σ, τ, rotL_apply, Matrix.mulVec, dotProduct]
    rfl
  rw [e] at h
  exact h

/-- The standard point of the Stiefel set: the first `p` coordinate vectors. -/
def q₀ {n p : ℕ} (hnp : p ≤ n) : Matrix (Fin n) (Fin p) ℝ :=
  fun i j => if i = Fin.castLE hnp j then 1 else 0

/-- `O(n)` acts transitively on `n × p` matrices with orthonormal columns. -/
lemma exists_orth {n p : ℕ} (hnp : p ≤ n) (q : Matrix (Fin n) (Fin p) ℝ) (hq : qᵀ * q = 1) :
    ∃ U : OG n, q = (U : Matrix (Fin n) (Fin n) ℝ) * q₀ hnp := by
  let v : Fin n → E n := fun k => if h : k.val < p then toLp 2 (fun i => q i ⟨k, h⟩) else 0
  let s : Set (Fin n) := {k | k.val < p}
  have hv : Orthonormal ℝ (s.domRestrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨k, hk⟩ ⟨l, hl⟩
    have hk' : k.val < p := hk
    have hl' : l.val < p := hl
    have := congrFun (congrFun hq ⟨k, hk'⟩) ⟨l, hl'⟩
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at this
    have e : ((⟨k.val, hk'⟩ : Fin p) = ⟨l.val, hl'⟩) ↔ k = l := by
      rw [Fin.mk.injEq, Fin.val_inj]
    change inner ℝ (v k) (v l) = if (⟨k, hk⟩ : s) = ⟨l, hl⟩ then 1 else 0
    simp only [v, dif_pos hk', dif_pos hl', EuclideanSpace.inner_toLp_toLp, dotProduct,
      star_trivial, Subtype.mk.injEq]
    simp only [e] at this
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp)
  refine ⟨⟨(EuclideanSpace.basisFun (Fin n) ℝ).toBasis.toMatrix b,
    (EuclideanSpace.basisFun (Fin n) ℝ).toMatrix_orthonormalBasis_mem_orthogonal b⟩, ?_⟩
  ext i j
  have hj : (Fin.castLE hnp j).val < p := j.isLt
  have hbj := hb (Fin.castLE hnp j) hj
  simp only [v, dif_pos hj] at hbj
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.castLE hnp j)]
  · simp [q₀, Module.Basis.toMatrix_apply, hbj]
  · intro k _ hk
    simp [q₀, hk]
  · simp

lemma measurable_act {n p : ℕ} {Q : Matrix (Fin n) (Fin p) ℝ → Matrix (Fin n) (Fin p) ℝ}
    (hQ : Measurable Q) :
    Measurable (fun x : OG n × Matrix (Fin n) (Fin p) ℝ =>
      ((x.1⁻¹ : OG n) : Matrix (Fin n) (Fin n) ℝ) * Q x.2) := by
  have hP : ∀ i k, Measurable (fun P : OG n => ((P⁻¹ : OG n) : Matrix (Fin n) (Fin n) ℝ) i k) :=
    fun i k => ((continuous_subtype_val.comp continuous_inv).matrix_elem i k).measurable
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  simp only [Matrix.mul_apply]
  refine Finset.measurable_sum _ fun k _ => ((hP i k).comp measurable_fst).mul ?_
  exact (measurable_pi_apply j).comp ((measurable_pi_apply k).comp (hQ.comp measurable_snd))

end GEPPLemma46

open GEPPLemma46 in
theorem solution (n p : ℕ) (hnp : p ≤ n)
    (Q : Matrix (Fin n) (Fin p) ℝ → Matrix (Fin n) (Fin p) ℝ)
    (R : Matrix (Fin n) (Fin p) ℝ → GEPPGrowth.Main.Mat p)
    (hQ : Measurable Q) (hR : Measurable R)
    (hQR : ∀ᵐ G ∂(GaussianMatrix.gaussianMatrix n p), GEPPGrowth.Main.ThinQR G (Q G) (R G)) :
    IndepFun Q R (GaussianMatrix.gaussianMatrix n p) := by
  let μ : Measure (Matrix (Fin n) (Fin p) ℝ) := GaussianMatrix.gaussianMatrix n p
  change ∀ᵐ G ∂μ, _ at hQR
  show IndepFun Q R μ
  have : IsProbabilityMeasure μ := GaussianMatrix.gaussianMatrix_isProbabilityMeasure n p
  -- Step 1: rotating the Gaussian input rotates `Q` and leaves `R` fixed.
  have step1 : ∀ (O : OG n) (A : Set (Matrix (Fin n) (Fin p) ℝ)) (B : Set (GEPPGrowth.Main.Mat p)),
      MeasurableSet A → MeasurableSet B →
      μ (Q ⁻¹' A ∩ R ⁻¹' B) =
        μ ({G | (O : Matrix (Fin n) (Fin n) ℝ) * Q G ∈ A} ∩ R ⁻¹' B) := by
    intro O A B hA hB
    have hT : MeasurePreserving (fun G : Matrix (Fin n) (Fin p) ℝ =>
        (O : Matrix (Fin n) (Fin n) ℝ) * G) μ μ := gauss_rot O
    have hQR' := hT.quasiMeasurePreserving.ae hQR
    have hpre : {G : Matrix (Fin n) (Fin p) ℝ | Q ((O : Matrix (Fin n) (Fin n) ℝ) * G) ∈ A ∧
        R ((O : Matrix (Fin n) (Fin n) ℝ) * G) ∈ B} =ᵐ[μ]
        ({G | (O : Matrix (Fin n) (Fin n) ℝ) * Q G ∈ A} ∩ R ⁻¹' B : Set (Matrix (Fin n) (Fin p) ℝ)) := by
      filter_upwards [hQR, hQR'] with G hG hOG
      have hG' : GEPPGrowth.Main.ThinQR ((O : Matrix (Fin n) (Fin n) ℝ) * G)
          ((O : Matrix (Fin n) (Fin n) ℝ) * Q G) (R G) := by
        refine ⟨by rw [Matrix.mul_assoc, ← hG.1], ?_, hG.2.2.1, hG.2.2.2⟩
        rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (O : Matrix (Fin n) (Fin n) ℝ)ᵀ,
          OG_tr_mul, Matrix.one_mul, hG.2.1]
      obtain ⟨e1, e2⟩ := thinQR_unique hOG hG'
      change (Q _ ∈ A ∧ R _ ∈ B) = (_ ∈ A ∧ R G ∈ B)
      rw [e1, e2]
    rw [← hT.measure_preimage (hQ hA |>.inter (hR hB)).nullMeasurableSet, ← measure_congr hpre]
    rfl
  -- Step 2: average over a Haar-distributed rotation.
  let f : Set (Matrix (Fin n) (Fin p) ℝ) → Matrix (Fin n) (Fin p) ℝ → ENNReal := fun A q =>
    haarO n {P | ((P⁻¹ : OG n) : Matrix (Fin n) (Fin n) ℝ) * q ∈ A}
  have hf : ∀ A q, qᵀ * q = 1 → f A q = f A (q₀ hnp) := by
    intro A q hq
    obtain ⟨U, rfl⟩ := exists_orth hnp q hq
    show haarO n _ = haarO n _
    rw [← measure_preimage_mul (haarO n) U]
    congr 1
    ext P
    have : ((U⁻¹ : OG n) : Matrix (Fin n) (Fin n) ℝ) * (U : Matrix (Fin n) (Fin n) ℝ) = 1 := by
      rw [← Submonoid.coe_mul, inv_mul_cancel, OneMemClass.coe_one]
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, mul_inv_rev, Submonoid.coe_mul]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc ((U⁻¹ : OG n) : Matrix (Fin n) (Fin n) ℝ), this,
      Matrix.one_mul]
  have key : ∀ (A : Set (Matrix (Fin n) (Fin p) ℝ)) (B : Set (GEPPGrowth.Main.Mat p)),
      MeasurableSet A → MeasurableSet B →
      μ (Q ⁻¹' A ∩ R ⁻¹' B) = f A (q₀ hnp) * μ (R ⁻¹' B) := by
    intro A B hA hB
    let S : Set (OG n × Matrix (Fin n) (Fin p) ℝ) :=
      {x | ((x.1⁻¹ : OG n) : Matrix (Fin n) (Fin n) ℝ) * Q x.2 ∈ A ∧ R x.2 ∈ B}
    have hS : MeasurableSet S := (measurable_act hQ hA).inter ((hR.comp measurable_snd) hB)
    have h1 := Measure.prod_apply (μ := haarO n) (ν := μ) hS
    have h2 := Measure.prod_apply_symm (μ := haarO n) (ν := μ) hS
    have e1 : ∀ P : OG n, μ (Prod.mk P ⁻¹' S) = μ (Q ⁻¹' A ∩ R ⁻¹' B) :=
      fun P => (step1 P⁻¹ A B hA hB).symm
    have e2 : (fun G => haarO n ((fun P => (P, G)) ⁻¹' S)) =ᵐ[μ]
        (R ⁻¹' B).indicator (fun _ => f A (q₀ hnp)) := by
      filter_upwards [hQR] with G hG
      by_cases hGB : R G ∈ B
      · rw [Set.indicator_of_mem (show G ∈ R ⁻¹' B from hGB), ← hf A (Q G) hG.2.1]
        congr 1
        ext P
        simp [S, hGB]
      · rw [Set.indicator_of_notMem (show G ∉ R ⁻¹' B from hGB)]
        convert measure_empty (μ := haarO n)
        ext P
        simp [S, hGB]
    simp_rw [e1, lintegral_const, measure_univ, mul_one] at h1
    rw [← h1, h2, lintegral_congr_ae e2, lintegral_indicator_const (hR hB)]
  refine (indepFun_iff_measure_inter_preimage_eq_mul (f := Q) (g := R) (μ := μ)).2 ?_
  intro A B hA hB
  have hA' := key A Set.univ hA MeasurableSet.univ
  rw [Set.preimage_univ, Set.inter_univ, measure_univ, mul_one] at hA'
  rw [key A B hA hB, hA']
