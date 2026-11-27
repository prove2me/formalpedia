-- Prove2me | solution 1 for GEPPGrowth.Main.proposition_4_15
-- status  : ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-26T22:36:32.221259+00:00
-- url     : https://prove2.me/submissions/126c2032-d2f6-42cb-b18a-023c69553901

import Definitions.Def_GEPPGrowth_Main_Process
import Theorems.Thm_GEPPGrowth_Main_lemma_4_10
import Theorems.Thm_GEPPGrowth_Main_lemma_4_8
import Theorems.Thm_GEPPGrowth_Main_lemma_4_6
import Theorems.Thm_GEPPGrowth_Main_lemma_4_13
import Theorems.Thm_MeasureTheory_lintegral_fintype_prod_eq_prod

open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators Matrix ENNReal

noncomputable section

namespace GEPP415

open GEPPGrowth.Main

/-- The standard Gaussian `p × m` matrix law, on GEPP's matrix carrier. -/
abbrev gm (p m : ℕ) : Measure (Matrix (Fin p) (Fin m) ℝ) := GaussianMatrix.gaussianMatrix p m

/-- The standard Gaussian on `Fin d → ℝ`. -/
abbrev gam (d : ℕ) : Measure (Fin d → ℝ) := Measure.pi (fun _ : Fin d => gaussianReal 0 1)

open scoped MatrixOrder in
lemma normal_eq_map (d : ℕ) (S : Mat d) : normal S = (gam d).map (fun y => CFC.sqrt S *ᵥ y) := by
  unfold normal multivariateGaussian
  rw [← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext y i
  simp

open scoped MatrixOrder in
lemma normal_one (d : ℕ) : normal (1 : Mat d) = gam d := by
  rw [normal_eq_map, CFC.sqrt_one]
  simp [Matrix.one_mulVec, Measure.map_id']

lemma measurable_det (t : ℕ) : Measurable (fun S : Mat t => S.det) := by
  change Measurable (fun S : Fin t → Fin t → ℝ => (Matrix.of S).det)
  simp only [Matrix.det_apply, Matrix.of_apply]; fun_prop

lemma measurable_gram (N t : ℕ) : Measurable (fun H : Matrix (Fin N) (Fin t) ℝ => Hᵀ * H) := by
  change Measurable (fun H : Fin N → Fin t → ℝ => fun i j => ∑ k, H k i * H k j)
  fun_prop

/-- Selecting coordinates along an injection of an i.i.d. product gives the smaller product. -/
lemma pi_map_comp_injective {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]
    {t n : ℕ} (e : Fin t → Fin n) (he : Function.Injective e) :
    (Measure.pi (fun _ : Fin n => ν)).map (fun x => x ∘ e) = Measure.pi (fun _ : Fin t => ν) := by
  classical
  have hm : Measurable (fun x : Fin n → X => x ∘ e) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply (e i)
  refine (Measure.pi_eq fun s hs => ?_).symm
  let s' : Fin n → Set X := Function.extend e s (fun _ => Set.univ)
  have hs' : ∀ r, MeasurableSet (s' r) := by
    intro r
    by_cases h : ∃ i, e i = r
    · obtain ⟨i, rfl⟩ := h
      simp only [s', he.extend_apply]; exact hs i
    · simp only [s', Function.extend_apply' _ _ _ h]; exact MeasurableSet.univ
  have hpre : (fun x : Fin n → X => x ∘ e) ⁻¹' Set.univ.pi s = Set.univ.pi s' := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Function.comp_apply]
    constructor
    · intro h r
      by_cases hr : ∃ i, e i = r
      · obtain ⟨i, rfl⟩ := hr
        simp only [s', he.extend_apply]; exact h i
      · simp [s', Function.extend_apply' _ _ _ hr]
    · intro h i
      have := h (e i)
      simpa [s', he.extend_apply] using this
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs), hpre, Measure.pi_pi]
  have h2 : ∀ i, ν (s i) = ν (s' (e i)) := fun i => by simp [s', he.extend_apply]
  simp_rw [h2]
  rw [← Finset.prod_image (s := Finset.univ) (g := e) (f := fun r => ν (s' r))
    (fun a _ b _ h => he h)]
  refine (Finset.prod_subset (Finset.subset_univ _) fun r _ hr => ?_).symm
  have : ¬ ∃ i, e i = r := by
    rintro ⟨i, rfl⟩; exact hr (Finset.mem_image_of_mem e (Finset.mem_univ i))
  simp [s', Function.extend_apply' _ _ _ this]

/-- Rows of a Gaussian matrix selected by an injection form a Gaussian matrix. -/
lemma gm_map_rows {t n m : ℕ} (e : Fin t → Fin n) (he : Function.Injective e) :
    (gm n m).map (fun G => G.submatrix e id) = gm t m :=
  pi_map_comp_injective _ e he

/-- Columns of a Gaussian matrix selected by an injection form a Gaussian matrix. -/
lemma gm_map_cols {t n m : ℕ} (e : Fin t → Fin n) (he : Function.Injective e) :
    (GaussianMatrix.gaussianMatrix m n).map (fun (G : Fin m → Fin n → ℝ) i => G i ∘ e) =
      GaussianMatrix.gaussianMatrix m t := by
  unfold GaussianMatrix.gaussianMatrix
  have h := Measure.pi_map_pi (μ := fun _ : Fin m => Measure.pi fun _ : Fin n => gaussianReal 0 1)
    (f := fun _ (c : Fin n → ℝ) => c ∘ e) (fun _ => (measurable_pi_lambda _ fun i =>
      measurable_pi_apply (e i)).aemeasurable)
  simp only [pi_map_comp_injective _ e he] at h
  exact h

/-- `HᵀH` for an `N × t` Gaussian `H` is Wishart `W_t(N, I)`. -/
lemma gm_map_gram (N t : ℕ) : (gm N t).map (fun H => Hᵀ * H) = wishart (1 : Mat t) N := by
  unfold wishart columnsLaw
  rw [normal_one]
  have hT : Measurable (fun z i j => z j i : (Fin N → Vec t) → Matrix (Fin t) (Fin N) ℝ) :=
    measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j =>
      (measurable_pi_apply i).comp (measurable_pi_apply j)
  have hG : Measurable (fun G : Matrix (Fin t) (Fin N) ℝ => G * G.transpose) := by
    change Measurable (fun G : Fin t → Fin N → ℝ => fun i j => ∑ k, G i k * G j k)
    fun_prop
  rw [Measure.map_map hG hT]
  rfl

/-! ### χ² moments -/

lemma gamma_prod (k m : ℕ) (hk : 0 < k) :
    Real.rpow 2 (m:ℝ) * Real.Gamma ((m:ℝ) + (k:ℝ)/2) / Real.Gamma ((k:ℝ)/2) =
      ∏ j ∈ Finset.range m, ((k:ℝ) + 2 * j) := by
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  have hG : 0 < Real.Gamma ((k:ℝ)/2) := Real.Gamma_pos_of_pos (by positivity)
  have e2 : ∀ q : ℕ, Real.rpow 2 (q:ℝ) = 2 ^ q := fun q => Real.rpow_natCast 2 q
  simp only [e2]
  induction m with
  | zero => simp [hG.ne']
  | succ m ih =>
    rw [Finset.prod_range_succ, ← ih]
    have h1 : ((m + 1 : ℕ) : ℝ) + (k:ℝ)/2 = ((m:ℝ) + (k:ℝ)/2) + 1 := by push_cast; ring
    rw [h1, Real.Gamma_add_one (by positivity), pow_succ]
    field_simp
    ring

/-- Natural moments of `χ²_k`: `E[x^m] = ∏_{j<m} (k + 2j)`. -/
lemma chiSquare_moment (k m : ℕ) (hk : 0 < k) :
    ∫⁻ x, ENNReal.ofReal (|x| ^ m) ∂(chiSquare k) =
      ENNReal.ofReal (∏ j ∈ Finset.range m, ((k:ℝ) + 2 * j)) := by
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  obtain ⟨hI, hE⟩ := lemma_4_8 k hk (m:ℝ) (by
    have : (0:ℝ) ≤ m := by positivity
    linarith [div_pos hk' (by norm_num : (0:ℝ) < 2)])
  have hnn : ∀ᵐ x ∂(chiSquare k), 0 ≤ x := by
    unfold chiSquare
    rw [ae_map_iff (Measurable.aemeasurable (by fun_prop)) measurableSet_Ici]
    exact Filter.Eventually.of_forall fun y => Finset.sum_nonneg fun i _ => sq_nonneg _
  have h1 : (fun x => ENNReal.ofReal (|x| ^ m)) =ᵐ[chiSquare k]
      fun x => ENNReal.ofReal (Real.rpow x m) := by
    filter_upwards [hnn] with x hx
    rw [abs_of_nonneg hx]
    exact congrArg _ (Real.rpow_natCast x m).symm
  rw [lintegral_congr_ae h1, ← ofReal_integral_eq_lintegral_ofReal hI
    (by filter_upwards [hnn] with x hx; exact Real.rpow_nonneg hx _), hE, gamma_prod k m hk]

/-- Moment `E[det(HᵀH)^m]` for an `N × t` Gaussian `H`, `t ≤ N`. -/
def gramMoment (N t m : ℕ) : ℝ :=
  ∏ i : Fin t, ∏ j ∈ Finset.range m, (((N - i.val : ℕ) : ℝ) + 2 * j)

lemma gramMoment_pos (N t m : ℕ) (htN : t ≤ N) : 0 < gramMoment N t m := by
  unfold gramMoment
  refine Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => ?_
  have : (0:ℝ) < ((N - i.val : ℕ) : ℝ) := by
    have : 0 < N - i.val := by omega
    exact_mod_cast this
  positivity

lemma moment_gram (N t m : ℕ) (ht : 0 < t) (htN : t ≤ N) :
    ∫⁻ H, ENNReal.ofReal (|(Hᵀ * H).det| ^ m) ∂(gm N t) = ENNReal.ofReal (gramMoment N t m) := by
  have hf : Measurable (fun x : ℝ => ENNReal.ofReal (|x| ^ m)) := by fun_prop
  rw [← lintegral_map (f := fun S : Mat t => ENNReal.ofReal (|S.det| ^ m))
      (hf.comp (measurable_det t)) (measurable_gram N t), gm_map_gram,
    ← lintegral_map hf (measurable_det t)]
  rw [lemma_4_10 t N ht htN, lintegral_map hf (by fun_prop)]
  have hprod : ∀ x : Fin t → ℝ, ENNReal.ofReal (|∏ i, x i| ^ m) =
      ∏ i, ENNReal.ofReal (|x i| ^ m) := by
    intro x
    rw [Finset.abs_prod, ← Finset.prod_pow, ENNReal.ofReal_prod_of_nonneg
      (fun i _ => by positivity)]
  simp_rw [hprod]
  rw [lintegral_fintype_prod_eq_prod (fun i x => ENNReal.ofReal (|x| ^ m)) (fun _ => hf)]
  unfold gramMoment
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => Finset.prod_nonneg fun j _ => by positivity)]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact chiSquare_moment (N - i.val) m (by omega)

/-- `χ²_k` has no atom at `0`. -/
lemma chiSquare_zero (k : ℕ) (hk : 0 < k) : chiSquare k {0} = 0 := by
  unfold chiSquare
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton 0)]
  have : (fun x : Fin k → ℝ => ∑ i, x i ^ 2) ⁻¹' {0} = {0} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)]
    simp [funext_iff]
  rw [this]
  haveI : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  haveI : NullSingletonClass (Measure.pi (fun _ : Fin k => gaussianReal 0 1)) :=
    Measure.pi_nullSingletonClass ⟨0, hk⟩
  exact measure_singleton 0

/-- `det(HᵀH) ≠ 0` almost surely for an `N × t` Gaussian `H`, `t ≤ N`. -/
lemma gram_det_ne_zero (N t : ℕ) (ht : 0 < t) (htN : t ≤ N) :
    ∀ᵐ H ∂(gm N t), (Hᵀ * H).det ≠ 0 := by
  rw [ae_iff]
  simp only [not_not]
  have hm : Measurable (fun H : Matrix (Fin N) (Fin t) ℝ => (Hᵀ * H).det) :=
    (measurable_det t).comp (measurable_gram N t)
  have h1 : gm N t {H | (Hᵀ * H).det = 0} =
      ((gm N t).map (fun H => (Hᵀ * H).det)) {0} := by
    rw [Measure.map_apply hm (measurableSet_singleton 0)]; rfl
  rw [h1, show (fun H : Matrix (Fin N) (Fin t) ℝ => (Hᵀ * H).det) =
      (fun S : Mat t => S.det) ∘ (fun H => Hᵀ * H) from rfl,
    ← Measure.map_map (measurable_det t) (measurable_gram N t), gm_map_gram,
    lemma_4_10 t N ht htN, Measure.map_apply (by fun_prop) (measurableSet_singleton 0)]
  refine le_antisymm ?_ (zero_le)
  have hsub : (fun x : Fin t → ℝ => ∏ i, x i) ⁻¹' {0} ⊆ ⋃ i, (fun x => x i) ⁻¹' {0} := by
    intro x hx
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Finset.prod_eq_zero_iff,
      Finset.mem_univ, true_and] at hx
    obtain ⟨i, hi⟩ := hx
    exact Set.mem_iUnion.2 ⟨i, hi⟩
  refine (measure_mono hsub).trans ((measure_iUnion_le _).trans (le_of_eq ?_))
  refine ENNReal.tsum_eq_zero.2 fun i => ?_
  rw [(measurePreserving_eval _ i).measure_preimage (measurableSet_singleton 0).nullMeasurableSet]
  exact chiSquare_zero _ (by omega)

end GEPP415

open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators Matrix ENNReal InnerProductSpace

noncomputable section

namespace GEPP415

open GEPPGrowth.Main InnerProductSpace

/-! ### A measurable thin QR factorization (Gram–Schmidt) -/

/-- Columns of a matrix as Euclidean vectors. -/
def colv {n t : ℕ} (G : Matrix (Fin n) (Fin t) ℝ) (j : Fin t) : EuclideanSpace ℝ (Fin n) :=
  toLp 2 (fun i => G i j)

/-- Gram–Schmidt orthonormalized columns. -/
def gsN {n t : ℕ} (G : Matrix (Fin n) (Fin t) ℝ) : Fin t → EuclideanSpace ℝ (Fin n) :=
  gramSchmidtNormed ℝ (colv G)

def qrQ {n t : ℕ} (G : Matrix (Fin n) (Fin t) ℝ) : Matrix (Fin n) (Fin t) ℝ :=
  fun i j => (gsN G j).ofLp i

def qrR {n t : ℕ} (G : Matrix (Fin n) (Fin t) ℝ) : Mat t :=
  fun i j => ⟪gsN G i, colv G j⟫_ℝ

lemma measurable_colv {n t : ℕ} (j : Fin t) :
    Measurable (fun G : Matrix (Fin n) (Fin t) ℝ => colv G j) := by
  unfold colv
  exact (PiLp.continuous_toLp 2 _).measurable.comp
    (measurable_pi_lambda _ fun i => (measurable_pi_apply j).comp (measurable_pi_apply i))

lemma measurable_gs {n t : ℕ} (j : Fin t) :
    Measurable (fun G : Matrix (Fin n) (Fin t) ℝ => gramSchmidt ℝ (colv G) j) := by
  induction j using WellFoundedLT.induction with
  | _ j ih =>
    have h : (fun G : Matrix (Fin n) (Fin t) ℝ => gramSchmidt ℝ (colv G) j) = fun G =>
        colv G j - ∑ i ∈ Finset.Iio j, (⟪gramSchmidt ℝ (colv G) i, colv G j⟫_ℝ /
          (‖gramSchmidt ℝ (colv G) i‖ : ℝ) ^ 2) • gramSchmidt ℝ (colv G) i := by
      funext G
      have := gramSchmidt_def'' ℝ (colv G) j
      simp only [RCLike.ofReal_real_eq_id, id] at this
      rw [eq_sub_iff_add_eq]; exact this.symm
    rw [h]
    refine (measurable_colv j).sub (Finset.measurable_sum _ fun i hi => ?_)
    have hi' := ih i (Finset.mem_Iio.1 hi)
    exact ((hi'.inner (measurable_colv j)).div (hi'.norm.pow_const 2)).smul hi'

lemma measurable_gsN {n t : ℕ} (j : Fin t) :
    Measurable (fun G : Matrix (Fin n) (Fin t) ℝ => gsN G j) := by
  unfold gsN
  simp only [gramSchmidtNormed, RCLike.ofReal_real_eq_id, id]
  exact ((measurable_gs j).norm.inv).smul (measurable_gs j)

lemma measurable_qrQ {n t : ℕ} : Measurable (qrQ : Matrix (Fin n) (Fin t) ℝ → _) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  exact (PiLp.continuous_apply 2 _ i).measurable.comp (measurable_gsN j)

lemma measurable_qrR {n t : ℕ} : Measurable (qrR : Matrix (Fin n) (Fin t) ℝ → _) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  exact (measurable_gsN i).inner (measurable_colv j)

/-- A nonsingular Gram matrix means linearly independent columns. -/
lemma linIndep_of_gram {n t : ℕ} (G : Matrix (Fin n) (Fin t) ℝ) (h : (Gᵀ * G).det ≠ 0) :
    LinearIndependent ℝ (colv G) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hv : G *ᵥ g = 0 := by
    funext i
    have := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v.ofLp i) hg
    simpa [colv, Matrix.mulVec, dotProduct, mul_comm] using this
  have : (Gᵀ * G) *ᵥ g = 0 := by rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  have h0 := Matrix.eq_zero_of_mulVec_eq_zero h this
  intro i; rw [h0]; rfl

/-- Gram–Schmidt gives a thin QR factorization of a full-rank matrix. -/
lemma thinQR_of_gram {n t : ℕ} (G : Matrix (Fin n) (Fin t) ℝ) (h : (Gᵀ * G).det ≠ 0) :
    ThinQR G (qrQ G) (qrR G) := by
  have hli := linIndep_of_gram G h
  have hon : Orthonormal ℝ (gsN G) := gramSchmidtNormed_orthonormal hli
  have hne : ∀ j, gramSchmidt ℝ (colv G) j ≠ 0 := fun j => gramSchmidt_ne_zero j hli
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- G = Q R: each column is its expansion in the orthonormal family
    have hspan : ∀ j, colv G j = ∑ l, ⟪gsN G l, colv G j⟫_ℝ • gsN G l := by
      intro j
      have hmem : colv G j ∈ Submodule.span ℝ (Set.range (gsN G)) := by
        rw [gsN, span_gramSchmidtNormed_range, span_gramSchmidt]
        exact Submodule.subset_span ⟨j, rfl⟩
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hmem
      rw [← hc]
      refine Finset.sum_congr rfl fun l _ => ?_
      congr 1
      rw [inner_sum, Finset.sum_eq_single l]
      · rw [inner_smul_right, real_inner_self_eq_norm_sq, hon.1 l]; ring
      · intro b _ hb
        rw [inner_smul_right, hon.2 hb.symm, mul_zero]
      · simp
    ext i j
    have := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v.ofLp i) (hspan j)
    simp only [colv, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at this
    rw [Matrix.mul_apply]
    simp only [qrQ, qrR, colv]
    rw [this]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  · ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    have h1 : ∑ k, (qrQ G)ᵀ i k * qrQ G k j = ⟪gsN G i, gsN G j⟫_ℝ := by
      simp only [Matrix.transpose_apply, qrQ, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    rw [h1]
    by_cases hij : i = j
    · subst hij; rw [if_pos rfl, real_inner_self_eq_norm_sq, hon.1 i]; norm_num
    · rw [if_neg hij, hon.2 hij]
  · intro i j hji
    simp only [qrR, gsN, gramSchmidtNormed, inner_smul_left]
    rw [gramSchmidt_inv_triangular ℝ (colv G) hji, mul_zero]
  · intro j
    simp only [qrR, gsN, gramSchmidtNormed, inner_smul_left]
    have hd : ⟪gramSchmidt ℝ (colv G) j, colv G j⟫_ℝ = ‖gramSchmidt ℝ (colv G) j‖ ^ 2 := by
      conv_lhs => rw [gramSchmidt_def'' ℝ (colv G) j]
      rw [inner_add_right, inner_sum, real_inner_self_eq_norm_sq]
      rw [Finset.sum_eq_zero, add_zero]
      intro i hi
      rw [inner_smul_right, gramSchmidt_orthogonal ℝ (colv G) (ne_of_gt (Finset.mem_Iio.1 hi)),
        mul_zero]
    rw [hd]
    have hpos : 0 < ‖gramSchmidt ℝ (colv G) j‖ := norm_pos_iff.2 (hne j)
    simp only [conj_trivial, RCLike.ofReal_real_eq_id, id]
    field_simp
    exact hpos

lemma measurable_rows {n t m : ℕ} (e : Fin t → Fin n) :
    Measurable (fun G : Matrix (Fin n) (Fin m) ℝ => G.submatrix e id) :=
  measurable_pi_lambda _ fun i => measurable_pi_apply (e i)

/-- `E[|det G_J|^{2m}]` over the rows `J = range e` of an `n × t` Gaussian `G`. -/
lemma moment_rows (n t m : ℕ) (ht : 0 < t) (e : Fin t → Fin n) (he : Function.Injective e) :
    ∫⁻ G, ENNReal.ofReal (|(G.submatrix e id).det| ^ (2 * m)) ∂(gm n t) =
      ENNReal.ofReal (gramMoment t t m) := by
  have hf : Measurable (fun H : Mat t => ENNReal.ofReal (|H.det| ^ (2 * m))) :=
    (by fun_prop : Measurable fun x : ℝ => ENNReal.ofReal (|x| ^ (2 * m))).comp (measurable_det t)
  rw [← lintegral_map hf (measurable_rows e), gm_map_rows e he, ← moment_gram t t m ht le_rfl]
  refine lintegral_congr fun H => ?_
  rw [Matrix.det_mul, Matrix.det_transpose, abs_mul, ← sq, ← pow_mul]

/-- `det(G_J) = 0` is null. -/
lemma rows_det_ne_zero (n t : ℕ) (ht : 0 < t) (e : Fin t → Fin n) (he : Function.Injective e) :
    ∀ᵐ G ∂(gm n t), (G.submatrix e id).det ≠ 0 := by
  have h := gram_det_ne_zero t t ht le_rfl
  rw [← gm_map_rows (m := t) e he] at h
  have h2 := ae_of_ae_map (measurable_rows e).aemeasurable h
  filter_upwards [h2] with G hG
  intro h0
  apply hG
  rw [Matrix.det_mul, Matrix.det_transpose, h0, mul_zero]

lemma upper_det_pos {t : ℕ} (R : Mat t) (hU : ∀ i j, j < i → R i j = 0) (hD : ∀ i, 0 < R i i) :
    0 < R.det := by
  have hb : R.BlockTriangular id := fun i j h => hU i j h
  rw [Matrix.det_of_upperTriangular hb]
  exact Finset.prod_pos fun i _ => hD i

/-- Fixed-row-set bound: `P(det GᵀG ≤ τ det(G_J)²) ≤ τ^m E[det(G_J)^{2m}]/E[det(GᵀG)^m]`. -/
lemma fixedJ_bound (n t m : ℕ) (ht : 0 < t) (htn : t ≤ n) (e : Fin t → Fin n)
    (he : Function.Injective e) (τ : ℝ) (hτ : 0 ≤ τ) :
    gm n t {G | (Gᵀ * G).det ≤ τ * (G.submatrix e id).det ^ 2} ≤
      ENNReal.ofReal (τ ^ m * (gramMoment t t m / gramMoment n t m)) := by
  set Q := (qrQ : Matrix (Fin n) (Fin t) ℝ → _) with hQdef
  set R := (qrR : Matrix (Fin n) (Fin t) ℝ → _) with hRdef
  have hQR : ∀ᵐ G ∂(gm n t), ThinQR G (Q G) (R G) := by
    filter_upwards [gram_det_ne_zero n t ht htn] with G hG using thinQR_of_gram G hG
  have hind : IndepFun Q R (gm n t) := lemma_4_6 n t htn Q R measurable_qrQ measurable_qrR hQR
  have hfac : ∀ G, ThinQR G (Q G) (R G) →
      (G.submatrix e id).det = ((Q G).submatrix e id).det * (R G).det ∧
      (Gᵀ * G).det = (R G).det ^ 2 ∧ 0 < (R G).det := by
    intro G ⟨hG, hQ, hU, hD⟩
    refine ⟨?_, ?_, upper_det_pos _ hU hD⟩
    · have : G.submatrix e id = (Q G).submatrix e id * R G := by
        conv_lhs => rw [hG]
        ext i j; simp [Matrix.mul_apply]
      rw [this, Matrix.det_mul]
    · conv_lhs => rw [hG]
      rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (Q G)ᵀ, hQ, Matrix.one_mul,
        Matrix.det_mul, Matrix.det_transpose, sq]
  -- the two independent factors
  let φ : Matrix (Fin n) (Fin t) ℝ → ℝ≥0∞ := fun q => ENNReal.ofReal (|(q.submatrix e id).det| ^ (2 * m))
  let ψ : Mat t → ℝ≥0∞ := fun r => ENNReal.ofReal (|r.det| ^ (2 * m))
  have hφ : Measurable φ :=
    (by fun_prop : Measurable fun x : ℝ => ENNReal.ofReal (|x| ^ (2 * m))).comp
      ((measurable_det t).comp (measurable_rows e))
  have hψ : Measurable ψ :=
    (by fun_prop : Measurable fun x : ℝ => ENNReal.ofReal (|x| ^ (2 * m))).comp (measurable_det t)
  have hprod := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
    (hφ.comp measurable_qrQ).aemeasurable (hψ.comp measurable_qrR).aemeasurable
    (hind.comp hφ hψ)
  have hL : ∫⁻ G, (φ ∘ Q) G * (ψ ∘ R) G ∂(gm n t) = ENNReal.ofReal (gramMoment t t m) := by
    rw [← moment_rows n t m ht e he]
    refine lintegral_congr_ae ?_
    filter_upwards [hQR] with G hG
    simp only [Function.comp_apply, φ, ψ]
    rw [(hfac G hG).1, abs_mul, mul_pow, ENNReal.ofReal_mul (by positivity)]
  have hRm : ∫⁻ G, (ψ ∘ R) G ∂(gm n t) = ENNReal.ofReal (gramMoment n t m) := by
    rw [← moment_gram n t m ht htn]
    refine lintegral_congr_ae ?_
    filter_upwards [hQR] with G hG
    simp only [Function.comp_apply, ψ]
    rw [(hfac G hG).2.1, abs_pow, ← pow_mul, mul_comm]
  have hMn := gramMoment_pos n t m htn
  have hMt := gramMoment_pos t t m le_rfl
  have hQm : ∫⁻ G, (φ ∘ Q) G ∂(gm n t) =
      ENNReal.ofReal (gramMoment t t m / gramMoment n t m) := by
    rw [hL, hRm] at hprod
    rw [ENNReal.ofReal_div_of_pos hMn, ENNReal.eq_div_iff (by simpa using hMn) ENNReal.ofReal_ne_top,
      hprod, mul_comm]
  -- Markov
  let f : Matrix (Fin n) (Fin t) ℝ → ℝ≥0∞ := fun G => ENNReal.ofReal (τ ^ m) * (φ ∘ Q) G
  have hmark := mul_meas_ge_le_lintegral₀ (μ := gm n t) (f := f)
    ((hφ.comp measurable_qrQ).const_mul _).aemeasurable 1
  rw [one_mul, lintegral_const_mul _ (hφ.comp measurable_qrQ), hQm,
    ← ENNReal.ofReal_mul (by positivity)] at hmark
  refine le_trans (measure_mono_ae ?_) hmark
  filter_upwards [hQR] with G hG hEv
  obtain ⟨h1, h2, h3⟩ := hfac G hG
  change (Gᵀ * G).det ≤ τ * (G.submatrix e id).det ^ 2 at hEv
  change 1 ≤ f G
  rw [h1, h2] at hEv
  have hb2 : 0 < (R G).det ^ 2 := by positivity
  have hone : 1 ≤ τ * ((Q G).submatrix e id).det ^ 2 := by
    by_contra hlt
    push_neg at hlt
    have : τ * (((Q G).submatrix e id).det * (R G).det) ^ 2 < (R G).det ^ 2 := by
      rw [mul_pow, ← mul_assoc]; nlinarith
    linarith
  simp only [f, φ, Function.comp_apply]
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.one_le_ofReal.2
  rw [pow_mul, ← mul_pow, sq_abs]
  calc (1:ℝ) = 1 ^ m := (one_pow m).symm
    _ ≤ _ := pow_le_pow_left₀ zero_le_one hone m

end GEPP415

open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators Matrix ENNReal

noncomputable section

namespace GEPP415

open GEPPGrowth.Main

lemma labels_injective {n : ℕ} (A : Mat n) (t : ℕ) : Function.Injective (run A t).labels := by
  induction t with
  | zero => exact Function.injective_id
  | succ t ih =>
    simp only [run]
    split_ifs with h
    · exact ih.comp (Equiv.swap _ _).injective
    · exact ih

/-- `det(F.submatrix L id)² = det(F_J)²` for the sorted enumeration of `J = range L`. -/
lemma det_sq_reindex {n t : ℕ} (F : Matrix (Fin n) (Fin t) ℝ) (L : Fin t → Fin n)
    (hL : Function.Injective L) :
    ∃ J ∈ Finset.powersetCard t (Finset.univ : Finset (Fin n)), ∃ hJ : J.card = t,
      (F.submatrix L id).det ^ 2 = (F.submatrix (J.orderEmbOfFin hJ) id).det ^ 2 := by
  classical
  set J := Finset.univ.image L
  have hJ : J.card = t := by
    rw [Finset.card_image_of_injective _ hL, Finset.card_univ, Fintype.card_fin]
  refine ⟨J, Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hJ⟩, hJ, ?_⟩
  have hmem : ∀ i, L i ∈ J := fun i => Finset.mem_image_of_mem L (Finset.mem_univ i)
  let σf : Fin t → Fin t := fun i => (J.orderIsoOfFin hJ).symm ⟨L i, hmem i⟩
  have hσ : ∀ i, J.orderEmbOfFin hJ (σf i) = L i := by
    intro i
    rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]
  have hσinj : Function.Injective σf := by
    intro a b hab
    apply hL
    rw [← hσ a, ← hσ b, hab]
  let σ : Equiv.Perm (Fin t) := Equiv.ofBijective σf (Finite.injective_iff_bijective.1 hσinj)
  have hsub : F.submatrix L id = (F.submatrix (J.orderEmbOfFin hJ) id).submatrix σ id := by
    ext i j
    simp [σ, hσ]
  rw [hsub, Matrix.det_permute, mul_pow]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

lemma gm_map_firstColumns {n t : ℕ} (ht : t ≤ n) :
    (gm n n).map (firstColumns ht) = gm n t :=
  gm_map_cols (Fin.castLE ht) (Fin.castLE_injective ht)

lemma measurable_firstColumns {n t : ℕ} (ht : t ≤ n) : Measurable (firstColumns ht) :=
  measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j =>
    (measurable_pi_apply _).comp (measurable_pi_apply i)

/-- The determinant tail of the actual GEPP covariance block, under a Gaussian input. -/
lemma tail_gm (n k m : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) (τ : ℝ) (hτ : 0 ≤ τ) :
    gm n n {A | (block (actualCov A (k-1)) (n-(k-1))).det ≤ τ} ≤
      (n.choose (k-1) : ℝ≥0∞) *
        ENNReal.ofReal (τ ^ m * (gramMoment (k-1) (k-1) m / gramMoment n (k-1) m)) := by
  classical
  have ht : k - 1 ≤ n := by omega
  set t := k - 1 with htdef
  have ht0 : 0 < t := by omega
  obtain ⟨-, hae⟩ := lemma_4_13 n k hk hkn
  set F := firstColumns ht with hFdef
  -- the per-subset events
  let S : Finset (Fin n) → Set (Matrix (Fin n) (Fin t) ℝ) := fun J =>
    if hJ : J.card = t then
      {G | (Gᵀ * G).det ≤ τ * (G.submatrix (J.orderEmbOfFin hJ) id).det ^ 2} ∪
        {G | (G.submatrix (J.orderEmbOfFin hJ) id).det = 0}
    else ∅
  have hcover : {A : Mat n | (block (actualCov A t) (n-t)).det ≤ τ} ≤ᵐ[gm n n]
      ⋃ J ∈ Finset.powersetCard t (Finset.univ : Finset (Fin n)), F ⁻¹' S J := by
    filter_upwards [hae] with A hA hEv
    change (block (actualCov A t) (n-t)).det ≤ τ at hEv
    rw [hA] at hEv
    have hPM : pivotMinor ht A = (F A).submatrix ((run A t).labels ∘ Fin.castLE ht) id :=
      rfl
    obtain ⟨J, hJmem, hJ, hdet⟩ := det_sq_reindex (F A) _
      ((labels_injective A t).comp (Fin.castLE_injective ht))
    rw [← hPM] at hdet
    change A ∈ ⋃ J ∈ Finset.powersetCard t (Finset.univ : Finset (Fin n)), F ⁻¹' S J
    refine Set.mem_biUnion hJmem ?_
    simp only [Set.mem_preimage, S, dif_pos hJ, Set.mem_union, Set.mem_setOf_eq]
    by_cases h0 : (pivotMinor ht A).det = 0
    · right
      have : ((F A).submatrix (J.orderEmbOfFin hJ) id).det ^ 2 = 0 := by rw [← hdet, h0]; ring
      exact pow_eq_zero_iff (two_ne_zero) |>.1 this
    · left
      rw [← hdet]
      have hp : 0 < (pivotMinor ht A).det ^ 2 := by positivity
      rw [div_le_iff₀ hp] at hEv; linarith
  refine (measure_mono_ae hcover).trans ((measure_biUnion_finset_le _ _).trans ?_)
  have hbound : ∀ J ∈ Finset.powersetCard t (Finset.univ : Finset (Fin n)),
      gm n n (F ⁻¹' S J) ≤
        ENNReal.ofReal (τ ^ m * (gramMoment t t m / gramMoment n t m)) := by
    intro J hJmem
    have hJ : J.card = t := (Finset.mem_powersetCard.1 hJmem).2
    refine (Measure.le_map_apply (measurable_firstColumns ht).aemeasurable _).trans ?_
    rw [gm_map_firstColumns ht]
    simp only [S, dif_pos hJ]
    refine (measure_union_le _ _).trans ?_
    have e1 := fixedJ_bound n t m ht0 ht (J.orderEmbOfFin hJ) (J.orderEmbOfFin hJ).injective τ hτ
    have e2 : gm n t {G | (G.submatrix (J.orderEmbOfFin hJ) id).det = 0} = 0 := by
      have := rows_det_ne_zero n t ht0 (J.orderEmbOfFin hJ) (J.orderEmbOfFin hJ).injective
      rw [ae_iff] at this
      simpa using this
    rw [e2, add_zero]
    exact e1
  refine (Finset.sum_le_sum hbound).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end GEPP415

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix ENNReal

noncomputable section

namespace GEPP415

open GEPPGrowth.Main

/-- `∏_{i<t} (t-i+a) / ∏_{i<t} (t+d-i+a) ≤ ((d+a)/(t+d+a))^d`. -/
lemma ratio_le (t d : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    (∏ i ∈ Finset.range t, (((t - i : ℕ) : ℝ) + a)) /
      (∏ i ∈ Finset.range t, (((t + d - i : ℕ) : ℝ) + a)) ≤
      (((d:ℝ) + a) / ((t:ℝ) + d + a)) ^ d := by
  set g : ℕ → ℝ := fun x => (x:ℝ) + 1 + a with hg
  have hgpos : ∀ x, 0 < g x := fun x => by simp only [hg]; positivity
  have hA : ∏ i ∈ Finset.range t, (((t - i : ℕ) : ℝ) + a) = ∏ i ∈ Finset.range t, g i := by
    rw [← Finset.prod_range_reflect g t]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hi := Finset.mem_range.1 hi
    simp only [hg]
    rw [show t - i = (t - 1 - i) + 1 by omega]
    push_cast; ring
  have hB : ∏ i ∈ Finset.range t, (((t + d - i : ℕ) : ℝ) + a) =
      ∏ i ∈ Finset.range t, g (d + i) := by
    rw [← Finset.prod_range_reflect (fun i => g (d + i)) t]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hi := Finset.mem_range.1 hi
    simp only [hg]
    rw [show t + d - i = d + (t - 1 - i) + 1 by omega]
    push_cast; ring
  have hid : (∏ i ∈ Finset.range t, g i) * ∏ i ∈ Finset.range d, g (t + i) =
      (∏ i ∈ Finset.range d, g i) * ∏ i ∈ Finset.range t, g (d + i) := by
    rw [← Finset.prod_range_add, ← Finset.prod_range_add, add_comm]
  have hBpos : 0 < ∏ i ∈ Finset.range t, g (d + i) := Finset.prod_pos fun i _ => hgpos _
  have hDpos : 0 < ∏ i ∈ Finset.range d, g (t + i) := Finset.prod_pos fun i _ => hgpos _
  rw [hA, hB, div_le_iff₀ hBpos]
  have hC : ∏ i ∈ Finset.range d, g i ≤
      (((d:ℝ) + a) / ((t:ℝ) + d + a)) ^ d * ∏ i ∈ Finset.range d, g (t + i) := by
    rw [show (((d:ℝ) + a) / ((t:ℝ) + d + a)) ^ d =
        ∏ i ∈ Finset.range d, (((d:ℝ) + a) / ((t:ℝ) + d + a)) by
          rw [Finset.prod_const, Finset.card_range],
      ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun i _ => (hgpos i).le) fun i hi => ?_
    have hi := Finset.mem_range.1 hi
    have hi' : (i:ℝ) + 1 ≤ d := by exact_mod_cast hi
    have ht : (0:ℝ) ≤ t := by positivity
    simp only [hg]
    rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
    push_cast
    nlinarith
  have := mul_le_mul_of_nonneg_right hC hBpos.le
  rw [← hid, mul_assoc, mul_comm (∏ i ∈ Finset.range d, g (t + i)), ← mul_assoc] at this
  exact le_of_mul_le_mul_right this hDpos

lemma gramMoment_range (N t m : ℕ) : gramMoment N t m =
    ∏ j ∈ Finset.range m, ∏ i ∈ Finset.range t, (((N - i : ℕ) : ℝ) + 2 * j) := by
  unfold gramMoment
  rw [Fin.prod_univ_eq_prod_range (fun i => ∏ j ∈ Finset.range m, (((N - i : ℕ) : ℝ) + 2 * j)) t,
    Finset.prod_comm]

lemma gramMoment_ratio (t d m n : ℕ) (hn : n = t + d) (hn0 : 0 < n) :
    gramMoment t t m / gramMoment n t m ≤ (((d:ℝ) + 2 * ((m:ℝ) - 1)) / n) ^ (d * m) := by
  subst hn
  rw [gramMoment_range, gramMoment_range, ← Finset.prod_div_distrib]
  have hn' : (0:ℝ) < ((t + d : ℕ) : ℝ) := by exact_mod_cast hn0
  calc ∏ j ∈ Finset.range m, (∏ i ∈ Finset.range t, (((t - i : ℕ) : ℝ) + 2 * j)) /
        ∏ i ∈ Finset.range t, (((t + d - i : ℕ) : ℝ) + 2 * j)
      ≤ ∏ j ∈ Finset.range m, (((d:ℝ) + 2 * j) / ((t:ℝ) + d + 2 * j)) ^ d := by
        refine Finset.prod_le_prod (fun j _ => ?_) fun j _ => ratio_le t d (2 * j) (by positivity)
        refine div_nonneg (Finset.prod_nonneg fun i _ => by positivity)
          (Finset.prod_nonneg fun i _ => by positivity)
    _ ≤ ∏ j ∈ Finset.range m, (((d:ℝ) + 2 * ((m:ℝ) - 1)) / ((t + d : ℕ) : ℝ)) ^ d := by
        refine Finset.prod_le_prod (fun j _ => by positivity) fun j hj => ?_
        have hj := Finset.mem_range.1 hj
        have hj' : (j:ℝ) ≤ (m:ℝ) - 1 := by
          have : (j:ℝ) + 1 ≤ m := by exact_mod_cast hj
          linarith
        refine pow_le_pow_left₀ (by positivity) ?_ d
        push_cast at hn' ⊢
        rw [div_le_div_iff₀ (by positivity) hn']
        have h0 : (0:ℝ) ≤ j := by positivity
        have h1 : (0:ℝ) ≤ t := by positivity
        have h2 : (0:ℝ) ≤ d := by positivity
        nlinarith
    _ = _ := by rw [Finset.prod_const, Finset.card_range, ← pow_mul]

lemma one_le_ceil_log (n : ℕ) (hn : 2 ≤ n) : 1 ≤ ⌈Real.log n⌉₊ := by
  have : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  exact Nat.one_le_iff_ne_zero.2 (Nat.pos_iff_ne_zero.1 (Nat.ceil_pos.2 this))

lemma rpow_pow_eq (n d m : ℕ) (hm : 1 ≤ m) :
    (Real.rpow (n:ℝ) ((d:ℝ) * (1 - 1 / (m:ℝ)))) ^ m = (n:ℝ) ^ (d * (m - 1)) := by
  have hm' : (m:ℝ) ≠ 0 := by positivity
  change ((n:ℝ) ^ ((d:ℝ) * (1 - 1 / (m:ℝ)))) ^ m = _
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_natCast]
  congr 1
  rw [Nat.cast_mul, Nat.cast_sub hm]
  field_simp
  push_cast
  ring

/-- Arithmetic of the first claim. -/
lemma arith1 (n t d : ℕ) (hn : n = t + d) (hn2 : 2 ≤ n) (τ : ℝ) (hτ : 0 < τ) :
    (n.choose t : ℝ) * (τ ^ ⌈Real.log n⌉₊ *
        (gramMoment t t ⌈Real.log n⌉₊ / gramMoment n t ⌈Real.log n⌉₊)) ≤
      (τ * ((d:ℝ) + 2 * Real.log n) ^ d /
        Real.rpow (n:ℝ) ((d:ℝ) * (1 - 1 / (⌈Real.log n⌉₊:ℝ)))) ^ ⌈Real.log n⌉₊ := by
  set m := ⌈Real.log n⌉₊ with hmdef
  have hm := one_le_ceil_log n hn2
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hm1 : (m:ℝ) - 1 ≤ Real.log n := by
    have := Nat.ceil_lt_add_one hlog; rw [← hmdef] at this; linarith
  have hnpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hchoose : (n.choose t : ℝ) ≤ (n:ℝ) ^ d := by
    have : n.choose t = n.choose d := by rw [hn, Nat.choose_symm_add]
    rw [this]; exact_mod_cast Nat.choose_le_pow n d
  have hρ := gramMoment_ratio t d m n hn (by omega)
  have hρ0 : 0 ≤ gramMoment t t m / gramMoment n t m :=
    div_nonneg (gramMoment_pos t t m le_rfl).le (gramMoment_pos n t m (by omega)).le
  set y : ℝ := (d:ℝ) + 2 * ((m:ℝ) - 1)
  have hy : 0 ≤ y := by
    have : (1:ℝ) ≤ m := by exact_mod_cast hm
    positivity
  have hX : y ≤ (d:ℝ) + 2 * Real.log n := by linarith
  rw [div_pow, rpow_pow_eq n d m hm, mul_pow, ← pow_mul]
  have hsplit : (n:ℝ) ^ (d * m) = (n:ℝ) ^ d * (n:ℝ) ^ (d * (m - 1)) := by
    rw [← pow_add]; congr 1
    rw [Nat.mul_sub, mul_one]
    have : d ≤ d * m := Nat.le_mul_of_pos_right d (by omega)
    omega
  calc (n.choose t : ℝ) * (τ ^ m * (gramMoment t t m / gramMoment n t m))
      ≤ (n:ℝ) ^ d * (τ ^ m * (y / n) ^ (d * m)) := by
        refine mul_le_mul hchoose (mul_le_mul_of_nonneg_left hρ (by positivity))
          (by positivity) (by positivity)
    _ = τ ^ m * y ^ (d * m) / (n:ℝ) ^ (d * (m - 1)) := by
        rw [div_pow, hsplit]
        field_simp
    _ ≤ τ ^ m * ((d:ℝ) + 2 * Real.log n) ^ (d * m) / (n:ℝ) ^ (d * (m - 1)) := by
        gcongr

/-- Arithmetic of the second claim. -/
lemma arith2 (n d : ℕ) (hd : 1 ≤ d) (hn2 : 2 ≤ n) :
    ((1 / Real.exp 1) * ((n:ℝ) / (Real.exp 1 * ((d:ℝ) + 2 * Real.log n))) ^ d *
        ((d:ℝ) + 2 * Real.log n) ^ d /
        Real.rpow (n:ℝ) ((d:ℝ) * (1 - 1 / (⌈Real.log n⌉₊:ℝ)))) ^ ⌈Real.log n⌉₊ ≤ 1 / (n:ℝ) := by
  set m := ⌈Real.log n⌉₊ with hmdef
  have hm := one_le_ceil_log n hn2
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn2)
  have hlogm : Real.log n ≤ m := Nat.le_ceil _
  have hnpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hmpos : (0:ℝ) < m := by exact_mod_cast hm
  set X : ℝ := (d:ℝ) + 2 * Real.log n
  have hXpos : 0 < X := by have : (1:ℝ) ≤ d := by exact_mod_cast hd
                           positivity
  -- the base equals `e^{-1-d} n^{d/m}`
  have hbase : (1 / Real.exp 1) * ((n:ℝ) / (Real.exp 1 * X)) ^ d * X ^ d /
      Real.rpow (n:ℝ) ((d:ℝ) * (1 - 1 / (m:ℝ))) =
      (1 / Real.exp 1) * (Real.rpow (n:ℝ) ((d:ℝ) / m) / Real.exp 1 ^ d) := by
    change _ / (n:ℝ) ^ ((d:ℝ) * (1 - 1 / (m:ℝ))) = _ * ((n:ℝ) ^ ((d:ℝ) / m) / _)
    have h1 : (n:ℝ) ^ ((d:ℝ) / m) = (n:ℝ) ^ d / (n:ℝ) ^ ((d:ℝ) * (1 - 1 / (m:ℝ))) := by
      rw [← Real.rpow_natCast, ← Real.rpow_sub hnpos]
      congr 1; ring
    rw [h1, div_pow, mul_pow]
    field_simp
  rw [hbase]
  have hpow : Real.rpow (n:ℝ) ((d:ℝ) / m) ≤ Real.exp 1 ^ d := by
    change (n:ℝ) ^ ((d:ℝ) / m) ≤ _
    rw [Real.rpow_def_of_pos hnpos, ← Real.exp_nat_mul, mul_one]
    apply Real.exp_le_exp.2
    rw [mul_div_assoc']
    rw [div_le_iff₀ hmpos]
    have : (0:ℝ) ≤ d := by positivity
    nlinarith
  have hb1 : (1 / Real.exp 1) * (Real.rpow (n:ℝ) ((d:ℝ) / m) / Real.exp 1 ^ d) ≤ 1 / Real.exp 1 := by
    have : Real.rpow (n:ℝ) ((d:ℝ) / m) / Real.exp 1 ^ d ≤ 1 :=
      (div_le_one (by positivity)).2 hpow
    have he : 0 < 1 / Real.exp 1 := by positivity
    nlinarith
  have hb0 : 0 ≤ (1 / Real.exp 1) * (Real.rpow (n:ℝ) ((d:ℝ) / m) / Real.exp 1 ^ d) := by
    have : 0 ≤ Real.rpow (n:ℝ) ((d:ℝ) / m) := Real.rpow_nonneg hnpos.le _
    positivity
  refine (pow_le_pow_left₀ hb0 hb1 m).trans ?_
  rw [one_div, ← Real.exp_neg, ← Real.exp_nat_mul, one_div, ← Real.exp_log hnpos, ← Real.exp_neg]
  apply Real.exp_le_exp.2
  linarith

end GEPP415

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix ENNReal

noncomputable section

namespace GEPP415

open GEPPGrowth.Main

/-! ### Measurability of the GEPP run and of the covariance update -/

/-- Evaluating a measurable family at a measurable finite index. -/
lemma measurable_at_index {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {k : ℕ}
    (F : X → Fin k → Y) (hF : ∀ i, Measurable fun x => F x i) (p : X → Fin k)
    (hp : Measurable p) : Measurable (fun x => F x (p x)) := by
  intro s hs
  have : (fun x => F x (p x)) ⁻¹' s = ⋃ i, (p ⁻¹' {i}) ∩ ((fun x => F x i) ⁻¹' s) := by
    ext x; simp
  rw [this]
  exact MeasurableSet.iUnion fun i => (hp (measurableSet_singleton i)).inter (hF i hs)

lemma measurable_foldl {X : Type*} [MeasurableSpace X] {k : ℕ} (f : X → Fin k → Fin k → Fin k)
    (hf : ∀ b j, Measurable fun x => f x b j) (l : List (Fin k)) :
    ∀ (b0 : X → Fin k), Measurable b0 → Measurable (fun x => l.foldl (f x) (b0 x)) := by
  induction l with
  | nil => intro b0 hb; simpa using hb
  | cons j l ih =>
    intro b0 hb
    simp only [List.foldl_cons]
    exact ih _ (measurable_at_index (fun x b => f x b j) (fun b => hf b j) b0 hb)

lemma measurable_rowPivot {n : ℕ} (k : Fin n) : Measurable (fun M : Mat n => rowPivot M k) := by
  unfold rowPivot
  refine measurable_foldl _ (fun b j => ?_) _ _ measurable_const
  refine Measurable.ite ?_ measurable_const measurable_const
  have h1 : Measurable fun M : Mat n => |M b k| := by fun_prop
  have h2 : Measurable fun M : Mat n => |M j k| := by fun_prop
  by_cases hkj : k ≤ j <;> by_cases hjb : j < b <;>
    simp only [hkj, hjb, true_and, false_and, and_true, and_false, or_false, Set.setOf_false,
      MeasurableSet.empty]
  · exact (measurableSet_lt h1 h2).union (measurableSet_eq_fun h1 h2)
  · exact measurableSet_lt h1 h2

lemma measurable_pivot (d : ℕ) : Measurable (fun y : Vec (d+1) => pivot y) := by
  unfold pivot
  refine measurable_foldl _ (fun b j => ?_) _ _ measurable_const
  refine Measurable.ite ?_ measurable_const measurable_const
  have h1 : Measurable fun y : Vec (d+1) => |y b| := by fun_prop
  have h2 : Measurable fun y : Vec (d+1) => |y j| := by fun_prop
  by_cases hjb : j < b <;> simp only [hjb, and_true, and_false, or_false]
  · exact (measurableSet_lt h1 h2).union (measurableSet_eq_fun h1 h2)
  · exact measurableSet_lt h1 h2

/-- The matrix part of an elimination step. -/
lemma measurable_stepAt {n : ℕ} {X : Type*} [MeasurableSpace X] (M : X → Mat n)
    (hM : Measurable M) (L : Fin n → Fin n) (k i : Fin n) :
    Measurable (fun x => (stepAt ⟨M x, L⟩ k i).matrix) := by
  have hM' : ∀ a b, Measurable fun x => M x a b := fun a b =>
    (measurable_pi_apply b).comp ((measurable_pi_apply a).comp hM)
  refine measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun b => ?_
  simp only [stepAt, Matrix.submatrix_apply, id]
  split_ifs
  all_goals first
    | exact (hM' _ _).sub (((hM' _ _).div (hM' _ _)).mul (hM' _ _))
    | exact (hM' _ _).sub (((hM' _ _).div (hM' _ _)).mul measurable_const)
    | exact (hM' _ _).sub (measurable_const.mul (hM' _ _))
    | exact (hM' _ _).sub (measurable_const.mul measurable_const)

lemma measurable_run {n : ℕ} (t : ℕ) : Measurable (fun A : Mat n => (run A t).matrix) := by
  induction t with
  | zero => exact measurable_id
  | succ t ih =>
    simp only [run]
    by_cases h : t < n
    · simp only [dif_pos h]
      have := measurable_at_index
        (fun A i => (stepAt ⟨(run A t).matrix, (run A t).labels⟩ ⟨t, h⟩ i).matrix) ?_
        (fun A => rowPivot (run A t).matrix ⟨t, h⟩) ((measurable_rowPivot _).comp ih)
      · exact this
      · intro i
        -- the matrix part does not depend on the labels
        have e : ∀ A : Mat n, (stepAt ⟨(run A t).matrix, (run A t).labels⟩ ⟨t, h⟩ i).matrix =
            (stepAt ⟨(run A t).matrix, id⟩ ⟨t, h⟩ i).matrix := fun A => rfl
        simp_rw [e]
        exact measurable_stepAt _ ih id _ _
    · simp only [dif_neg h]; exact ih

lemma measurable_residual {n : ℕ} (t : ℕ) :
    Measurable (fun A : Mat n => GEPPGrowth.Main.residual A t) := by
  have := measurable_run (n := n) t
  change Measurable (fun A : Mat n => fun (i : Fin (n-t)) (j : Fin (n-t)) =>
    (run A t).matrix ⟨i.val+t, by omega⟩ ⟨j.val+t, by omega⟩)
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp this)

lemma measurable_compressionAt {d : ℕ} (i : Fin (d+1)) (a : Fin d) (c : Fin (d+1)) :
    Measurable (fun y : Vec (d+1) => compressionAt y i a c) := by
  have : (fun y : Vec (d+1) => compressionAt y i a c) = fun y =>
      ∑ l, deletion i a l * ((1 : Mat (d+1)) l c - y l / y i * basisVector i c) := by
    funext y
    simp only [compressionAt, eliminationAt, Matrix.mul_apply, Matrix.sub_apply,
      Matrix.vecMulVec_apply, ratiosAt]
  rw [this]
  exact Finset.measurable_sum _ fun l _ => measurable_const.mul (measurable_const.sub
    (((measurable_pi_apply l).div (measurable_pi_apply i)).mul measurable_const))

lemma measurable_update (d : ℕ) :
    Measurable (fun p : Mat (d+1) × Vec (d+1) => update p.1 p.2) := by
  have hfix : ∀ i : Fin (d+1), Measurable (fun p : Mat (d+1) × Vec (d+1) => updateAt p.1 p.2 i) := by
    intro i
    have e : (fun p : Mat (d+1) × Vec (d+1) => updateAt p.1 p.2 i) = fun p => fun a b =>
        ∑ c, (∑ e, compressionAt p.2 i a e * p.1 e c) * compressionAt p.2 i b c := by
      funext p
      ext a b
      simp only [updateAt, Matrix.mul_apply, Matrix.transpose_apply]
    rw [e]
    refine measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun b => ?_
    refine Finset.measurable_sum _ fun c _ => ?_
    refine Measurable.mul (Finset.measurable_sum _ fun e _ => ?_) ?_
    · exact ((measurable_compressionAt i a e).comp measurable_snd).mul
        ((measurable_pi_apply c).comp ((measurable_pi_apply e).comp measurable_fst))
    · exact (measurable_compressionAt i b c).comp measurable_snd
  have h := measurable_at_index (X := Mat (d+1) × Vec (d+1)) (Y := Mat d) (k := d+1)
    (fun p i => updateAt p.1 p.2 i) hfix (fun p => pivot p.2)
    ((measurable_pivot d).comp measurable_snd)
  have e : (fun p : Mat (d+1) × Vec (d+1) => update p.1 p.2) =
      fun p => updateAt p.1 p.2 (pivot p.2) := by
    funext p; rfl
  rw [e]; exact h

lemma measurable_block (d : ℕ) : Measurable (fun S : CovState => block S d) :=
  measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j =>
    (measurable_pi_apply _).comp (measurable_pi_apply _)

lemma measurable_embed (d : ℕ) : Measurable (fun M : Mat d => embed M) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  simp only [embed]
  split_ifs
  · exact (measurable_pi_apply _).comp (measurable_pi_apply _)
  · exact measurable_const
  · exact measurable_const

lemma measurable_embed_update (d : ℕ) (B : Mat (d+1)) :
    Measurable (fun y : Vec (d+1) => embed (update B y)) := by
  have h := (measurable_update d).comp (measurable_prodMk_left (x := B))
  exact (measurable_embed d).comp h

lemma measurable_stateUpdate (D : ℕ) :
    Measurable (fun p : CovState × (ℕ → ℝ) => stateUpdate D p.1 p.2) := by
  cases D with
  | zero => exact measurable_fst
  | succ d =>
    simp only [stateUpdate]
    have h1 : Measurable (fun p : CovState × (ℕ → ℝ) =>
        (block p.1 (d+1), (fun j : Fin (d+1) => p.2 j.val))) :=
      ((measurable_block (d+1)).comp measurable_fst).prodMk
        (measurable_pi_lambda _ fun j => (measurable_pi_apply _).comp measurable_snd)
    have h2 := (measurable_update d).comp h1
    exact (measurable_embed d).comp h2

/-- First column of a square block, as a total infinite vector. -/
def col0 {D : ℕ} (M : Mat D) : ℕ → ℝ := fun i => if h : i < D then M ⟨i, h⟩ ⟨0, by omega⟩ else 0

lemma measurable_col0 (D : ℕ) : Measurable (fun M : Mat D => col0 M) := by
  refine measurable_pi_lambda _ fun i => ?_
  simp only [col0]
  split_ifs
  · exact (measurable_pi_apply _).comp (measurable_pi_apply _)
  · exact measurable_const

lemma actualCov_succ {n : ℕ} (A : Mat n) (t : ℕ) (ht : t < n) :
    actualCov A (t+1) =
      stateUpdate (n-t) (actualCov A t) (col0 (GEPPGrowth.Main.residual A t)) := by
  simp only [actualCov]
  congr 1
  funext i
  unfold actualColumn col0
  by_cases hi : i + t < n
  · rw [dif_pos hi, dif_pos ht, dif_pos (show i < n - t by omega)]
    simp only [GEPPGrowth.Main.residual, Matrix.submatrix_apply]
    congr 1
    exact Fin.ext (by simp)
  · rw [dif_neg hi, dif_neg (show ¬ i < n - t by omega)]

end GEPP415

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix ENNReal

noncomputable section

namespace GEPP415

open GEPPGrowth.Main

/-! ### Gaussian kernels -/

instance borelMat (d : ℕ) : BorelSpace (Mat d) :=
  inferInstanceAs (BorelSpace (Fin d → Fin d → ℝ))

open scoped MatrixOrder Classical in
/-- The PSD square root, extended by zero. -/
def sqrt' {d : ℕ} (S : Mat d) : Mat d := if 0 ≤ S then CFC.sqrt S else 0

open scoped MatrixOrder Classical in
lemma measurable_sqrt' (d : ℕ) : Measurable (fun S : Mat d => sqrt' S) := by
  classical
  have hcl : IsClosed {S : Mat d | 0 ≤ S} := by
    have : {S : Mat d | 0 ≤ S} = {S | S.PosSemidef} := by
      ext S; exact Matrix.nonneg_iff_posSemidef
    rw [this]
    have : {S : Mat d | S.PosSemidef} = {S | ∀ i j : Fin d, S j i = S i j} ∩
        ⋂ x : Fin d → ℝ, {S | 0 ≤ x ⬝ᵥ (S *ᵥ x)} := by
      ext S
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter,
        Matrix.posSemidef_iff_dotProduct_mulVec, Matrix.IsHermitian.ext_iff, star_trivial]
    rw [this]
    refine IsClosed.inter ?_ (isClosed_iInter fun x => isClosed_le continuous_const ?_)
    · simp only [Set.setOf_forall]
      exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq (by fun_prop) (by fun_prop)
    · simp only [dotProduct, Matrix.mulVec]; fun_prop
  have hc : ContinuousOn (fun S : Mat d => CFC.sqrt S) {S | 0 ≤ S} := by
    open scoped Matrix.Norms.L2Operator in exact CFC.continuousOn_sqrt
  have := ContinuousOn.measurable_piecewise hc (continuousOn_const (c := (0 : Mat d)))
    hcl.measurableSet
  convert this using 1
  funext S
  simp only [sqrt', Set.piecewise, Set.mem_setOf_eq]

open scoped MatrixOrder Classical in
lemma normal_eq_map' {d : ℕ} (S : Mat d) : normal S = (gam d).map (fun y => sqrt' S *ᵥ y) := by
  by_cases hS : 0 ≤ S
  · rw [normal_eq_map]; simp only [sqrt', if_pos hS]
  · have hS' : ¬ S.PosSemidef := fun h => hS (Matrix.nonneg_iff_posSemidef.2 h)
    simp only [sqrt', if_neg hS, Matrix.zero_mulVec]
    rw [Measure.map_const, measure_univ, one_smul]
    unfold normal
    rw [multivariateGaussian_of_not_posSemidef _ hS']
    ext s hs
    rw [Measure.map_apply (by fun_prop) hs, Measure.dirac_apply, Measure.dirac_apply]
    have h0 : (fun i => (0 : EuclideanSpace ℝ (Fin d)).ofLp i) = (0 : Vec d) := rfl
    simp only [Set.indicator, Set.mem_preimage, h0]
    rfl

/-- `x ↦ ν.map (f x)` is measurable when `f` is jointly measurable. -/
lemma measurable_map_kernel {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] (ν : Measure Y) [SFinite ν] (f : X → Y → Z)
    (hf : Measurable (Function.uncurry f)) : Measurable (fun x => ν.map (f x)) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  have : (fun x => ν.map (f x) s) = fun x => ν (Prod.mk x ⁻¹' (Function.uncurry f ⁻¹' s)) := by
    funext x
    rw [Measure.map_apply (show Measurable (f x) from hf.comp measurable_prodMk_left) hs]
    rfl
  rw [this]
  exact measurable_measure_prodMk_left (hf hs)

lemma columnsLaw_eq_map {d : ℕ} (S : Mat d) (D : ℕ) :
    columnsLaw S D = (Measure.pi fun _ : Fin D => gam d).map
      (fun z : Fin D → Vec d => fun i j => (sqrt' S *ᵥ z j) i) := by
  unfold columnsLaw
  simp_rw [normal_eq_map' S]
  have hT : Measurable (fun z i j => z j i : (Fin D → Vec d) → Matrix (Fin d) (Fin D) ℝ) :=
    measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j =>
      (measurable_pi_apply i).comp (measurable_pi_apply j)
  have hM : Measurable (fun y : Vec d => sqrt' S *ᵥ y) := by fun_prop
  rw [← Measure.pi_map_pi (fun _ => hM.aemeasurable)]
  exact Measure.map_map (μ := Measure.pi fun _ : Fin D => gam d) hT
    (measurable_pi_lambda _ fun j => hM.comp (measurable_pi_apply j))

lemma measurable_mulVec_sqrt (d : ℕ) :
    Measurable (fun p : Mat d × Vec d => sqrt' p.1 *ᵥ p.2) := by
  have h := measurable_sqrt' d
  refine measurable_pi_lambda _ fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.measurable_sum _ fun j _ => ?_
  exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp (h.comp measurable_fst))).mul
    ((measurable_pi_apply j).comp measurable_snd)

lemma measurable_columnsLaw (d D : ℕ) : Measurable (fun S : Mat d => columnsLaw S D) := by
  have e : (fun S : Mat d => columnsLaw S D) = fun S => (Measure.pi fun _ : Fin D => gam d).map
      (fun z : Fin D → Vec d => (fun i j => (sqrt' S *ᵥ z j) i : Matrix (Fin d) (Fin D) ℝ)) := by
    funext S; exact columnsLaw_eq_map S D
  rw [e]
  have h : Measurable (fun p : Mat d × (Fin D → Vec d) =>
      (fun i j => (sqrt' p.1 *ᵥ p.2 j) i : Matrix (Fin d) (Fin D) ℝ)) := by
    refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
    exact (measurable_pi_apply i).comp ((measurable_mulVec_sqrt d).comp
      (measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd)))
  exact measurable_map_kernel (X := Mat d) (Y := Fin D → Vec d) (Z := Matrix (Fin d) (Fin D) ℝ)
    _ (fun S z i j => (sqrt' S *ᵥ z j) i) h

lemma measurable_mulVec_sqrt_of {X : Type*} [MeasurableSpace X] {d : ℕ} (f : X → Mat d)
    (g : X → Vec d) (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x => sqrt' (f x) *ᵥ g x) := by
  have hs := (measurable_sqrt' d).comp hf
  refine measurable_pi_lambda _ fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.measurable_sum _ fun j _ => ?_
  exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hs)).mul
    ((measurable_pi_apply j).comp hg)

/-- The covariance step as a pushforward of a fixed Gaussian. -/
lemma covStep_succ_eq (d : ℕ) (S : CovState) :
    covStep (d+1) S = (gam (d+1)).map
      (fun z => embed (update (block S (d+1)) (sqrt' (block S (d+1)) *ᵥ z))) := by
  rw [covStep, normal_eq_map']
  have h1 : Measurable (fun z : Vec (d+1) => sqrt' (block S (d+1)) *ᵥ z) :=
    measurable_mulVec_sqrt_of _ _ measurable_const measurable_id
  exact Measure.map_map (μ := gam (d+1)) (measurable_embed_update d _) h1

lemma measurable_covStep (D : ℕ) : Measurable (covStep D) := by
  cases D with
  | zero => exact Measure.measurable_dirac
  | succ d =>
    have e : covStep (d+1) = fun S => (gam (d+1)).map
        (fun z => embed (update (block S (d+1)) (sqrt' (block S (d+1)) *ᵥ z))) :=
      funext (covStep_succ_eq d)
    rw [e]
    have hb : Measurable (fun p : CovState × Vec (d+1) => block p.1 (d+1)) :=
      (measurable_block (d+1)).comp measurable_fst
    have h1 : Measurable (fun p : CovState × Vec (d+1) =>
        (block p.1 (d+1), sqrt' (block p.1 (d+1)) *ᵥ p.2)) :=
      hb.prodMk (measurable_mulVec_sqrt_of _ _ hb measurable_snd)
    have h2 := (measurable_update d).comp h1
    have h3 := (measurable_embed d).comp h2
    exact measurable_map_kernel (X := CovState) (Y := Vec (d+1)) (Z := CovState) _
      (fun S z => embed (update (block S (d+1)) (sqrt' (block S (d+1)) *ᵥ z))) h3

/-- One covariance step is the update by the first column of a fresh `columnsLaw` sample. -/
lemma covStep_eq (D : ℕ) (hD : 0 < D) (S : CovState) :
    covStep D S = (columnsLaw (block S D) D).map (fun M => stateUpdate D S (col0 M)) := by
  obtain ⟨d, rfl⟩ : ∃ d, D = d + 1 := ⟨D - 1, by omega⟩
  set B := block S (d+1)
  set ν := Measure.pi fun _ : Fin (d+1) => normal B
  have hT : Measurable (fun z i j => z j i : (Fin (d+1) → Vec (d+1)) → Matrix (Fin (d+1)) (Fin (d+1)) ℝ) :=
    measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j =>
      (measurable_pi_apply i).comp (measurable_pi_apply j)
  have hΦ : Measurable (fun M : Mat (d+1) => stateUpdate (d+1) S (col0 M)) := by
    have h := (measurable_stateUpdate (d+1)).comp
      ((measurable_const (a := S)).prodMk (measurable_col0 (d+1)))
    exact h
  have e3 := Measure.map_map (μ := ν) (measurable_embed_update d B) (measurable_pi_apply 0)
  have e4 := Measure.map_map (μ := ν) hΦ hT
  have hcomp : (fun M : Mat (d+1) => stateUpdate (d+1) S (col0 M)) ∘
      (fun z i j => z j i : (Fin (d+1) → Vec (d+1)) → Matrix (Fin (d+1)) (Fin (d+1)) ℝ) =
      (fun y => embed (update B y)) ∘ (fun z => z 0) := by
    funext z
    have : (fun j : Fin (d+1) => col0 (fun i j => z j i : Mat (d+1)) j.val) = z 0 := by
      funext j; simp only [col0, dif_pos j.isLt]; rfl
    show embed (update (block S (d+1)) (fun j : Fin (d+1) =>
      col0 (fun i j => z j i : Mat (d+1)) j.val)) = embed (update B (z 0))
    rw [this]
  calc covStep (d+1) S = (normal B).map (fun y => embed (update B y)) := rfl
    _ = (ν.map (fun z => z 0)).map (fun y => embed (update B y)) := by
        rw [(measurePreserving_eval _ 0).map_eq]
    _ = ν.map ((fun y => embed (update B y)) ∘ (fun z => z 0)) := e3
    _ = ν.map ((fun M : Mat (d+1) => stateUpdate (d+1) S (col0 M)) ∘
          (fun z i j => z j i : (Fin (d+1) → Vec (d+1)) → Matrix (Fin (d+1)) (Fin (d+1)) ℝ)) := by
        rw [hcomp]
    _ = (ν.map (fun z i j => z j i : (Fin (d+1) → Vec (d+1)) → Matrix (Fin (d+1)) (Fin (d+1)) ℝ)).map
          (fun M : Mat (d+1) => stateUpdate (d+1) S (col0 M)) := e4.symm
    _ = _ := rfl

end GEPP415

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix ENNReal

noncomputable section

namespace GEPP415

open GEPPGrowth.Main

/-! ### The covariance process is the law of the actual GEPP covariances -/

instance gm_isProb (p m : ℕ) : IsProbabilityMeasure (gm p m) :=
  GaussianMatrix.gaussianMatrix_isProbabilityMeasure p m

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

lemma block_embed {d : ℕ} (M : Mat d) : block (embed M) d = M := by
  ext i j; simp [block, embed]

lemma columnsLaw_one (n : ℕ) : columnsLaw (1 : Mat n) n = gm n n := by
  unfold columnsLaw
  rw [normal_one]
  exact (transpose_mp n n).map_eq

/-- The residual law at time zero. -/
lemma hrl_zero (n : ℕ) : HasResidualLaw n 0 (Nat.zero_le n) := by
  refine ⟨⟨fun _ => embed (1 : Mat n), measurable_const, fun A => rfl⟩, ?_⟩
  intro H E hH hE
  have hbl : block (embed (1 : Mat n)) (n - 0) = (1 : Mat n) := block_embed _
  have hres : ∀ A : Mat n, GEPPGrowth.Main.residual A 0 = A := by
    intro A; ext i j; rfl
  have hF : ∀ A : Mat n, firstColumns (Nat.zero_le n) A = 0 := fun A => Subsingleton.elim _ _
  show (gm n n) {A : Mat n | firstColumns (Nat.zero_le n) A ∈ H ∧
      GEPPGrowth.Main.residual A 0 ∈ E} =
    ∫⁻ _ in {A : Mat n | firstColumns (Nat.zero_le n) A ∈ H},
      columnsLaw (block (embed (1 : Mat n)) (n - 0)) (n - 0) E ∂(gm n n)
  rw [setLIntegral_const, hbl, columnsLaw_one]
  by_cases h0 : (0 : Matrix (Fin n) (Fin 0) ℝ) ∈ H
  · have hS1 : {A : Mat n | firstColumns (Nat.zero_le n) A ∈ H ∧
        GEPPGrowth.Main.residual A 0 ∈ E} = E := by
      ext A; simp only [Set.mem_setOf_eq, hF A, hres A, h0, true_and]
    have hS2 : {A : Mat n | firstColumns (Nat.zero_le n) A ∈ H} = Set.univ := by
      ext A; simp only [Set.mem_setOf_eq, hF A, h0, Set.mem_univ]
    rw [hS1, hS2, measure_univ, mul_one]
    rfl
  · have hS1 : {A : Mat n | firstColumns (Nat.zero_le n) A ∈ H ∧
        GEPPGrowth.Main.residual A 0 ∈ E} = ∅ := by
      ext A; simp only [Set.mem_setOf_eq, hF A, h0, false_and, Set.mem_empty_iff_false]
    have hS2 : {A : Mat n | firstColumns (Nat.zero_le n) A ∈ H} = ∅ := by
      ext A; simp only [Set.mem_setOf_eq, hF A, h0, Set.mem_empty_iff_false]
    rw [hS1, hS2, measure_empty, mul_zero]

/-- One step of the comparison between the covariance process and actual GEPP. -/
lemma step (n t : ℕ) (ht : t < n) (hR : HasResidualLaw n t ht.le)
    (IH : covLaw n t ≤ (gm n n).map (fun A => actualCov A t)) :
    covLaw n (t+1) ≤ (gm n n).map (fun A => actualCov A (t+1)) := by
  obtain ⟨⟨c, hc, hcA⟩, hrect⟩ := hR
  set F := firstColumns ht.le with hFdef
  have hFm : Measurable F := measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j =>
    (measurable_pi_apply _).comp (measurable_pi_apply i)
  have hat : (fun A : Mat n => actualCov A t) = c ∘ F := funext fun A => (hcA A).symm
  have hatm : Measurable (fun A : Mat n => actualCov A t) := hat ▸ hc.comp hFm
  have hres := measurable_residual (n := n) t
  -- the residual kernel
  let κ : Kernel (Matrix (Fin n) (Fin t) ℝ) (Mat (n-t)) :=
    ⟨fun G => columnsLaw (block (c G) (n-t)) (n-t),
      (measurable_columnsLaw _ _).comp ((measurable_block _).comp hc)⟩
  haveI : IsMarkovKernel κ := ⟨fun G => columnsLaw_isProbabilityMeasure _ _⟩
  have hFmap : (gm n n).map F = gm n t := gm_map_cols (Fin.castLE ht.le) (Fin.castLE_injective _)
  -- joint law of (first columns, residual)
  have hjoint : (gm n n).map (fun A => (F A, GEPPGrowth.Main.residual A t)) = (gm n t) ⊗ₘ κ := by
    have hpm : Measurable (fun A => (F A, GEPPGrowth.Main.residual A t)) := hFm.prodMk hres
    haveI : IsFiniteMeasure ((gm n n).map (fun A => (F A, GEPPGrowth.Main.residual A t))) :=
      inferInstance
    refine MeasureTheory.ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ ?_
    · rintro _ ⟨H, hH, E, hE, rfl⟩
      have hH : MeasurableSet H := hH
      have hE : MeasurableSet E := hE
      rw [Measure.map_apply hpm (hH.prod hE), Measure.compProd_apply_prod hH hE, ← hFmap,
        setLIntegral_map hH (Kernel.measurable_coe κ hE) hFm]
      have := hrect H E hH hE
      have hκ : ∀ A : Mat n, κ (F A) E = columnsLaw (block (actualCov A t) (n-t)) (n-t) E :=
        fun A => by
          show columnsLaw (block (c (F A)) (n-t)) (n-t) E = _
          rw [hcA A]
      simp_rw [hκ]
      exact this
    · rw [Measure.map_apply hpm MeasurableSet.univ, Set.preimage_univ, measure_univ, measure_univ]
  rw [Measure.le_iff]
  intro s hs
  have hΦ : Measurable (fun p : Matrix (Fin n) (Fin t) ℝ × Mat (n-t) =>
      stateUpdate (n-t) (c p.1) (col0 p.2)) :=
    (measurable_stateUpdate (n-t)).comp ((hc.comp measurable_fst).prodMk
      ((measurable_col0 _).comp measurable_snd))
  set W := (fun p : Matrix (Fin n) (Fin t) ℝ × Mat (n-t) => stateUpdate (n-t) (c p.1) (col0 p.2)) ⁻¹' s
  have hW : MeasurableSet W := hΦ hs
  have hnext : (fun A : Mat n => actualCov A (t+1)) =
      fun A => stateUpdate (n-t) (c (F A)) (col0 (GEPPGrowth.Main.residual A t)) := by
    funext A; rw [actualCov_succ A t ht, hcA]
  have hnextm : Measurable (fun A : Mat n => actualCov A (t+1)) := by
    rw [hnext]
    exact hΦ.comp (hFm.prodMk hres)
  calc covLaw n (t+1) s = ∫⁻ S, covStep (n-t) S s ∂(covLaw n t) :=
        Measure.bind_apply hs (measurable_covStep _).aemeasurable
    _ ≤ ∫⁻ S, covStep (n-t) S s ∂((gm n n).map (fun A => actualCov A t)) := lintegral_mono' IH le_rfl
    _ = ∫⁻ A, covStep (n-t) (actualCov A t) s ∂(gm n n) :=
        lintegral_map ((Measure.measurable_coe hs).comp (measurable_covStep _)) hatm
    _ = ∫⁻ A, κ (F A) (Prod.mk (F A) ⁻¹' W) ∂(gm n n) := by
        refine lintegral_congr fun A => ?_
        have hm : Measurable (fun M : Mat (n-t) => stateUpdate (n-t) (actualCov A t) (col0 M)) := by
          have h := (measurable_stateUpdate (n-t)).comp
            ((measurable_const (a := actualCov A t)).prodMk (measurable_col0 (n-t)))
          exact h
        rw [covStep_eq (n-t) (by omega), Measure.map_apply hm hs]
        have hpre : Prod.mk (F A) ⁻¹' W =
            (fun M => stateUpdate (n-t) (actualCov A t) (col0 M)) ⁻¹' s := by
          rw [← hcA A]; rfl
        show _ = columnsLaw (block (c (F A)) (n-t)) (n-t) (Prod.mk (F A) ⁻¹' W)
        rw [hpre, hcA A]
    _ = ∫⁻ G, κ G (Prod.mk G ⁻¹' W) ∂(gm n t) := by
        rw [← hFmap, lintegral_map (Kernel.measurable_kernel_prodMk_left hW) hFm]
    _ = ((gm n t) ⊗ₘ κ) W := (Measure.compProd_apply hW).symm
    _ = (gm n n) ((fun A => (F A, GEPPGrowth.Main.residual A t)) ⁻¹' W) := by
        rw [← hjoint, Measure.map_apply (hFm.prodMk hres) hW]
    _ = ((gm n n).map (fun A => actualCov A (t+1))) s := by
        rw [Measure.map_apply hnextm hs, hnext]
        rfl

/-- `covLaw n t` is dominated by the law of the actual GEPP covariance after `t` steps. -/
lemma covLaw_le (n : ℕ) : ∀ t, (ht : t < n) →
    (∀ s, 1 ≤ s → (hs : s < t) → HasResidualLaw n s (hs.trans ht).le) →
    covLaw n t ≤ (gm n n).map (fun A => actualCov A t) := by
  intro t
  induction t with
  | zero =>
    intro _ _
    have : (fun A : Mat n => actualCov A 0) = fun _ => embed (1 : Mat n) := rfl
    rw [this, Measure.map_const, measure_univ, one_smul]
    rfl
  | succ t ih =>
    intro ht hR
    have hRt : HasResidualLaw n t (by omega) := by
      rcases Nat.eq_zero_or_pos t with h | h
      · subst h; exact hrl_zero n
      · exact hR t h (by omega)
    exact step n t (by omega) hRt (ih (by omega) fun s h1 h2 => hR s h1 (by omega))

/-- The bridge used for Proposition 4.15. -/
lemma covLaw_apply_le (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) (E : Set CovState)
    (hE : MeasurableSet E) :
    covLaw n (k-1) E ≤ gm n n {A | actualCov A (k-1) ∈ E} := by
  have hR : ∀ s, 1 ≤ s → (hs : s < k - 1) → HasResidualLaw n s (by omega) := by
    intro s h1 h2
    have := (lemma_4_13 n (s+1) (by omega) (by omega)).1
    simpa using this
  have hle := covLaw_le n (k-1) (by omega) hR
  obtain ⟨⟨c, hc, hcA⟩, -⟩ := (lemma_4_13 n k hk hkn).1
  have hatm : Measurable (fun A : Mat n => actualCov A (k-1)) := by
    have : (fun A : Mat n => actualCov A (k-1)) = c ∘ firstColumns (show k - 1 ≤ n by omega) :=
      funext fun A => (hcA A).symm
    rw [this]
    exact hc.comp (measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j =>
      (measurable_pi_apply _).comp (measurable_pi_apply i))
  calc covLaw n (k-1) E ≤ ((gm n n).map (fun A => actualCov A (k-1))) E := hle E
    _ = _ := Measure.map_apply hatm hE

end GEPP415

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix ENNReal

noncomputable section

namespace GEPP415

open GEPPGrowth.Main

/-- The tail bound with the binomial and moment-ratio constants. -/
lemma tail_covLaw (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) (m : ℕ) (τ : ℝ) (hτ : 0 ≤ τ) :
    prob (covLaw n (k-1)) {S | (block S (n-(k-1))).det ≤ τ} ≤
      (n.choose (k-1) : ℝ) * (τ ^ m * (gramMoment (k-1) (k-1) m / gramMoment n (k-1) m)) := by
  have hE : MeasurableSet {S : CovState | (block S (n-(k-1))).det ≤ τ} :=
    measurableSet_le ((measurable_det _).comp (measurable_block _)) measurable_const
  have h1 := covLaw_apply_le n k hk hkn _ hE
  have h2 := tail_gm n k m hk hkn τ hτ
  have hρ : 0 ≤ τ ^ m * (gramMoment (k-1) (k-1) m / gramMoment n (k-1) m) :=
    mul_nonneg (pow_nonneg hτ _) (div_nonneg (gramMoment_pos _ _ _ le_rfl).le
      (gramMoment_pos _ _ _ (by omega)).le)
  unfold prob
  have h3 : (covLaw n (k-1)) {S | (block S (n-(k-1))).det ≤ τ} ≤
      ENNReal.ofReal ((n.choose (k-1) : ℝ) *
        (τ ^ m * (gramMoment (k-1) (k-1) m / gramMoment n (k-1) m))) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
    exact h1.trans h2
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) h3

end GEPP415

open GEPPGrowth.Main in
theorem solution (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) :
    (∀ t : ℝ, 0 < t →
      prob (covLaw n (k-1)) {S | (block S (n-(k-1))).det ≤ t} ≤
        (t * ((n-k+1:ℕ)+2*Real.log n)^ (n-k+1) /
          Real.rpow (n:ℝ) ((n-k+1:ℕ)*(1-1/(Nat.ceil (Real.log n):ℝ)))) ^
            Nat.ceil (Real.log n)) ∧
    prob (covLaw n (k-1)) {S | (block S (n-(k-1))).det ≤
      (1 / Real.exp 1) * ((n:ℝ) /
        (Real.exp 1 * ((n-k+1:ℕ)+2*Real.log n)))^(n-k+1)} ≤ 1/(n:ℝ) := by
  have hn2 : 2 ≤ n := by omega
  have part1 : ∀ t : ℝ, 0 < t →
      prob (covLaw n (k-1)) {S | (block S (n-(k-1))).det ≤ t} ≤
        (t * ((n-k+1:ℕ)+2*Real.log n)^ (n-k+1) /
          Real.rpow (n:ℝ) ((n-k+1:ℕ)*(1-1/(Nat.ceil (Real.log n):ℝ)))) ^
            Nat.ceil (Real.log n) := by
    intro t ht
    refine (GEPP415.tail_covLaw n k hk hkn ⌈Real.log n⌉₊ t ht.le).trans ?_
    exact GEPP415.arith1 n (k-1) (n-k+1) (by omega) hn2 t ht
  refine ⟨part1, ?_⟩
  have hd : 1 ≤ n - k + 1 := by omega
  have hX : 0 < ((n-k+1:ℕ):ℝ) + 2 * Real.log n := by
    have : (1:ℝ) ≤ ((n-k+1:ℕ):ℝ) := by exact_mod_cast hd
    have : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    linarith
  have hτ : 0 < (1 / Real.exp 1) * ((n:ℝ) /
      (Real.exp 1 * ((n-k+1:ℕ)+2*Real.log n)))^(n-k+1) := by
    have : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    positivity
  refine (part1 _ hτ).trans ?_
  exact GEPP415.arith2 n (n-k+1) hd hn2
