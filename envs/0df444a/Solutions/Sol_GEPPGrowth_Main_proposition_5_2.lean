-- Prove2me | solution 1 for GEPPGrowth.Main.proposition_5_2
-- status  : ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-26T22:36:31.138125+00:00
-- url     : https://prove2.me/submissions/5138086a-03e3-4a02-a015-462125c3f1f9

import Definitions.Def_GEPPGrowth_Main_Process
import Theorems.Thm_GEPPGrowth_Main_lemma_4_5
import Theorems.Thm_GEPPGrowth_Main_proposition_4_12
import Theorems.Thm_GEPPGrowth_Main_proposition_5_1

-- vendored from Solutions.Lib.GEPP
section Solutions_Lib_GEPP

/-! Shared helpers for the GEPP growth mission, collected from accepted solutions.
Import as `import Solutions.Lib.GEPP`; `p2m check`/`verify` inline this file before submitting.
See docs/missions/gepp.md for what each lemma says. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

namespace P2mLib.GEPP

open GEPPGrowth.Main

section -- from Sol_gepp_prop_3_1.lean
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix
open GEPPGrowth.Main
/-- A linear image of a centered multivariate Gaussian is the Gaussian with covariance `A S Aᵀ`. -/
lemma mvG_map {m n : ℕ} (S : Mat n) (hS : S.PosSemidef) (A : Matrix (Fin m) (Fin n) ℝ) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) S).map
      (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)) =
    multivariateGaussian 0 (A * S * Aᵀ) := by
  have hS' : (A * S * Aᵀ).PosSemidef := by
    simpa using hS.mul_mul_conjTranspose_same A
  apply IsGaussian.ext
  · simp only [id]
    rw [ContinuousLinearMap.integral_id_map IsGaussian.integrable_id]
    simp
  · have hadj : ∀ w : EuclideanSpace ℝ (Fin m),
        ((LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)).adjoint w).ofLp =
          Aᵀ *ᵥ w.ofLp := by
      intro w
      have h1 := Matrix.toEuclideanLin_conjTranspose_eq_adjoint A
      have h2 := congrArg (fun f => (f w).ofLp) h1
      simp only [Matrix.ofLp_toEuclideanLin_apply] at h2
      rw [← ContinuousLinearMap.coe_coe, ← ContinuousLinearMap.adjoint_toLinearMap]
      simpa using h2.symm
    ext u v
    rw [covarianceBilin_map IsGaussian.memLp_two_id, covarianceBilin_multivariateGaussian hS,
      covarianceBilin_multivariateGaussian hS', hadj, hadj]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec u.ofLp A,
      Matrix.mulVec_transpose]

/-- `normal` version of `mvG_map`: `A x` for `x ~ N(0,S)` has law `N(0, A S Aᵀ)`. -/
lemma normal_map_mulVec {m n : ℕ} (S : Mat n) (hS : S.PosSemidef) (A : Matrix (Fin m) (Fin n) ℝ) :
    (normal S).map (fun x => A *ᵥ x) = normal (A * S * Aᵀ) := by
  unfold normal
  rw [← mvG_map S hS A, Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1

/-- A pushforward of a product measure is the bind of the sections. -/
lemma prod_map_eq_bind {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (ν : Measure α) (π : Measure β) [SFinite π] (G : α × β → γ) (hG : Measurable G) :
    (ν.prod π).map G = ν.bind (fun y => π.map (fun w => G (y, w))) := by
  have hk : Measurable (fun y => π.map (fun w => G (y, w))) := by
    refine Measure.measurable_of_measurable_coe _ (fun s hs => ?_)
    have : (fun y => π.map (fun w => G (y, w)) s) = fun y => π (Prod.mk y ⁻¹' (G ⁻¹' s)) := by
      funext y
      rw [Measure.map_apply (f := fun w => G (y, w)) (hG.comp measurable_prodMk_left) hs]
      rfl
    rw [this]
    exact measurable_measure_prodMk_left (hG hs)
  ext s hs
  rw [Measure.map_apply hG hs, Measure.prod_apply (hG hs), Measure.bind_apply hs hk.aemeasurable]
  refine lintegral_congr (fun y => ?_)
  rw [Measure.map_apply (f := fun w => G (y, w)) (hG.comp measurable_prodMk_left) hs]
  rfl

end

section -- from Sol_gepp_prop_3_3.lean
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.L2Operator
open GEPPGrowth.Main
/-- `D Dᵀ = 1`: the rows of the deletion matrix are distinct standard basis rows. -/
lemma deletion_mul_transpose {d : ℕ} (i : Fin (d+1)) :
    deletion i * (deletion i).transpose = 1 := by
  ext a b
  simp [Matrix.mul_apply, deletion, Matrix.one_apply, eq_comm]

/-- `Dᵀ D = 1 - eᵢ eᵢᵀ`: the projection that kills coordinate `i`. -/
lemma transpose_mul_deletion {d : ℕ} (i : Fin (d+1)) :
    (deletion i).transpose * deletion i =
      1 - Matrix.vecMulVec (basisVector i) (basisVector i) := by
  have key : ∀ g : Fin (d+1) → ℝ,
      ∑ a : Fin d, g (Equiv.swap 0 i a.succ) = ∑ k, g k - g i := by
    intro g
    rw [← Equiv.sum_comp (Equiv.swap 0 i) g, Fin.sum_univ_succ, Equiv.swap_apply_left]
    ring
  refine Matrix.ext fun b c => ?_
  have := key (fun k => (if k = b then 1 else 0) * (if k = c then 1 else 0))
  rw [Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.vecMulVec_apply]
  simp only [Matrix.transpose_apply, deletion]
  rw [this]
  simp only [basisVector]
  by_cases hb : b = i <;> by_cases hc : c = i <;> by_cases hbc : b = c <;>
    simp only [hb, hc, hbc, eq_comm (a := i)] <;> subst_vars <;>
    simp_all [Finset.sum_ite_eq'] <;> exact fun h => by simp_all

/-- The `i`-th row of `I - r eᵢᵀ` vanishes when `rᵢ = 1`, so `(1 - eᵢeᵢᵀ) E = E`. -/
lemma proj_mul_elim {d : ℕ} (y : Vec (d+1)) (i : Fin (d+1)) (hyi : y i ≠ 0) :
    (1 - Matrix.vecMulVec (basisVector i) (basisVector i)) * eliminationAt y i =
      eliminationAt y i := by
  ext a b
  by_cases ha : a = i
  · subst ha
    simp only [Matrix.mul_apply, eliminationAt, Matrix.vecMulVec_apply, basisVector, ratiosAt,
      Matrix.one_apply, Matrix.sub_apply]
    rw [Finset.sum_eq_zero fun x _ => by by_cases h : a = x <;> simp [h, eq_comm]]
    by_cases hab : a = b
    · subst hab; simp [hyi]
    · simp [hab, Ne.symm hab]
  · simp [Matrix.mul_apply, eliminationAt, Matrix.vecMulVec_apply, basisVector, ratiosAt,
      Matrix.one_apply, Matrix.sub_apply, ha]

/-- A matrix with `D Dᵀ = 1` has spectral norm at most one, and so does its transpose. -/
lemma norm_le_one_of_mul_transpose {m n : ℕ} (D : Matrix (Fin m) (Fin (n)) ℝ)
    (h : D * D.transpose = 1) : ‖D‖ ≤ 1 ∧ ‖D.transpose‖ ≤ 1 := by
  have h1 : ‖(1 : Matrix (Fin m) (Fin m) ℝ)‖ ≤ 1 := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun _ => by simp
  have hsq : ‖D.transpose‖ * ‖D.transpose‖ ≤ 1 := by
    have := Matrix.l2_opNorm_conjTranspose_mul_self D.transpose
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose, h] at this
    rw [← this]; exact h1
  have ht : ‖D.transpose‖ ≤ 1 := by nlinarith [norm_nonneg D.transpose]
  refine ⟨?_, ht⟩
  have := Matrix.l2_opNorm_conjTranspose D
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  rw [← this]; exact ht

end

section -- from Sol_gepp_prop_4_11.lean
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix
/-- A pushforward of a measure by a map into a measurable set gives its complement mass zero. -/
lemma map_compl_eq_zero {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    (f : α → β) {G : Set β} (hG : MeasurableSet G) (hf : ∀ x, f x ∈ G) : μ.map f Gᶜ = 0 := by
  by_cases h : AEMeasurable f μ
  · rw [Measure.map_apply_of_aemeasurable h hG.compl]
    have : f ⁻¹' Gᶜ = ∅ := by ext x; simp [hf x]
    simp [this]
  · simp [Measure.map_of_not_aemeasurable h]

lemma bind_compl_eq_zero {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    (κ : α → Measure β) {G : Set β} (hG : MeasurableSet G) (hκ : ∀ᵐ x ∂μ, κ x Gᶜ = 0) :
    μ.bind κ Gᶜ = 0 := by
  by_cases h : AEMeasurable κ μ
  · rw [Measure.bind_apply hG.compl h]
    simpa using lintegral_congr_ae hκ
  · simp [Measure.bind, Measure.map_of_not_aemeasurable h]

lemma block_embed {d : ℕ} (M : Mat d) : block (embed M) d = M := by
  ext i j; simp [block, embed]

/-- The deterministic core: one elimination step keeps `S ⪰ I`, for any column and pivot. -/
lemma updateAt_sub_one {d : ℕ} (S : Mat (d+1)) (hS : (S - 1).PosSemidef) (y : Vec (d+1))
    (i : Fin (d+1)) : (updateAt S y i - 1).PosSemidef := by
  set C := compressionAt y i
  set w : Vec d := fun a => ratiosAt y i (Equiv.swap 0 i a.succ)
  have hrow : ∀ a c, C a c = (if Equiv.swap 0 i a.succ = c then 1 else 0) -
      (if c = i then w a else 0) := by
    intro a c
    simp only [C, w, compressionAt, deletion, eliminationAt, Matrix.mul_apply, Matrix.sub_apply,
      Matrix.one_apply, Matrix.vecMulVec_apply, basisVector, mul_sub]
    simp [Finset.sum_sub_distrib, ite_mul, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq', eq_comm]
  have hC : C * C.transpose = 1 + Matrix.vecMulVec w w := by
    ext a a'
    have hne : ∀ a : Fin d, Equiv.swap 0 i a.succ ≠ i := by
      intro a h
      rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right] at h
      exact Fin.succ_ne_zero a h
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hrow]
    simp [sub_mul, mul_sub, Finset.sum_sub_distrib, ite_mul, mul_ite, Finset.sum_ite_eq,
      Finset.sum_ite_eq', hne, Matrix.one_apply, Matrix.vecMulVec_apply, Fin.succ_inj]
  have hsplit : updateAt S y i - 1 = C * (S - 1) * C.transpose + Matrix.vecMulVec w w := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hC]
    simp only [updateAt, C]
    abel
  rw [hsplit]
  have h1 := hS.mul_mul_conjTranspose_same C
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h1
  have h2 := Matrix.posSemidef_vecMulVec_self_star w
  rw [star_trivial] at h2
  exact h1.add h2

end

section -- from Sol_gepp_prop_4_12.lean
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.L2Operator
open GEPPGrowth.Main
/-- Rayleigh bound: `xᵀ M x ≤ ‖M‖ |x|²` for the l2 operator norm. -/
lemma dot_mulVec_le_specNorm {d : ℕ} (M : Mat d) (x : Vec d) :
    x ⬝ᵥ (M *ᵥ x) ≤ GaussianMatrix.specNorm M * (x ⬝ᵥ x) := by
  have h := Matrix.l2_opNorm_mulVec M (WithLp.toLp 2 x)
  have hin := real_inner_le_norm (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))
    ((EuclideanSpace.equiv (Fin d) ℝ).symm (M *ᵥ x))
  have hxx : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖ ^ 2 = x ⬝ᵥ x := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]; simp [dotProduct, sq]
  have hin' : x ⬝ᵥ (M *ᵥ x) = inner ℝ (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))
      ((EuclideanSpace.equiv (Fin d) ℝ).symm (M *ᵥ x)) := by
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  have hn0 := norm_nonneg (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))
  simp only at h
  rw [hin', ← hxx]
  show _ ≤ ‖M‖ * _
  nlinarith

/-- For symmetric PSD `S` with `S v = λ v`, `|v| = 1`: `uᵀ S u ≥ λ (u·v)²`. -/
lemma quad_ge_of_eig {d : ℕ} (S : Mat d) (hS : S.PosSemidef) (v : Vec d)
    (hv : v ⬝ᵥ v = 1) (lam : ℝ) (heig : S *ᵥ v = lam • v) (u : Vec d) :
    lam * (u ⬝ᵥ v) ^ 2 ≤ u ⬝ᵥ (S *ᵥ u) := by
  set a := u ⬝ᵥ v
  set u' := u - a • v with hu'
  have hu'v : u' ⬝ᵥ v = 0 := by
    simp [hu', sub_dotProduct, smul_dotProduct, hv, a]
  have hsymm : S.transpose = S := hS.1
  have hSu : S *ᵥ u = S *ᵥ u' + (a * lam) • v := by
    rw [show u = u' + a • v by simp [hu'], Matrix.mulVec_add, Matrix.mulVec_smul, heig, smul_smul]
  have hvS : v ⬝ᵥ (S *ᵥ u') = 0 := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsymm, heig, smul_dotProduct,
      dotProduct_comm, hu'v, smul_zero]
  have key : u ⬝ᵥ (S *ᵥ u) = u' ⬝ᵥ (S *ᵥ u') + lam * a ^ 2 := by
    rw [hSu]
    conv_lhs => rw [show u = u' + a • v by simp [hu']]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, hvS, hu'v, hv,
      smul_eq_mul]
    ring
  have := hS.dotProduct_mulVec_nonneg u'
  simp at this
  nlinarith

end

end P2mLib.GEPP

end Solutions_Lib_GEPP

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.L2Operator

noncomputable section

namespace GEPPGrowth.Main.Prop52

open GEPPGrowth.Main P2mLib.GEPP

/-- A unit eigenvector of a PSD `S` for the eigenvalue `‖S‖`. -/
lemma exists_top_eig {d : ℕ} (hd : 0 < d) (S : Mat d) (hS : S.PosSemidef) :
    ∃ v : Vec d, sqLength v = 1 ∧ S *ᵥ v = GaussianMatrix.specNorm S • v := by
  have hH := hS.1
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have : Nontrivial (Mat d) := inferInstance
  obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image Finset.univ (fun i => |hH.eigenvalues i|)
    Finset.univ_nonempty
  set v := hH.eigenvectorBasis i0
  have hv1 : (v : Vec d) ⬝ᵥ (v : Vec d) = 1 := by
    have h := (hH.eigenvectorBasis.orthonormal.1 i0)
    rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at h
    simpa [dotProduct, sq] using h
  have hmv := hH.mulVec_eigenvectorBasis i0
  have hge : GaussianMatrix.specNorm S ≤ hH.eigenvalues i0 := by
    have hspec := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at hspec
    have hU := hH.eigenvectorUnitary.2
    unfold GaussianMatrix.specNorm
    calc ‖S‖ ≤ ‖(hH.eigenvectorUnitary : Mat d)‖ * ‖Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues)‖ *
          ‖(star hH.eigenvectorUnitary : Mat d)‖ := by
            conv_lhs => rw [hspec]
            exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ = ‖(RCLike.ofReal ∘ hH.eigenvalues : Fin d → ℝ)‖ := by
            rw [norm_star, CStarRing.norm_of_mem_unitary hU,
              Matrix.l2_opNorm_diagonal]; ring
      _ ≤ hH.eigenvalues i0 := by
            refine (pi_norm_le_iff_of_nonneg (hS.eigenvalues_nonneg i0)).2 fun i => ?_
            have := hi0 i (Finset.mem_univ _)
            simp only [Function.comp_apply, RCLike.ofReal_real_eq_id, id, Real.norm_eq_abs]
            rwa [abs_of_nonneg (hS.eigenvalues_nonneg i0)] at this
  have hle : hH.eigenvalues i0 ≤ GaussianMatrix.specNorm S := by
    have h := dot_mulVec_le_specNorm S (v : Vec d)
    rw [hmv, dotProduct_smul, hv1, smul_eq_mul, mul_one, mul_one] at h
    exact h
  refine ⟨v, ?_, ?_⟩
  · simpa [sqLength, dotProduct, sq] using hv1
  · rw [hmv, le_antisymm hle hge]

/-- `S ⪰ I` forces `‖S⁻¹‖ ≤ 1`. -/
lemma specNorm_inv_le_one {d : ℕ} (S : Mat d) (hS : S.PosDef) (hI : (S - 1).PosSemidef) :
    GaussianMatrix.specNorm S⁻¹ ≤ 1 := by
  unfold GaussianMatrix.specNorm
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  set u : Vec d := S⁻¹ *ᵥ x.ofLp with hu
  change ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin d))‖ ≤ 1 * ‖x‖
  have hSu : S *ᵥ u = x.ofLp := by
    rw [hu, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hS.det_pos.ne'), Matrix.one_mulVec]
  have hnorm : ∀ w : Vec d, ‖(WithLp.toLp 2 w : EuclideanSpace ℝ (Fin d))‖ ^ 2 = w ⬝ᵥ w := by
    intro w
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]; simp [dotProduct, sq]
  have hpsd := hI.dotProduct_mulVec_nonneg u
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, hSu] at hpsd
  have hcs := real_inner_le_norm (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin d)) x
  have hin : inner ℝ (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin d)) x = u ⬝ᵥ x.ofLp := by
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  have h1 := hnorm u
  have hx := hnorm x.ofLp
  simp only [WithLp.toLp_ofLp] at hx
  rw [hin] at hcs
  have := norm_nonneg (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin d))
  have := norm_nonneg x
  nlinarith

lemma specNorm_inv_pos {d : ℕ} (S : Mat (d+1)) (hS : S.PosDef) :
    0 < GaussianMatrix.specNorm S⁻¹ := by
  unfold GaussianMatrix.specNorm
  refine norm_pos_iff.2 fun h => ?_
  have h1 := Matrix.nonsing_inv_mul S (isUnit_iff_ne_zero.2 hS.det_pos.ne')
  rw [h, zero_mul] at h1
  exact zero_ne_one h1

/-- The three cone conditions at a pivot index `i`. -/
def Cond {d : ℕ} (v y : Vec (d+1)) (i : Fin (d+1)) : Prop :=
  (v i) ^ 2 ≥ 1 / ((d+1 : ℕ) : ℝ) ∧
    sqLength (ratiosAt y i) ≥ ((d+1 : ℕ) : ℝ) / 2 ∧
    v i * deletedInner i v (ratiosAt y i) ≤ 0

lemma ratiosAt_smul {d : ℕ} (y : Vec (d+1)) (i : Fin (d+1)) {t : ℝ} (ht : 0 < t) :
    ratiosAt (fun j => t * y j) i = ratiosAt y i := by
  funext j; simp [ratiosAt, mul_div_mul_left _ _ ht.ne']

lemma prob_mono {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {A B : Set α} (h : A ⊆ B) : prob μ A ≤ prob μ B :=
  ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono h)

end GEPPGrowth.Main.Prop52

open GEPPGrowth.Main GEPPGrowth.Main.Prop52

theorem solution (d : ℕ) (hd : 3 ≤ d) (S : Mat (d+1))
    (hS : S.PosDef) (hI : (S-1).PosSemidef)
    (p : Vec (d+1) → Fin (d+1))
    (hmax : ∀ y, IsMaxPivot y (p y)) :
    (0.16:ℝ)^(d+1) / (2*((d+1:ℕ):ℝ)*Real.sqrt S.det) ≤
      prob (normal S) {y | (3/2 - 2/((d+1:ℕ):ℝ))*GaussianMatrix.specNorm S ≤
        GaussianMatrix.specNorm (updateAt S y (p y))} := by
  classical
  obtain ⟨v, hv, heig⟩ := exists_top_eig (Nat.succ_pos d) S hS.posSemidef
  -- the conic set: every max pivot satisfies the cone conditions
  set E : Set (Vec (d+1)) := {y | ∀ i, IsMaxPivot y i → Cond v y i} with hE
  -- an adversarial selector: a failing max pivot if there is one
  let q : Vec (d+1) → Fin (d+1) := fun y =>
    if h : ∃ i, IsMaxPivot y i ∧ ¬ Cond v y i then h.choose else p y
  have hq : ∀ y, IsMaxPivot y (q y) := by
    intro y
    by_cases h : ∃ i, IsMaxPivot y i ∧ ¬ Cond v y i
    · simp only [q, dif_pos h]; exact h.choose_spec.1
    · simp only [q, dif_neg h]; exact hmax y
  have hconeE : growthConeWith q v ⊆ E := by
    intro y hy i hi
    by_contra hc
    have h : ∃ i, IsMaxPivot y i ∧ ¬ Cond v y i := ⟨i, hi, hc⟩
    have := h.choose_spec.2
    simp only [growthConeWith, Set.mem_ofPred_eq, q, dif_pos h] at hy
    exact this hy
  have hEconic : Conic E := by
    intro y hy t ht i hi
    have hi' : IsMaxPivot y i := by
      intro j
      have := hi j
      simp only [abs_mul, abs_of_pos ht] at this
      exact le_of_mul_le_mul_left this ht
    obtain ⟨h1, h2, h3⟩ := hy i hi'
    refine ⟨h1, ?_, ?_⟩ <;> rw [ratiosAt_smul y i ht] <;> assumption
  have hEsub : E ⊆ {y | (3/2 - 2/((d+1:ℕ):ℝ))*GaussianMatrix.specNorm S ≤
      GaussianMatrix.specNorm (updateAt S y (p y))} := by
    intro y hy
    obtain ⟨h1, h2, h3⟩ := hy (p y) (hmax y)
    have hy0 : y ≠ 0 := by
      rintro rfl
      have : sqLength (ratiosAt (0 : Vec (d+1)) (p 0)) = 0 := by
        simp [sqLength, ratiosAt]
      rw [this] at h2
      have : (0:ℝ) < ((d+1:ℕ):ℝ) / 2 := by positivity
      linarith
    have hd1 : 1 ≤ d := by omega
    have hlarge : (2:ℝ) ≤ ((d+1:ℕ):ℝ) / 2 := by
      have : (3:ℝ) ≤ d := by exact_mod_cast hd
      push_cast; linarith
    have := proposition_4_12 d hd1 S hS v hv heig y hy0 (p y) (hmax y) 2 (by norm_num) h1 h2
      hlarge h3
    simp only [Set.mem_ofPred_eq]
    convert this using 2
    norm_num
  have h51 := proposition_5_1 d hd v hv q hq
  have h45 := lemma_4_5 (d+1) S hS E hEconic
  have hn1 := specNorm_inv_le_one S hS hI
  have hn0 := specNorm_inv_pos S hS
  set x := GaussianMatrix.specNorm S⁻¹
  have hxa : 0 < Real.rpow x (((d+1:ℕ):ℝ)/2) := Real.rpow_pos_of_pos hn0 _
  have hxa1 : Real.rpow x (((d+1:ℕ):ℝ)/2) ≤ 1 := Real.rpow_le_one hn0.le hn1 (by positivity)
  have hdet : 0 < Real.sqrt S.det := Real.sqrt_pos.2 hS.det_pos
  have hPI : (0.16:ℝ)^(d+1) / (2*((d+1:ℕ):ℝ)) ≤ prob (normal (1 : Mat (d+1))) E :=
    h51.trans (prob_mono _ hconeE)
  refine le_trans ?_ (h45.trans (prob_mono _ hEsub))
  set a := Real.rpow x (((d+1:ℕ):ℝ)/2)
  set B := (0.16:ℝ)^(d+1) / (2*((d+1:ℕ):ℝ))
  have hB : 0 ≤ B := by positivity
  calc (0.16:ℝ)^(d+1) / (2*((d+1:ℕ):ℝ)*Real.sqrt S.det) = B * (1 / Real.sqrt S.det) := by
        simp only [B]; field_simp
    _ ≤ prob (normal (1 : Mat (d+1))) E * (1 / (a * Real.sqrt S.det)) := by
        refine mul_le_mul hPI (one_div_le_one_div_of_le (by positivity) ?_) (by positivity)
          (hB.trans hPI)
        nlinarith
    _ = _ := by ring
