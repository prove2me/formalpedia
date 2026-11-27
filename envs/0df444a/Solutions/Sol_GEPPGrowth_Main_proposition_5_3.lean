-- Prove2me | solution 1 for GEPPGrowth.Main.proposition_5_3
-- status  : ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-26T22:46:03.784374+00:00
-- url     : https://prove2.me/submissions/51975051-7fec-435a-acec-5ce95db06774

import Definitions.Def_GEPPGrowth_Main_Process
import Theorems.Thm_GEPPGrowth_Main_proposition_5_2
import Theorems.Thm_GEPPGrowth_Main_proposition_4_14
import Theorems.Thm_GEPPGrowth_Main_proposition_4_15
import Theorems.Thm_GEPPGrowth_Main_proposition_4_16
import Theorems.Thm_GEPPGrowth_Main_proposition_4_11

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
open scoped BigOperators Matrix ENNReal

noncomputable section

namespace GEPP53

open GEPPGrowth.Main P2mLib.GEPP

instance matBorel (a b : ℕ) : BorelSpace (Matrix (Fin a) (Fin b) ℝ) :=
  inferInstanceAs (BorelSpace (Fin a → Fin b → ℝ))

/-- The standard Gaussian on `Fin d → ℝ`. -/
abbrev gam (d : ℕ) : Measure (Fin d → ℝ) := Measure.pi (fun _ : Fin d => gaussianReal 0 1)

/-! ### Measurability of the covariance kernel (from the 4.14 solution) -/

open scoped Matrix.Norms.L2Operator MatrixOrder in
lemma cont_sqrt (d : ℕ) : ContinuousOn (CFC.sqrt : Mat d → Mat d) {a | 0 ≤ a} :=
  CFC.continuousOn_sqrt

open scoped MatrixOrder in
lemma psd_closed (d : ℕ) : IsClosed {a : Mat d | 0 ≤ a} := by
  have : {a : Mat d | 0 ≤ a} = {a | ∀ i j : Fin d, a j i = a i j} ∩
      ⋂ x : Fin d → ℝ, {a | 0 ≤ x ⬝ᵥ (a *ᵥ x)} := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Matrix.nonneg_iff_posSemidef,
      Matrix.posSemidef_iff_dotProduct_mulVec, Matrix.IsHermitian.ext_iff, star_trivial]
  rw [this]
  refine IsClosed.inter ?_ (isClosed_iInter fun x => isClosed_le continuous_const ?_)
  · simp only [Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_eq (by fun_prop) (by fun_prop)
  · simp only [dotProduct, Matrix.mulVec]; fun_prop

open scoped MatrixOrder in
lemma measurable_sqrt (d : ℕ) : Measurable (CFC.sqrt : Mat d → Mat d) := by
  classical
  have : (CFC.sqrt : Mat d → Mat d) =
      Set.piecewise {a : Mat d | 0 ≤ a} CFC.sqrt (fun _ => 0) := by
    funext a
    by_cases ha : 0 ≤ a
    · simp [Set.piecewise, ha]
    · simp only [Set.piecewise, Set.mem_setOf_eq, ha, if_false]
      exact CFC.sqrt_of_not_nonneg ha
  rw [this]
  exact ContinuousOn.measurable_piecewise (cont_sqrt d) continuousOn_const
    (psd_closed d).measurableSet

open scoped MatrixOrder in
lemma normal_eq_map (d : ℕ) (S : Mat d) :
    normal S = (gam d).map (fun y => CFC.sqrt S *ᵥ y) := by
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

lemma meas_entry {α : Type*} [MeasurableSpace α] {p q : ℕ} {f : α → Matrix (Fin p) (Fin q) ℝ}
    (hf : Measurable f) (a : Fin p) (b : Fin q) : Measurable (fun x => f x a b) :=
  (measurable_pi_apply b).comp ((measurable_pi_apply a).comp hf)

lemma measurable_mulVec (d : ℕ) : Measurable (fun p : Mat d × Vec d => p.1 *ᵥ p.2) := by
  refine measurable_pi_lambda _ fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.measurable_sum _ fun j _ =>
    (meas_entry measurable_fst i j).mul ((measurable_pi_apply j).comp measurable_snd)

open scoped MatrixOrder in
lemma measurable_normal (d : ℕ) : Measurable (fun S : Mat d => normal S) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  have hm : Measurable (fun p : Mat d × Vec d => CFC.sqrt p.1 *ᵥ p.2) :=
    (measurable_mulVec d).comp (((measurable_sqrt d).comp measurable_fst).prodMk measurable_snd)
  have : ∀ S : Mat d, normal S s =
      gam d (Prod.mk S ⁻¹' ((fun p : Mat d × Vec d => CFC.sqrt p.1 *ᵥ p.2) ⁻¹' s)) := by
    intro S
    have hmS : Measurable (fun y : Vec d => CFC.sqrt S *ᵥ y) :=
      (measurable_mulVec d).comp (measurable_const.prodMk measurable_id)
    rw [normal_eq_map, Measure.map_apply hmS hs]
    rfl
  simp_rw [this]
  exact measurable_measure_prodMk_left (hm hs)

lemma measurable_block (m : ℕ) : Measurable (fun S : CovState => block S m) :=
  measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j =>
    (measurable_pi_apply _).comp (measurable_pi_apply _)

/-- Extension of a vector by zeros. -/
def ext (m : ℕ) (v : Vec m) : ℕ → ℝ := fun i => if h : i < m then v ⟨i, h⟩ else 0

lemma measurable_ext (m : ℕ) : Measurable (ext m) := by
  refine measurable_pi_lambda _ fun i => ?_
  by_cases h : i < m
  · simp only [ext, h, dif_pos]; exact measurable_pi_apply _
  · simp only [ext, h, dif_neg, not_false_eq_true]; exact measurable_const

/-! ### Measurability of the covariance update -/

lemma measurable_foldl {α : Type*} [MeasurableSpace α] {k : ℕ}
    (g : α → Fin k → Fin k → Fin k) (hg : ∀ j, Measurable (fun p : α × Fin k => g p.1 p.2 j))
    (l : List (Fin k)) :
    ∀ b : α → Fin k, Measurable b → Measurable (fun a => l.foldl (g a) (b a)) := by
  induction l with
  | nil => intro b hb; simpa using hb
  | cons j l ih => intro b hb; exact ih _ ((hg j).comp (measurable_id.prodMk hb))

lemma measurable_pivot (d : ℕ) : Measurable (fun y : Vec (d+1) => pivot y) := by
  unfold pivot
  refine measurable_foldl _ (fun j => ?_) _ _ measurable_const
  refine measurable_from_prod_countable_left fun b => ?_
  refine Measurable.ite ?_ measurable_const measurable_const
  simp only [Set.setOf_or, Set.setOf_and]
  exact (measurableSet_lt (by fun_prop) (by fun_prop)).union
    ((measurableSet_eq_fun (by fun_prop) (by fun_prop)).inter (MeasurableSet.const _))

lemma measurable_compressionAt (d : ℕ) (i : Fin (d+1)) :
    Measurable (fun y : Vec (d+1) => compressionAt y i) := by
  refine measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun b => ?_
  simp only [compressionAt, eliminationAt, ratiosAt, Matrix.mul_apply, Matrix.sub_apply,
    Matrix.vecMulVec_apply]
  fun_prop

lemma measurable_updateAt (d : ℕ) (i : Fin (d+1)) :
    Measurable (fun p : Mat (d+1) × Vec (d+1) => updateAt p.1 p.2 i) := by
  have hC : Measurable (fun p : Mat (d+1) × Vec (d+1) => compressionAt p.2 i) :=
    (measurable_compressionAt d i).comp measurable_snd
  refine measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun b => ?_
  simp only [updateAt, Matrix.mul_apply, Matrix.transpose_apply]
  refine Finset.measurable_sum _ fun e _ => Measurable.mul
    (Finset.measurable_sum _ fun f _ => (meas_entry hC a f).mul (meas_entry measurable_fst f e))
    (meas_entry hC b e)

lemma measurable_update (d : ℕ) :
    Measurable (fun p : Mat (d+1) × Vec (d+1) => updateAt p.1 p.2 (pivot p.2)) := by
  have h : Measurable (fun q : (Mat (d+1) × Vec (d+1)) × Fin (d+1) => updateAt q.1.1 q.1.2 q.2) :=
    measurable_from_prod_countable_left fun i => measurable_updateAt d i
  have h2 : Measurable (fun p : Mat (d+1) × Vec (d+1) => (p, pivot p.2)) :=
    measurable_id.prodMk ((measurable_pivot d).comp measurable_snd)
  have := h.comp h2
  simp only [Function.comp_def] at this
  exact this

lemma measurable_embed (d : ℕ) : Measurable (fun M : Mat d => embed M) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  by_cases hi : i < d
  · by_cases hj : j < d
    · simp only [embed, hi, hj, dif_pos]; exact meas_entry measurable_id _ _
    · simp only [embed, hi, hj, dif_pos, dif_neg, not_false_eq_true]; exact measurable_const
  · simp only [embed, hi, dif_neg, not_false_eq_true]; exact measurable_const

lemma measurable_stateUpdate (m : ℕ) :
    Measurable (fun p : CovState × (ℕ → ℝ) => stateUpdate m p.1 p.2) := by
  cases m with
  | zero => exact measurable_fst
  | succ d =>
    have e : (fun p : CovState × (ℕ → ℝ) => stateUpdate (d+1) p.1 p.2) =
        fun p => embed (updateAt (block p.1 (d+1)) (fun j : Fin (d+1) => p.2 j.val)
          (pivot (fun j : Fin (d+1) => p.2 j.val))) := by
      funext p; simp only [stateUpdate, update]
    rw [e]
    have h1 : Measurable (fun p : CovState × (ℕ → ℝ) =>
        (block p.1 (d+1), (fun j : Fin (d+1) => p.2 j.val))) :=
      ((measurable_block (d+1)).comp measurable_fst).prodMk
        (measurable_pi_lambda _ fun j => (measurable_pi_apply _).comp measurable_snd)
    have := (measurable_embed d).comp ((measurable_update d).comp h1)
    simp only [Function.comp_def] at this
    exact this

lemma covStep_eq (m : ℕ) (S : CovState) :
    covStep m S = (normal (block S m)).map (fun v => stateUpdate m S (ext m v)) := by
  cases m with
  | zero => simp [covStep, stateUpdate, Measure.map_const]
  | succ d =>
    simp only [covStep, stateUpdate]
    congr 2
    funext v
    congr 2
    funext j
    simp [ext, j.isLt]

/-! ### Generic measure-theory helpers -/

/-- The transition kernel of the covariance process is measurable. -/
lemma measurable_covStep (m : ℕ) : Measurable (covStep m) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  let κ : Kernel CovState (Vec m) :=
    ⟨fun S => normal (block S m), (measurable_normal m).comp (measurable_block m)⟩
  haveI : IsMarkovKernel κ := ⟨fun S => normal_isProbabilityMeasure (block S m)⟩
  have hG : MeasurableSet {p : CovState × Vec m | stateUpdate m p.1 (ext m p.2) ∈ s} :=
    (measurable_stateUpdate m).comp (measurable_fst.prodMk ((measurable_ext m).comp measurable_snd)) hs
  have e : ∀ S, covStep m S s = κ S (Prod.mk S ⁻¹' {p : CovState × Vec m | stateUpdate m p.1 (ext m p.2) ∈ s}) := by
    intro S
    have hm : Measurable (fun v => stateUpdate m S (ext m v)) :=
      (measurable_stateUpdate m).comp (measurable_const.prodMk (measurable_ext m))
    rw [covStep_eq, Measure.map_apply hm hs]
    rfl
  simp_rw [e]
  exact Kernel.measurable_kernel_prodMk_left hG

instance covStep_prob (m : ℕ) (S : CovState) : IsProbabilityMeasure (covStep m S) := by
  have hm : Measurable (fun v => stateUpdate m S (ext m v)) :=
    (measurable_stateUpdate m).comp (measurable_const.prodMk (measurable_ext m))
  rw [covStep_eq]
  exact Measure.isProbabilityMeasure_map hm.aemeasurable

instance covLaw_prob (n t : ℕ) : IsProbabilityMeasure (covLaw n t) := by
  induction t with
  | zero => simp only [covLaw]; infer_instance
  | succ t ih =>
    simp only [covLaw]
    constructor
    rw [Measure.bind_apply MeasurableSet.univ (measurable_covStep _).aemeasurable]
    simp

/-! ### The pivot is a maximal pivot -/

lemma foldl_spec {ι K : Type*} [LinearOrder K] (P : ι → Prop) [DecidablePred P] (key : ι → K)
    (L : List ι) (b₀ : ι) :
    ((L.foldl (fun b j => if P j ∧ key b < key j then j else b) b₀) = b₀ ∨
        P (L.foldl (fun b j => if P j ∧ key b < key j then j else b) b₀)) ∧
      key b₀ ≤ key (L.foldl (fun b j => if P j ∧ key b < key j then j else b) b₀) ∧
      ∀ j ∈ L, P j → key j ≤ key (L.foldl (fun b j => if P j ∧ key b < key j then j else b) b₀) := by
  induction L generalizing b₀ with
  | nil => simp
  | cons x L ih =>
    simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp]
    by_cases hx : P x ∧ key b₀ < key x
    · rw [if_pos hx]
      obtain ⟨h1, h2, h3⟩ := ih x
      refine ⟨h1.elim (fun h => Or.inr (by rw [h]; exact hx.1)) Or.inr, hx.2.le.trans h2, fun _ => h2, h3⟩
    · rw [if_neg hx]
      obtain ⟨h1, h2, h3⟩ := ih b₀
      refine ⟨h1, h2, fun hP => ?_, h3⟩
      exact (not_lt.1 fun h => hx ⟨hP, h⟩).trans h2

def keyV {d : ℕ} (y : Vec d) (j : Fin d) : Lex (ℝ × (Fin d)ᵒᵈ) :=
  toLex (|y j|, OrderDual.toDual j)

lemma pivot_max {d : ℕ} (y : Vec (d+1)) : IsMaxPivot y (pivot y) := by
  have hp : pivot y = (List.finRange (d+1)).foldl
      (fun b j => if True ∧ keyV y b < keyV y j then j else b) 0 := by
    unfold pivot
    congr 1
    funext b j
    simp only [keyV, Prod.Lex.toLex_lt_toLex, OrderDual.toDual_lt_toDual, true_and]
  intro j
  obtain ⟨-, -, h3⟩ := foldl_spec (fun _ => True) (keyV y) (List.finRange (d+1)) 0
  have := h3 j (List.mem_finRange j) trivial
  rw [← hp] at this
  simp only [keyV, Prod.Lex.toLex_le_toLex] at this
  rcases this with h | h
  · exact h.le
  · exact h.1.le

/-! ### The good sets along the chain -/

/-- States whose leading `D`-block dominates `I`, has norm at least `a` and determinant at
most `b`. -/
def Good (D : ℕ) (a b : ℝ) : Set CovState :=
  {S | (block S D - 1).PosSemidef ∧ a ≤ GaussianMatrix.specNorm (block S D) ∧
    (block S D).det ≤ b}

open scoped Matrix.Norms.L2Operator in
lemma specNorm_cont (D : ℕ) : Continuous (fun M : Mat D => GaussianMatrix.specNorm M) := by
  unfold GaussianMatrix.specNorm
  exact continuous_norm

open scoped MatrixOrder in
lemma good_meas (D : ℕ) (a b : ℝ) : MeasurableSet (Good D a b) := by
  have h1 : IsClosed {M : Mat D | (M - 1).PosSemidef} := by
    have := (psd_closed D).preimage
      (continuous_id.sub continuous_const : Continuous fun M : Mat D => M - 1)
    convert this using 1
    ext M
    simp [Matrix.nonneg_iff_posSemidef]
  have h3 : Continuous (fun M : Mat D => M.det) := continuous_id.matrix_det
  have hC : IsClosed {M : Mat D | (M - 1).PosSemidef ∧ a ≤ GaussianMatrix.specNorm M ∧
      M.det ≤ b} :=
    h1.inter ((isClosed_le continuous_const (specNorm_cont D)).inter
      (isClosed_le h3 continuous_const))
  exact (measurable_block D) hC.measurableSet

/-! ### Deterministic matrix facts -/

lemma posDef_of {d : ℕ} {M : Mat d} (h : (M - 1).PosSemidef) : M.PosDef := by
  simpa using Matrix.PosDef.posSemidef_add h Matrix.PosDef.one

lemma one_le_norm {d : ℕ} {M : Mat (d+1)} (h : (M - 1).PosSemidef) :
    1 ≤ GaussianMatrix.specNorm M := by
  have h1 := dot_mulVec_le_specNorm M (Pi.single 0 1)
  have h2 := h.dotProduct_mulVec_nonneg (Pi.single 0 1)
  simp [Matrix.sub_mulVec] at h1 h2
  linarith

open scoped Matrix.Norms.L2Operator in
lemma det_le_norm_pow {d : ℕ} {M : Mat d} (h : M.PosSemidef) :
    M.det ≤ GaussianMatrix.specNorm M ^ d := by
  rw [h.1.det_eq_prod_eigenvalues]
  unfold GaussianMatrix.specNorm
  have : ‖M‖ ^ d = ∏ _i : Fin d, ‖M‖ := by simp
  rw [this]
  simp only [RCLike.ofReal_real_eq_id, id]
  refine Finset.prod_le_prod (fun i _ => h.eigenvalues_nonneg i) (fun i _ => ?_)
  set v := (h.1.eigenvectorBasis i).ofLp
  have hv := h.1.mulVec_eigenvectorBasis i
  have h1 := dot_mulVec_le_specNorm M v
  have hvv : v ⬝ᵥ v = 1 := by
    have hn : ‖h.1.eigenvectorBasis i‖ = 1 := (h.1.eigenvectorBasis).orthonormal.1 i
    have := real_inner_self_eq_norm_sq (h.1.eigenvectorBasis i)
    rw [hn, EuclideanSpace.inner_eq_star_dotProduct] at this
    simpa [v] using this
  rw [hv, dotProduct_smul, hvv] at h1
  simpa [GaussianMatrix.specNorm] using h1

open scoped MatrixOrder in
/-- `normal M` has no atom at the origin when `M` is positive definite. -/
lemma normal_zero {d : ℕ} {M : Mat (d+1)} (h : M.PosDef) : normal M {0} = 0 := by
  have hm : Measurable (fun y : Vec (d+1) => CFC.sqrt M *ᵥ y) :=
    (measurable_mulVec _).comp (measurable_const.prodMk measurable_id)
  rw [normal_eq_map, Measure.map_apply hm (measurableSet_singleton 0)]
  have hsub : (fun y => CFC.sqrt M *ᵥ y) ⁻¹' {0} ⊆ Set.univ.pi (fun _ => {0}) := by
    intro y hy
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hy
    have hM0 : (0:Mat (d+1)) ≤ M := (Matrix.nonneg_iff_posSemidef).2 h.posSemidef
    have hMy : M *ᵥ y = 0 := by
      rw [← CFC.sqrt_mul_sqrt_self M hM0, ← Matrix.mulVec_mulVec, hy, Matrix.mulVec_zero]
    have hy0 : y = 0 := by
      by_contra hne
      have := h.dotProduct_mulVec_pos hne
      simp [hMy] at this
    simp [hy0]
  refine measure_mono_null hsub ?_
  rw [Measure.pi_pi]
  exact Finset.prod_eq_zero (Finset.mem_univ 0)
    (gaussianReal_absolutelyContinuous 0 one_ne_zero (Real.volume_singleton))

/-! ### One step of the chain -/

lemma one_step (e : ℕ) (he : 3 ≤ e) (μ : Measure CovState) (g a b b' : ℝ) (hg0 : 0 ≤ g)
    (hg : g ≤ 3/2 - 2/((e+1:ℕ):ℝ)) (hb : 0 < b) (hb' : ((e+1:ℕ):ℝ) * b ≤ b') :
    ENNReal.ofReal ((0.16:ℝ)^(e+1) / (2*((e+1:ℕ):ℝ)*Real.sqrt b)) * μ (Good (e+1) a b) ≤
      (μ.bind (covStep (e+1))) (Good e (g*a) b') := by
  rw [Measure.bind_apply (good_meas _ _ _) (measurable_covStep _).aemeasurable]
  set c := (0.16:ℝ)^(e+1) / (2*((e+1:ℕ):ℝ)*Real.sqrt b)
  calc ENNReal.ofReal c * μ (Good (e+1) a b)
      = ∫⁻ _ in Good (e+1) a b, ENNReal.ofReal c ∂μ := by
        rw [setLIntegral_const, mul_comm]
    _ ≤ ∫⁻ S in Good (e+1) a b, covStep (e+1) S (Good e (g*a) b') ∂μ :=
        setLIntegral_mono' (good_meas _ _ _) fun S hS => ?_
    _ ≤ ∫⁻ S, covStep (e+1) S (Good e (g*a) b') ∂μ := setLIntegral_le_lintegral _ _
  obtain ⟨hI, ha, hdet⟩ := hS
  set M := block S (e+1)
  have hPD : M.PosDef := posDef_of hI
  have hdpos : 0 < M.det := hPD.det_pos
  have hm : Measurable (fun y : Vec (e+1) => embed (update M y)) := by
    have h1 : Measurable (fun y : Vec (e+1) => updateAt M y (pivot y)) :=
      (measurable_update e).comp (f := fun y : Vec (e+1) => (M, y))
        (measurable_const.prodMk measurable_id)
    exact (measurable_embed e).comp h1
  rw [covStep, Measure.map_apply hm (good_meas _ _ _)]
  have h52 := proposition_5_2 e he M hPD hI pivot pivot_max
  set E52 := {y : Vec (e+1) | (3/2 - 2/((e+1:ℕ):ℝ)) * GaussianMatrix.specNorm M ≤
    GaussianMatrix.specNorm (updateAt M y (pivot y))}
  have hcle : c ≤ prob (normal M) E52 := by
    refine le_trans ?_ h52
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    gcongr
  have hsub : E52 ⊆ ((fun y => embed (update M y)) ⁻¹' Good e (g*a) b') ∪ {0} := by
    intro y hy
    by_cases hy0 : y = 0
    · exact Or.inr hy0
    left
    simp only [Set.mem_preimage, Good, Set.mem_setOf_eq, block_embed]
    have hN : 0 ≤ GaussianMatrix.specNorm M := le_trans zero_le_one (one_le_norm hI)
    refine ⟨updateAt_sub_one M hI y (pivot y), ?_, ?_⟩
    · calc g * a ≤ g * GaussianMatrix.specNorm M := mul_le_mul_of_nonneg_left ha hg0
        _ ≤ (3/2 - 2/((e+1:ℕ):ℝ)) * GaussianMatrix.specNorm M :=
            mul_le_mul_of_nonneg_right hg hN
        _ ≤ _ := hy
    · have h416 := (proposition_4_16 e (by omega) M hPD y hy0 (pivot y) (pivot_max y)).2 hI
      calc (update M y).det ≤ ((e+1:ℕ):ℝ) * M.det := h416
        _ ≤ ((e+1:ℕ):ℝ) * b := by gcongr
        _ ≤ b' := hb'
  calc ENNReal.ofReal c ≤ normal M E52 := by
        rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]; exact hcle
    _ ≤ normal M ((fun y => embed (update M y)) ⁻¹' Good e (g*a) b') + normal M {0} :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ = _ := by rw [normal_zero hPD, add_zero]

/-! ### Start of the chain -/

/-- `N_d^{d+1}` is the lower determinant threshold of Proposition 4.15. -/
lemma initialNormBound_pow (n d : ℕ) :
    initialNormBound n d ^ (d+1) = (1 / Real.exp 1) *
      ((n:ℝ) / (Real.exp 1 * (((d+1:ℕ):ℝ) + 2*Real.log n)))^(d+1) := by
  unfold initialNormBound
  have he : Real.exp (1 + 1/((d:ℝ)+1)) ^ (d+1) = Real.exp 1 * Real.exp 1 ^ (d+1) := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    field_simp
    ring
  push_cast
  rw [div_pow, div_pow, mul_pow, mul_pow, he]
  field_simp

open scoped Matrix.Norms.L2Operator in
/-- A positive semidefinite `M` whose determinant beats the 4.15 threshold has `‖M‖ ≥ N_d`. -/
lemma initialNormBound_le (n d : ℕ) {M : Mat (d+1)} (hM : M.PosSemidef)
    (h : (1 / Real.exp 1) * ((n:ℝ) / (Real.exp 1 * (((d+1:ℕ):ℝ) + 2*Real.log n)))^(d+1) <
      M.det) : initialNormBound n d ≤ GaussianMatrix.specNorm M := by
  by_contra hlt
  push_neg at hlt
  have h0 : 0 ≤ GaussianMatrix.specNorm M := by
    unfold GaussianMatrix.specNorm; exact norm_nonneg _
  have := pow_lt_pow_left₀ hlt h0 (show d+1 ≠ 0 by omega)
  rw [initialNormBound_pow] at this
  linarith [det_le_norm_pow hM]

lemma base (n d : ℕ) (hd : 4 ≤ d) (hdn : d ≤ n-2) :
    ENNReal.ofReal (1/2 - 1/(n:ℝ)) ≤
      covLaw n (n-d-1) (Good (d+1) (max (initialNormBound n d) 1) (512 * (n:ℝ)^(3*(d+1)+3))) := by
  have h14 := (proposition_4_14 n (n-d) (by omega) (by omega)).2
  have h15 := (proposition_4_15 n (n-d) (by omega) (by omega)).2
  have h11 := proposition_4_11 n (n-d-1) (by omega)
  have e1 : n - (n-d-1) = d+1 := by omega
  have e2 : n - (n-d) + 1 = d+1 := by omega
  rw [e1] at h11 h14 h15
  rw [e2] at h14 h15
  set μ := covLaw n (n-d-1)
  set B := 512 * (n:ℝ)^(3*(d+1)+3)
  set thr := (1 / Real.exp 1) * ((n:ℝ) / (Real.exp 1 * (((d+1:ℕ):ℝ) + 2*Real.log n)))^(d+1)
  set G := Good (d+1) (max (initialNormBound n d) 1) B
  set A := {S : CovState | B ≤ (block S (d+1)).det}
  set L := {S : CovState | (block S (d+1)).det ≤ thr}
  set Z := {S : CovState | ¬ (block S (d+1) - 1).PosSemidef}
  have hZ : μ Z = 0 := by rw [ae_iff] at h11; exact h11
  have hcover : Set.univ ⊆ G ∪ A ∪ L ∪ Z := by
    intro S _
    by_cases hZ' : S ∈ Z
    · exact Or.inr hZ'
    by_cases hA' : S ∈ A
    · exact Or.inl (Or.inl (Or.inr hA'))
    by_cases hL' : S ∈ L
    · exact Or.inl (Or.inr hL')
    refine Or.inl (Or.inl (Or.inl ?_))
    simp only [Z, A, L, Set.mem_setOf_eq, not_not, not_le] at hZ' hA' hL'
    have hPSD : (block S (d+1)).PosSemidef := (posDef_of hZ').posSemidef
    exact ⟨hZ', max_le (initialNormBound_le n d hPSD hL') (one_le_norm hZ'), hA'.le⟩
  have h1 : (1:ℝ≥0∞) ≤ μ G + μ A + μ L + μ Z := by
    calc (1:ℝ≥0∞) = μ Set.univ := measure_univ.symm
      _ ≤ μ (G ∪ A ∪ L ∪ Z) := measure_mono hcover
      _ ≤ _ := (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
          (add_le_add (measure_union_le _ _) le_rfl)) le_rfl)
  rw [hZ, add_zero] at h1
  have h2 := ENNReal.toReal_mono (by simp [measure_ne_top]) h1
  rw [ENNReal.toReal_add (by simp [measure_ne_top]) (measure_ne_top _ _),
    ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at h2
  rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
  unfold prob at h14 h15
  simp only [ENNReal.toReal_one] at h2
  linarith

/-! ### The chain -/

/-- The closed-form lower bound after `k` successful steps, without the factor `1/2 - 1/n`. -/
def F (n d k : ℕ) : ℝ :=
  Real.rpow (0.16:ℝ) ((k:ℝ)*(2*(d:ℝ)+3-k)/2) /
    ((32*Real.sqrt 2)^k * Real.rpow ((d:ℝ)+1) ((k:ℝ)*((k:ℝ)+3)/4) *
      Real.rpow (n:ℝ) ((k:ℝ)*(3*(d:ℝ)+6)/2))

lemma F_zero (n d : ℕ) : F n d 0 = 1 := by
  simp [F]

lemma F_nonneg (n d k : ℕ) : 0 ≤ F n d k := by
  simp only [F, Real.rpow_eq_pow]
  positivity

/-- One more step costs at most the success probability of Proposition 5.2. -/
lemma F_succ (n d k : ℕ) (hk : k ≤ d) (hn : 1 ≤ n) :
    F n d (k+1) ≤ F n d k * ((0.16:ℝ)^(d-k+1) /
      (2*((d-k+1:ℕ):ℝ)*Real.sqrt (512 * (n:ℝ)^(3*(d+1)+3) * ((d:ℝ)+1)^k))) := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  have hD : (0:ℝ) < (d:ℝ)+1 := by positivity
  have e1 : Real.rpow (0.16:ℝ) (((k+1:ℕ):ℝ)*(2*(d:ℝ)+3-((k+1:ℕ):ℝ))/2) =
      Real.rpow (0.16:ℝ) ((k:ℝ)*(2*(d:ℝ)+3-k)/2) * Real.rpow (0.16:ℝ) ((d:ℝ)+1-k) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add (by norm_num)]
    congr 1; push_cast; ring
  have e2 : Real.rpow ((d:ℝ)+1) (((k+1:ℕ):ℝ)*(((k+1:ℕ):ℝ)+3)/4) =
      Real.rpow ((d:ℝ)+1) ((k:ℝ)*((k:ℝ)+3)/4) * (Real.rpow ((d:ℝ)+1) ((k:ℝ)/2) * ((d:ℝ)+1)) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add_one hD.ne', ← Real.rpow_add hD]
    congr 1; push_cast; ring
  have e3 : Real.rpow (n:ℝ) (((k+1:ℕ):ℝ)*(3*(d:ℝ)+6)/2) =
      Real.rpow (n:ℝ) ((k:ℝ)*(3*(d:ℝ)+6)/2) * Real.rpow (n:ℝ) ((3*(d:ℝ)+6)/2) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add hn0]
    congr 1; push_cast; ring
  have hnum : (0.16:ℝ)^(d-k+1) = Real.rpow (0.16:ℝ) ((d:ℝ)+1-k) := by
    rw [Real.rpow_eq_pow, ← Real.rpow_natCast]
    congr 1; push_cast [Nat.cast_sub hk]; ring
  have s1 : Real.sqrt ((n:ℝ)^(3*(d+1)+3)) = Real.rpow (n:ℝ) ((3*(d:ℝ)+6)/2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_eq_pow, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    congr 1; push_cast; ring
  have s2 : Real.sqrt (((d:ℝ)+1)^k) = Real.rpow ((d:ℝ)+1) ((k:ℝ)/2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_eq_pow, ← Real.rpow_natCast, ← Real.rpow_mul hD.le]
    congr 1; ring
  have s3 : Real.sqrt 512 = 16 * Real.sqrt 2 := by
    rw [show (512:ℝ) = 16^2 * 2 by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  have hsq : Real.sqrt (512 * (n:ℝ)^(3*(d+1)+3) * ((d:ℝ)+1)^k) =
      16 * Real.sqrt 2 * Real.rpow (n:ℝ) ((3*(d:ℝ)+6)/2) * Real.rpow ((d:ℝ)+1) ((k:ℝ)/2) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num), s1, s2, s3]
  unfold F
  rw [e1, e2, e3, hnum, hsq, pow_succ]
  set a := Real.rpow (0.16:ℝ) ((k:ℝ)*(2*(d:ℝ)+3-k)/2)
  set a' := Real.rpow (0.16:ℝ) ((d:ℝ)+1-k)
  set b := Real.rpow ((d:ℝ)+1) ((k:ℝ)*((k:ℝ)+3)/4)
  set b' := Real.rpow ((d:ℝ)+1) ((k:ℝ)/2)
  set c := Real.rpow (n:ℝ) ((k:ℝ)*(3*(d:ℝ)+6)/2)
  set c' := Real.rpow (n:ℝ) ((3*(d:ℝ)+6)/2)
  have ha : 0 ≤ a := by simp only [a, Real.rpow_eq_pow]; positivity
  have ha' : 0 ≤ a' := by simp only [a', Real.rpow_eq_pow]; positivity
  have hb : 0 < b := by simp only [b, Real.rpow_eq_pow]; positivity
  have hb' : 0 < b' := by simp only [b', Real.rpow_eq_pow]; positivity
  have hc : 0 < c := by simp only [c, Real.rpow_eq_pow]; positivity
  have hc' : 0 < c' := by simp only [c', Real.rpow_eq_pow]; positivity
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hq : 0 < (32 * Real.sqrt 2)^k := by positivity
  have hdk : (0:ℝ) < ((d-k+1:ℕ):ℝ) := by positivity
  have hdk' : ((d-k+1:ℕ):ℝ) ≤ (d:ℝ)+1 := by exact_mod_cast (show d-k+1 ≤ d+1 by omega)
  rw [show a * a' / ((32 * Real.sqrt 2)^k * (32 * Real.sqrt 2) * (b * (b' * ((d:ℝ)+1))) * (c * c')) =
      a / ((32 * Real.sqrt 2)^k * b * c) * (a' / (32 * Real.sqrt 2 * b' * ((d:ℝ)+1) * c')) by
    field_simp]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply div_le_div_of_nonneg_left ha' (by positivity)
  have : 0 < Real.sqrt 2 * c' * b' := by positivity
  nlinarith

lemma chain (n T d : ℕ) (hT : 4 ≤ T) (hTd : T ≤ d) (hdn : d ≤ n-2) :
    ∀ k, k ≤ d - T →
      ENNReal.ofReal ((1/2 - 1/(n:ℝ)) * F n d k) ≤
        covLaw n (n-d-1+k) (Good (d+1-k) ((3/2 - 2/(T:ℝ))^k * max (initialNormBound n d) 1)
          (512 * (n:ℝ)^(3*(d+1)+3) * ((d:ℝ)+1)^k)) := by
  intro k
  induction k with
  | zero =>
    intro _
    simpa [F_zero] using base n d (by omega) hdn
  | succ k ih =>
    intro hk
    have ih' := ih (by omega)
    obtain ⟨e, he⟩ : ∃ e, d - k = e := ⟨_, rfl⟩
    have hdim : d+1-k = e+1 := by omega
    have hdim2 : d+1-(k+1) = e := by omega
    have ht : n - (n-d-1+k) = e+1 := by omega
    rw [hdim] at ih'
    rw [hdim2, show n-d-1+(k+1) = (n-d-1+k)+1 from rfl]
    simp only [covLaw]
    rw [ht]
    have hn : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hB : 0 < 512 * (n:ℝ)^(3*(d+1)+3) * ((d:ℝ)+1)^k := by positivity
    have hg0 : (0:ℝ) ≤ 3/2 - 2/(T:ℝ) := by
      have : (4:ℝ) ≤ T := by exact_mod_cast hT
      rw [sub_nonneg, div_le_iff₀ (by linarith)]; linarith
    have hg : 3/2 - 2/(T:ℝ) ≤ 3/2 - 2/((e+1:ℕ):ℝ) := by
      have : (T:ℝ) ≤ ((e+1:ℕ):ℝ) := by exact_mod_cast (show T ≤ e+1 by omega)
      have : (4:ℝ) ≤ T := by exact_mod_cast hT
      gcongr
    have hstep := one_step e (by omega) (covLaw n (n-d-1+k)) (3/2 - 2/(T:ℝ))
      ((3/2 - 2/(T:ℝ))^k * max (initialNormBound n d) 1)
      (512 * (n:ℝ)^(3*(d+1)+3) * ((d:ℝ)+1)^k)
      (512 * (n:ℝ)^(3*(d+1)+3) * ((d:ℝ)+1)^(k+1)) hg0 hg hB (by
        have : ((e+1:ℕ):ℝ) ≤ (d:ℝ)+1 := by exact_mod_cast (show e+1 ≤ d+1 by omega)
        calc ((e+1:ℕ):ℝ) * (512 * (n:ℝ)^(3*(d+1)+3) * ((d:ℝ)+1)^k)
            ≤ ((d:ℝ)+1) * (512 * (n:ℝ)^(3*(d+1)+3) * ((d:ℝ)+1)^k) :=
              mul_le_mul_of_nonneg_right this hB.le
          _ = _ := by ring)
    rw [show (3/2 - 2/(T:ℝ))^(k+1) * max (initialNormBound n d) 1 =
      (3/2 - 2/(T:ℝ)) * ((3/2 - 2/(T:ℝ))^k * max (initialNormBound n d) 1) by ring]
    refine le_trans ?_ hstep
    have hp0 : (0:ℝ) ≤ 1/2 - 1/(n:ℝ) := by
      have : (6:ℝ) ≤ n := by exact_mod_cast (show 6 ≤ n by omega)
      have : 1/(n:ℝ) ≤ 1/2 := by
        rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
      linarith
    have hFs := F_succ n d k (by omega) (by omega)
    rw [he] at hFs
    calc ENNReal.ofReal ((1/2 - 1/(n:ℝ)) * F n d (k+1))
        ≤ ENNReal.ofReal ((0.16:ℝ)^(e+1) / (2*((e+1:ℕ):ℝ)*
            Real.sqrt (512 * (n:ℝ)^(3*(d+1)+3) * ((d:ℝ)+1)^k)) *
            ((1/2 - 1/(n:ℝ)) * F n d k)) := by
          apply ENNReal.ofReal_le_ofReal
          calc (1/2 - 1/(n:ℝ)) * F n d (k+1) ≤ (1/2 - 1/(n:ℝ)) * (F n d k * ((0.16:ℝ)^(e+1) /
              (2*((e+1:ℕ):ℝ)*Real.sqrt (512 * (n:ℝ)^(3*(d+1)+3) * ((d:ℝ)+1)^k)))) :=
                mul_le_mul_of_nonneg_left hFs hp0
            _ = _ := by ring
      _ ≤ _ := by
          rw [ENNReal.ofReal_mul (by positivity)]
          gcongr

lemma statement_eq (n T d : ℕ) (hTd : T ≤ d) :
    (1/2 - 1/(n:ℝ)) *
      Real.rpow (0.16:ℝ) (((d-T:ℕ):ℝ)*(((d-T:ℕ):ℝ)+2*T+3)/2) /
      ((32*Real.sqrt 2)^(d-T) * Real.rpow (((d-T:ℕ):ℝ)+T+1) (((d-T:ℕ):ℝ)*(((d-T:ℕ):ℝ)+3)/4) *
        Real.rpow (n:ℝ) (3*((d-T:ℕ):ℝ)*(((d-T:ℕ):ℝ)+T+2)/2)) =
    (1/2 - 1/(n:ℝ)) * F n d (d-T) := by
  obtain ⟨r, rfl⟩ : ∃ r, d = r + T := ⟨d - T, by omega⟩
  rw [show r + T - T = r by omega]
  unfold F
  push_cast
  ring_nf

end GEPP53

open GEPPGrowth.Main in
theorem solution (n T d : ℕ) (hT : 4 ≤ T) (hTd : T ≤ d) (hdn : d ≤ n-2) :
    let r := d-T
    (1/2 - 1/(n:ℝ)) *
      Real.rpow (0.16:ℝ) ((r:ℝ)*((r:ℝ)+2*T+3)/2) /
      ((32*Real.sqrt 2)^r * Real.rpow ((r:ℝ)+T+1) ((r:ℝ)*((r:ℝ)+3)/4) *
        Real.rpow (n:ℝ) (3*(r:ℝ)*((r:ℝ)+T+2)/2)) ≤
      prob (covLaw n (n-d+r-1)) {S |
        (3/2 - 2/(T:ℝ))^r ≤
          GaussianMatrix.specNorm (block S (n-(n-d+r-1))) / max (initialNormBound n d) 1} := by
  intro r
  rw [GEPP53.statement_eq n T d hTd]
  have hc := GEPP53.chain n T d hT hTd hdn r le_rfl
  have h1 : n-d+r-1 = n-d-1+r := by omega
  have h2 : n-(n-d-1+r) = d+1-r := by omega
  rw [h1, h2]
  unfold prob
  rw [← ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
  refine hc.trans (measure_mono fun S hS => ?_)
  obtain ⟨-, hS, -⟩ := hS
  show _ ≤ GaussianMatrix.specNorm _ / _
  rw [le_div_iff₀ (lt_of_lt_of_le one_pos (le_max_right _ _))]
  exact hS
