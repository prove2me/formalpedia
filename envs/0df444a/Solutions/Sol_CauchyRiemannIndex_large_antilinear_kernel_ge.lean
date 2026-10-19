-- Prove2me | solution 1 for CauchyRiemannIndex.large_antilinear_kernel_ge
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-17T14:05:15.572435+00:00
-- url     : https://prove2.me/submissions/49e97a1a-1dbf-4476-9f29-c73b8a53a02a

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Theorems.Thm_CauchyRiemannIndex_global_estimate
import Theorems.Thm_CauchyRiemannIndex_compact_restriction
import Theorems.Thm_CauchyRiemannIndex_finiteDimensional_ker_isClosed_range_of_estimate
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Theorems.Thm_CauchyRiemannIndex_exists_solution_of_adjoint_estimate
import Theorems.Thm_CauchyRiemannIndex_large_antilinear_adjoint_estimate
import Theorems.Thm_CauchyRiemannIndex_linearIndependent_sub_of_orthogonal



/-!
# Cutoffs and the zeros of `β`
-/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology Metric
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

/-- The tent `τ_a(v) = max 0 (min 1 (2 - 2|v|/a))`. -/
def lapTau (a v : ℝ) : ℝ := max 0 (min 1 (2 - 2 * |v| / a))

lemma lapTau_continuous (a : ℝ) : Continuous (lapTau a) := by
  unfold lapTau; fun_prop

lemma lapTau_nonneg (a v : ℝ) : 0 ≤ lapTau a v := le_max_left _ _

lemma lapTau_le_one (a v : ℝ) : lapTau a v ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

lemma lapTau_eq_one {a v : ℝ} (ha : 0 < a) (hv : |v| ≤ a / 2) : lapTau a v = 1 := by
  unfold lapTau
  have : 1 ≤ 2 - 2 * |v| / a := by
    rw [le_sub_comm, div_le_iff₀ ha]; linarith
  rw [min_eq_left this, max_eq_right zero_le_one]

lemma lapTau_eq_zero {a v : ℝ} (ha : 0 < a) (hv : a ≤ |v|) : lapTau a v = 0 := by
  unfold lapTau
  have : 2 - 2 * |v| / a ≤ 0 := by
    rw [sub_nonpos, le_div_iff₀ ha]; linarith
  exact max_eq_left ((min_le_right _ _).trans this)

/-- The bump `ψ`, `= 1` on `[-a/2, a/2]`, supported in `(-3a/4, 3a/4)`. -/
def lapPsi {a : ℝ} (ha : 0 < a) : ContDiffBump (0 : ℝ) :=
  ⟨a / 2, 3 * a / 4, by positivity, by linarith⟩

/-- `k(u) = u ψ(u)`. -/
def lapK {a : ℝ} (ha : 0 < a) (u : ℝ) : ℝ := u * lapPsi ha u

/-- `k'(u) = ψ(u) + u ψ'(u)`. -/
def lapKd {a : ℝ} (ha : 0 < a) (u : ℝ) : ℝ := lapPsi ha u + u * deriv (lapPsi ha) u

lemma lapPsi_diff {a : ℝ} (ha : 0 < a) : Differentiable ℝ (lapPsi ha) :=
  (lapPsi ha).contDiff.differentiable (n := 1) one_ne_zero

lemma lapK_hasDerivAt {a : ℝ} (ha : 0 < a) (u : ℝ) : HasDerivAt (lapK ha) (lapKd ha u) u := by
  have h := (hasDerivAt_id u).mul ((lapPsi_diff ha) u).hasDerivAt
  unfold lapK lapKd
  refine h.congr_deriv ?_
  simp

lemma lapK_continuous {a : ℝ} (ha : 0 < a) : Continuous (lapK ha) :=
  continuous_id.mul ((lapPsi ha).contDiff (n := 0)).continuous

lemma lapKd_continuous {a : ℝ} (ha : 0 < a) : Continuous (lapKd ha) :=
  ((lapPsi ha).contDiff (n := 0)).continuous.add
    (continuous_id.mul (((lapPsi ha).contDiff (n := 1)).continuous_deriv le_rfl))

lemma lapPsi_eq_zero {a : ℝ} (ha : 0 < a) {u : ℝ} (hu : 3 * a / 4 ≤ |u|) : lapPsi ha u = 0 :=
  (lapPsi ha).zero_of_le_dist (by rw [Real.dist_eq, sub_zero]; exact hu)

lemma lapPsi_deriv_eq_zero {a : ℝ} (ha : 0 < a) {u : ℝ} (hu : 3 * a / 4 < |u|) :
    deriv (lapPsi ha) u = 0 := by
  have hU : IsOpen {u : ℝ | 3 * a / 4 < |u|} := isOpen_lt continuous_const continuous_abs
  have hev : (lapPsi ha : ℝ → ℝ) =ᶠ[𝓝 u] fun _ => 0 :=
    Filter.eventually_of_mem (hU.mem_nhds hu) fun v hv => lapPsi_eq_zero ha (le_of_lt hv)
  rw [hev.deriv_eq]; simp

lemma lapPsi_eq_one {a : ℝ} (ha : 0 < a) {u : ℝ} (hu : |u| ≤ a / 2) : lapPsi ha u = 1 :=
  (lapPsi ha).one_of_mem_closedBall (by
    rw [mem_closedBall, Real.dist_eq, sub_zero]; exact hu)

lemma lapPsi_deriv_eq_zero' {a : ℝ} (ha : 0 < a) {u : ℝ} (hu : |u| < a / 2) :
    deriv (lapPsi ha) u = 0 := by
  have hU : IsOpen {u : ℝ | |u| < a / 2} := isOpen_lt continuous_abs continuous_const
  have hev : (lapPsi ha : ℝ → ℝ) =ᶠ[𝓝 u] fun _ => 1 :=
    Filter.eventually_of_mem (hU.mem_nhds hu) fun v hv => lapPsi_eq_one ha (le_of_lt hv)
  rw [hev.deriv_eq]; simp

lemma lapK_eq_zero {a : ℝ} (ha : 0 < a) {u : ℝ} (hu : a ≤ |u|) : lapK ha u = 0 := by
  unfold lapK; rw [lapPsi_eq_zero ha (by linarith), mul_zero]

lemma lapKd_eq_zero {a : ℝ} (ha : 0 < a) {u : ℝ} (hu : a ≤ |u|) : lapKd ha u = 0 := by
  unfold lapKd
  rw [lapPsi_eq_zero ha (by linarith), lapPsi_deriv_eq_zero ha (by linarith)]; ring

lemma lapKd_eq_one {a : ℝ} (ha : 0 < a) {u : ℝ} (hu : |u| < a / 2) : lapKd ha u = 1 := by
  unfold lapKd
  rw [lapPsi_eq_one ha hu.le, lapPsi_deriv_eq_zero' ha hu]; ring

lemma lapK_abs_le {a : ℝ} (ha : 0 < a) (u : ℝ) : |lapK ha u| ≤ |u| := by
  unfold lapK
  rw [abs_mul]
  have h0 := (lapPsi ha).nonneg (x := u)
  have h1 := (lapPsi ha).le_one (x := u)
  rw [abs_of_nonneg h0]
  nlinarith [abs_nonneg u]

lemma lapKd_bounded {a : ℝ} (ha : 0 < a) : ∃ B : ℝ, 0 ≤ B ∧ ∀ u, |lapKd ha u| ≤ B := by
  obtain ⟨B, hB⟩ := (lapKd_continuous ha).bounded_above_of_compact_support
    (HasCompactSupport.intro (isCompact_Icc (a := -a) (b := a)) fun u hu => by
      refine lapKd_eq_zero ha ?_
      by_contra h
      exact hu (abs_le.1 (le_of_lt (not_le.1 h)))
  )
  exact ⟨max B 0, le_max_right _ _, fun u => (hB u).trans (le_max_left _ _)⟩

/-! ### The zeros of `β` -/

section zeros

variable {β : ℝ × ℝ → ℂ} {Z : Finset (ℝ × ℝ)} {r : ℝ}

lemma lap_per_int (hβper : ∀ s t, β (s, t + 1) = β (s, t)) (s t : ℝ) (m : ℤ) :
    β (s, t + m) = β (s, t) := by
  have hp : Function.Periodic (fun t => β (s, t)) 1 := fun t => hβper s t
  have := hp.int_mul m t
  simpa [mul_one, add_comm] using this

/-- The normal form near every translate of a zero. -/
lemma lap_local (hβper : ∀ s t, β (s, t + 1) = β (s, t))
    (hplusZ : ∀ ζ ∈ Z, ∀ z : ℂ, ‖z‖ < r → β (ζ.1 + z.re, ζ.2 + z.im) = z)
    {ζ : ℝ × ℝ} (hζ : ζ ∈ Z) (m : ℤ) {u v : ℝ} (huv : ‖(⟨u, v⟩ : ℂ)‖ < r) :
    β (ζ.1 + u, ζ.2 + m + v) = ⟨u, v⟩ := by
  have := hplusZ ζ hζ ⟨u, v⟩ huv
  have e : ζ.2 + m + v = ζ.2 + v + m := by ring
  rw [e, lap_per_int hβper]
  exact this

lemma lap_norm_lt {u v a : ℝ} (hu : |u| < a) (hv : |v| < a) : ‖(⟨u, v⟩ : ℂ)‖ < 2 * a := by
  have := Complex.norm_le_abs_re_add_abs_im ⟨u, v⟩
  simp only at this
  linarith

/-- Distinct translates of zeros are at distance `≥ r` (in the box norm, `≥ r / 2`). -/
lemma lap_sep (hβper : ∀ s t, β (s, t + 1) = β (s, t))
    (hZ : ∀ ζ ∈ Z, 0 ≤ ζ.2 ∧ ζ.2 < 1)
    (hzero : ∀ x : ℝ × ℝ, β x = 0 ↔ ∃ ζ ∈ Z, ∃ m : ℤ, x = (ζ.1, ζ.2 + m))
    (hplusZ : ∀ ζ ∈ Z, ∀ z : ℂ, ‖z‖ < r → β (ζ.1 + z.re, ζ.2 + z.im) = z)
    {ζ ζ' : ℝ × ℝ} (hζ : ζ ∈ Z) (hζ' : ζ' ∈ Z) {m m' : ℤ}
    (h1 : |ζ'.1 - ζ.1| < r / 2) (h2 : |ζ'.2 + m' - (ζ.2 + m)| < r / 2) :
    ζ = ζ' ∧ m = m' := by
  have hn := lap_norm_lt h1 h2
  rw [show 2 * (r / 2) = r by ring] at hn
  have hloc := lap_local hβper hplusZ hζ m hn
  have e : (ζ.1 + (ζ'.1 - ζ.1), ζ.2 + m + (ζ'.2 + m' - (ζ.2 + m))) = (ζ'.1, ζ'.2 + m') := by
    ext <;> simp
  rw [e, (hzero _).2 ⟨ζ', hζ', m', rfl⟩] at hloc
  have hre := congrArg Complex.re hloc
  have him := congrArg Complex.im hloc
  simp only [Complex.zero_re, Complex.zero_im] at hre him
  have hmm : (m : ℝ) = m' := by
    have hd : ((m' - m : ℤ) : ℝ) = ζ.2 - ζ'.2 := by push_cast; linarith
    have hlt : |((m' - m : ℤ) : ℝ)| < 1 := by
      rw [hd, abs_lt]
      constructor <;> linarith [hZ ζ hζ, hZ ζ' hζ']
    have : m' - m = 0 := by
      rw [← Int.cast_abs] at hlt
      have : |m' - m| < 1 := by exact_mod_cast hlt
      exact Int.abs_lt_one_iff.1 this
    have : (m : ℝ) = m' := by exact_mod_cast (by omega : m = m')
    exact this
  have hm : m = m' := by exact_mod_cast hmm
  refine ⟨Prod.ext (by linarith) (by rw [hmm] at him; linarith), hm⟩

end zeros

end

end CauchyRiemannIndex

/-!
# Pointwise algebra of `antilinearMat β` and `J₀` on `ℝ² = ℂ`
-/

namespace CauchyRiemannIndex

open Matrix
open scoped RealInnerProductSpace

noncomputable section


lemma lap_inner (v w : Vec 1) : ⟪v, w⟫ = v (Sum.inl 0 : Fin 1 ⊕ Fin 1) * w (Sum.inl 0 : Fin 1 ⊕ Fin 1) + v (Sum.inr 0 : Fin 1 ⊕ Fin 1) * w (Sum.inr 0 : Fin 1 ⊕ Fin 1) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, Fintype.sum_sum_type, mul_comm]

lemma lap_norm_sq (v : Vec 1) : ‖v‖ ^ 2 = v (Sum.inl 0 : Fin 1 ⊕ Fin 1) ^ 2 + v (Sum.inr 0 : Fin 1 ⊕ Fin 1) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, lap_inner]; ring

lemma lap_alm_1 (b : ℂ) (v : Vec 1) :
    Matrix.toEuclideanLin (antilinearMat b) v (Sum.inl 0 : Fin 1 ⊕ Fin 1) = b.re * v (Sum.inl 0 : Fin 1 ⊕ Fin 1) + b.im * v (Sum.inr 0 : Fin 1 ⊕ Fin 1) := by
  simp [Matrix.toEuclideanLin_apply, antilinearMat, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type]

lemma lap_alm_2 (b : ℂ) (v : Vec 1) :
    Matrix.toEuclideanLin (antilinearMat b) v (Sum.inr 0 : Fin 1 ⊕ Fin 1) = b.im * v (Sum.inl 0 : Fin 1 ⊕ Fin 1) - b.re * v (Sum.inr 0 : Fin 1 ⊕ Fin 1) := by
  simp [Matrix.toEuclideanLin_apply, antilinearMat, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type]
  ring

lemma lap_J_1 (v : Vec 1) : Matrix.toEuclideanLin (J₀ 1) v (Sum.inl 0 : Fin 1 ⊕ Fin 1) = -v (Sum.inr 0 : Fin 1 ⊕ Fin 1) := by
  simp [Matrix.toEuclideanLin_apply, Matrix.J, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]

lemma lap_J_2 (v : Vec 1) : Matrix.toEuclideanLin (J₀ 1) v (Sum.inr 0 : Fin 1 ⊕ Fin 1) = v (Sum.inl 0 : Fin 1 ⊕ Fin 1) := by
  simp [Matrix.toEuclideanLin_apply, Matrix.J, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]

lemma lap_alm_transpose (b : ℂ) : (antilinearMat b)ᵀ = antilinearMat b := by
  simp only [antilinearMat, Matrix.fromBlocks_transpose]
  congr 1 <;> (ext; simp)

lemma lap_alm_add (b c : ℂ) : antilinearMat (b + c) = antilinearMat b + antilinearMat c := by
  simp only [antilinearMat, Complex.add_re, Complex.add_im, neg_add, Matrix.fromBlocks_add]
  congr 1 <;> (ext; simp)

lemma lap_alm_smul (c : ℝ) (b : ℂ) : antilinearMat ((c : ℂ) * b) = c • antilinearMat b := by
  simp only [antilinearMat, Complex.re_ofReal_mul, Complex.im_ofReal_mul, Matrix.fromBlocks_smul]
  congr 1 <;> (ext; simp)

lemma lap_inner_alm_sym (b : ℂ) (v w : Vec 1) :
    ⟪Matrix.toEuclideanLin (antilinearMat b) v, w⟫ =
      ⟪v, Matrix.toEuclideanLin (antilinearMat b) w⟫ := by
  rw [lap_inner, lap_inner, lap_alm_1, lap_alm_2, lap_alm_1, lap_alm_2]; ring

lemma lap_norm_alm_sq (b : ℂ) (v : Vec 1) :
    ‖Matrix.toEuclideanLin (antilinearMat b) v‖ ^ 2 = ‖b‖ ^ 2 * ‖v‖ ^ 2 := by
  rw [lap_norm_sq, lap_norm_sq, lap_alm_1, lap_alm_2, Complex.sq_norm, Complex.normSq_apply]
  ring

lemma lap_inner_J_alm (b : ℂ) (a w : Vec 1) :
    ⟪Matrix.toEuclideanLin (J₀ 1) a, Matrix.toEuclideanLin (antilinearMat b) w⟫ =
      -⟪a, Matrix.toEuclideanLin (antilinearMat (Complex.I * b)) w⟫ := by
  rw [lap_inner, lap_inner, lap_J_1, lap_J_2, lap_alm_1, lap_alm_2, lap_alm_1, lap_alm_2]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  ring

lemma lap_inner_alm_self_le (b : ℂ) (v : Vec 1) :
    |⟪v, Matrix.toEuclideanLin (antilinearMat b) v⟫| ≤ ‖b‖ * ‖v‖ ^ 2 := by
  calc |⟪v, Matrix.toEuclideanLin (antilinearMat b) v⟫|
      ≤ ‖v‖ * ‖Matrix.toEuclideanLin (antilinearMat b) v‖ := abs_real_inner_le_norm _ _
    _ = ‖b‖ * ‖v‖ ^ 2 := by
      have h := lap_norm_alm_sq b v
      have h' : ‖Matrix.toEuclideanLin (antilinearMat b) v‖ = ‖b‖ * ‖v‖ := by
        rw [← Real.sqrt_sq (norm_nonneg _), h, ← mul_pow, Real.sqrt_sq (by positivity)]
      rw [h']; ring

lemma lap_norm_J (v : Vec 1) : ‖Matrix.toEuclideanLin (J₀ 1) v‖ = ‖v‖ := by
  have h : ‖Matrix.toEuclideanLin (J₀ 1) v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [lap_norm_sq, lap_norm_sq, lap_J_1, lap_J_2]; ring
  rw [← Real.sqrt_sq (norm_nonneg (Matrix.toEuclideanLin (J₀ 1) v)), h,
    Real.sqrt_sq (norm_nonneg _)]

end

end CauchyRiemannIndex

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff

noncomputable section

variable {n : ℕ}

/-- Matrices as continuous linear maps of `ℝ²ⁿ`, continuously in the matrix. -/
def matCLM (n : ℕ) : Mat n →ₗ[ℝ] (Vec n →L[ℝ] Vec n) :=
  (LinearMap.toContinuousLinearMap : (Vec n →ₗ[ℝ] Vec n) ≃ₗ[ℝ] (Vec n →L[ℝ] Vec n)).toLinearMap ∘ₗ
    (Matrix.toEuclideanLin : Mat n ≃ₗ[ℝ] (Vec n →ₗ[ℝ] Vec n)).toLinearMap

lemma matCLM_apply (A : Mat n) (v : Vec n) : matCLM n A v = Matrix.toEuclideanLin A v := rfl

lemma continuous_matCLM : Continuous (matCLM n) := LinearMap.continuous_of_finiteDimensional _

/-- A uniform operator bound for a continuous `1`-periodic matrix loop. -/
lemma exists_bound_loop (Sinf : ℝ → Mat n) (hc : Continuous Sinf) (hper : Function.Periodic Sinf 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t (v : Vec n), ‖Matrix.toEuclideanLin (Sinf t) v‖ ≤ M * ‖v‖ := by
  have hg : Continuous fun t => matCLM n (Sinf t) := continuous_matCLM.comp hc
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hg.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t v => ?_⟩
  obtain ⟨y, hy, hty⟩ := hper.exists_mem_Ico₀ one_pos t
  rw [← matCLM_apply, hty]
  calc ‖matCLM n (Sinf y) v‖ ≤ ‖matCLM n (Sinf y)‖ * ‖v‖ := (matCLM n (Sinf y)).le_opNorm v
    _ ≤ max C 0 * ‖v‖ := by
      gcongr
      exact (hC y (Set.Ico_subset_Icc_self hy)).trans (le_max_left _ _)

lemma exists_bound_mat (A : Mat n) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (v : Vec n), ‖Matrix.toEuclideanLin A v‖ ≤ M * ‖v‖ :=
  ⟨‖matCLM n A‖, norm_nonneg _, fun v => (matCLM n A).le_opNorm v⟩

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A continuous map on `ℝ × ℝ` vanishing for large `|s|` is in `L^p` of the strip. -/
lemma memLp_of_vanish {E : Type*} [NormedAddCommGroup E] (g : ℝ × ℝ → E) (hg : Continuous g)
    (R : ℝ) (hR : ∀ s t, R < |s| → g (s, t) = 0) : MemLp g p cylMeasure := by
  set K : Set (ℝ × ℝ) := Set.Icc (-R) R ×ˢ Set.Icc 0 1 with hK
  have hKc : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKm : MeasurableSet K := measurableSet_Icc.prod measurableSet_Icc
  have hae : K.indicator g =ᵐ[cylMeasure] g := by
    unfold cylMeasure
    refine ae_restrict_of_forall_mem (MeasurableSet.univ.prod measurableSet_Ico) ?_
    rintro ⟨s, t⟩ ⟨-, ht⟩
    by_cases hx : (s, t) ∈ K
    · simp [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      have : R < |s| := by
        by_contra h
        push_neg at h
        exact hx ⟨abs_le.1 h, Set.Ico_subset_Icc_self ht⟩
      exact (hR s t this).symm
  refine (memLp_congr_ae hae).1 ((memLp_indicator_iff_restrict hKm).2 ?_)
  haveI : IsFiniteMeasure (cylMeasure.restrict K) := by
    refine isFiniteMeasure_restrict.2 (ne_of_lt (lt_of_le_of_lt ?_ (hKc.measure_lt_top (μ := (volume : Measure (ℝ × ℝ))))))
    exact Measure.le_iff'.1 Measure.restrict_le_self K
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hg.continuousOn
  exact MemLp.of_bound hg.aestronglyMeasurable C (ae_restrict_of_forall_mem hKm hC)

lemma partialS_eq_zero {u : ℝ × ℝ → Vec n} (R : ℝ) (hR : ∀ s t, R < |s| → u (s, t) = 0)
    {s t : ℝ} (hs : R < |s|) : partialS u (s, t) = 0 := by
  have hU : IsOpen {x : ℝ × ℝ | R < |x.1|} := isOpen_lt continuous_const (continuous_abs.comp continuous_fst)
  have hev : u =ᶠ[𝓝 (s, t)] fun _ => 0 :=
    Filter.eventually_of_mem (hU.mem_nhds hs) fun x hx => hR x.1 x.2 hx
  simp [partialS, hev.fderiv_eq]

lemma partialT_eq_zero {u : ℝ × ℝ → Vec n} (R : ℝ) (hR : ∀ s t, R < |s| → u (s, t) = 0)
    {s t : ℝ} (hs : R < |s|) : partialT u (s, t) = 0 := by
  have hU : IsOpen {x : ℝ × ℝ | R < |x.1|} := isOpen_lt continuous_const (continuous_abs.comp continuous_fst)
  have hev : u =ᶠ[𝓝 (s, t)] fun _ => 0 :=
    Filter.eventually_of_mem (hU.mem_nhds hs) fun x hx => hR x.1 x.2 hx
  simp [partialT, hev.fderiv_eq]

lemma IsTestSection.continuous {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) : Continuous u :=
  hu.1.continuous

lemma IsTestSection.continuous_partialS {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) :
    Continuous (partialS u) :=
  (hu.1.continuous_fderiv (by simp)).clm_apply continuous_const

lemma IsTestSection.continuous_partialT {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) :
    Continuous (partialT u) :=
  (hu.1.continuous_fderiv (by simp)).clm_apply continuous_const

lemma IsTestSection.memLp {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) : MemLp u p cylMeasure := by
  obtain ⟨R, hR⟩ := hu.2.2
  exact memLp_of_vanish u hu.continuous R hR

lemma IsTestSection.memLp_partialS {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) :
    MemLp (partialS u) p cylMeasure := by
  obtain ⟨R, hR⟩ := hu.2.2
  exact memLp_of_vanish _ hu.continuous_partialS R fun s t hs => partialS_eq_zero R hR hs

lemma IsTestSection.memLp_partialT {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) :
    MemLp (partialT u) p cylMeasure := by
  obtain ⟨R, hR⟩ := hu.2.2
  exact memLp_of_vanish _ hu.continuous_partialT R fun s t hs => partialT_eq_zero R hR hs

lemma IsTestSection.sub {u v : ℝ × ℝ → Vec n} (hu : IsTestSection u) (hv : IsTestSection v) :
    IsTestSection (u - v) := by
  obtain ⟨R₁, h₁⟩ := hu.2.2
  obtain ⟨R₂, h₂⟩ := hv.2.2
  refine ⟨ContDiff.sub hu.1 hv.1, fun s t => by simp [hu.2.1, hv.2.1], max R₁ R₂, fun s t hs => ?_⟩
  simp [h₁ s t (lt_of_le_of_lt (le_max_left _ _) hs), h₂ s t (lt_of_le_of_lt (le_max_right _ _) hs)]

lemma IsTestSection.add {u v : ℝ × ℝ → Vec n} (hu : IsTestSection u) (hv : IsTestSection v) :
    IsTestSection (u + v) := by
  obtain ⟨R₁, h₁⟩ := hu.2.2
  obtain ⟨R₂, h₂⟩ := hv.2.2
  refine ⟨ContDiff.add hu.1 hv.1, fun s t => by simp [hu.2.1, hv.2.1], max R₁ R₂, fun s t hs => ?_⟩
  simp [h₁ s t (lt_of_le_of_lt (le_max_left _ _) hs), h₂ s t (lt_of_le_of_lt (le_max_right _ _) hs)]

lemma IsTestSection.smul {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) (c : ℝ) :
    IsTestSection (c • u) := by
  obtain ⟨R₁, h₁⟩ := hu.2.2
  refine ⟨ContDiff.const_smul c hu.1, fun s t => by simp [hu.2.1], R₁, fun s t hs => ?_⟩
  simp [h₁ s t hs]

lemma isTestSection_zero : IsTestSection (0 : ℝ × ℝ → Vec n) :=
  ⟨contDiff_const, fun _ _ => rfl, 0, fun _ _ _ => rfl⟩

lemma partialS_add {u v : ℝ × ℝ → Vec n} (hu : IsTestSection u) (hv : IsTestSection v) :
    partialS (u + v) = partialS u + partialS v := by
  funext x
  simp only [partialS, Pi.add_apply]
  rw [fderiv_add ((hu.1.differentiable (by simp)) x) ((hv.1.differentiable (by simp)) x)]
  rfl

lemma partialT_add {u v : ℝ × ℝ → Vec n} (hu : IsTestSection u) (hv : IsTestSection v) :
    partialT (u + v) = partialT u + partialT v := by
  funext x
  simp only [partialT, Pi.add_apply]
  rw [fderiv_add ((hu.1.differentiable (by simp)) x) ((hv.1.differentiable (by simp)) x)]
  rfl

lemma partialS_sub {u v : ℝ × ℝ → Vec n} (hu : IsTestSection u) (hv : IsTestSection v) :
    partialS (u - v) = partialS u - partialS v := by
  funext x
  simp only [partialS, Pi.sub_apply]
  rw [fderiv_sub ((hu.1.differentiable (by simp)) x) ((hv.1.differentiable (by simp)) x)]
  rfl

lemma partialT_sub {u v : ℝ × ℝ → Vec n} (hu : IsTestSection u) (hv : IsTestSection v) :
    partialT (u - v) = partialT u - partialT v := by
  funext x
  simp only [partialT, Pi.sub_apply]
  rw [fderiv_sub ((hu.1.differentiable (by simp)) x) ((hv.1.differentiable (by simp)) x)]
  rfl

lemma partialS_smul {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) (c : ℝ) :
    partialS (c • u) = c • partialS u := by
  funext x
  simp only [partialS, Pi.smul_apply]
  rw [fderiv_const_smul ((hu.1.differentiable (by simp)) x)]
  rfl

lemma partialT_smul {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) (c : ℝ) :
    partialT (c • u) = c • partialT u := by
  funext x
  simp only [partialT, Pi.smul_apply]
  rw [fderiv_const_smul ((hu.1.differentiable (by simp)) x)]
  rfl

lemma partialS_zero : partialS (0 : ℝ × ℝ → Vec n) = 0 := by
  funext x; simp [partialS]

lemma partialT_zero : partialT (0 : ℝ × ℝ → Vec n) = 0 := by
  funext x; simp [partialT]

end

end CauchyRiemannIndex

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

variable {n : ℕ}

lemma cylMeasure_eq_prod :
    cylMeasure = (volume : Measure ℝ).prod (volume.restrict (Set.Ico (0 : ℝ) 1)) := by
  rw [cylMeasure, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]

lemma fderiv_eq_zero_of_vanish {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : ℝ × ℝ → E} (R : ℝ) (hR : ∀ s t, R < |s| → φ (s, t) = 0) {s t : ℝ} (hs : R < |s|) :
    fderiv ℝ φ (s, t) = 0 := by
  have hU : IsOpen {x : ℝ × ℝ | R < |x.1|} :=
    isOpen_lt continuous_const (continuous_abs.comp continuous_fst)
  have hev : φ =ᶠ[𝓝 (s, t)] fun _ => 0 :=
    Filter.eventually_of_mem (hU.mem_nhds hs) fun x hx => hR x.1 x.2 hx
  rw [hev.fderiv_eq]; simp

lemma hasCompactSupport_of_vanish {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} (R : ℝ)
    (hR : ∀ s, R < |s| → f s = 0) : HasCompactSupport f :=
  HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R)) fun s hs =>
    hR s (not_le.1 fun h => hs (abs_le.1 h))

/-- `∫ ∂ₛφ = 0` over the cylinder for a `C¹` function vanishing for large `|s|`. -/
lemma integral_fderiv_s_eq_zero (φ : ℝ × ℝ → ℝ) (hφ : ContDiff ℝ 1 φ) (R : ℝ)
    (hR : ∀ s t, R < |s| → φ (s, t) = 0) :
    ∫ x, fderiv ℝ φ x (1, 0) ∂cylMeasure = 0 := by
  have hc : Continuous fun x => fderiv ℝ φ x (1, 0) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hI : Integrable (fun x => fderiv ℝ φ x (1, 0)) cylMeasure := by
    rw [← memLp_one_iff_integrable]
    exact memLp_of_vanish _ hc R fun s t hs => by simp [fderiv_eq_zero_of_vanish R hR hs]
  rw [cylMeasure_eq_prod] at hI ⊢
  rw [integral_prod_symm _ hI]
  have h : ∀ t : ℝ, ∫ s, fderiv ℝ φ (s, t) (1, 0) = 0 := by
    intro t
    have hd : ∀ s, HasDerivAt (fun s => φ (s, t)) (fderiv ℝ φ (s, t) (1, 0)) s := by
      intro s
      have h1 : HasDerivAt (fun s : ℝ => (s, t)) ((1 : ℝ), (0 : ℝ)) s :=
        (hasDerivAt_id s).prodMk (hasDerivAt_const s t)
      exact ((hφ.differentiable (by simp)) (s, t)).hasFDerivAt.comp_hasDerivAt s h1
    refine integral_eq_zero_of_hasDerivAt_of_integrable hd ?_ ?_
    · exact (hc.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
        (hasCompactSupport_of_vanish R fun s hs => by
          simp [fderiv_eq_zero_of_vanish R hR hs])
    · exact (hφ.continuous.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
        (hasCompactSupport_of_vanish R fun s hs => hR s t hs)
  simp [h]

/-- `∫ ∂ₜφ = 0` over the cylinder for a `C¹` function, `1`-periodic in `t`, vanishing for large
`|s|`. -/
lemma integral_fderiv_t_eq_zero (φ : ℝ × ℝ → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hper : ∀ s t, φ (s, t + 1) = φ (s, t)) (R : ℝ) (hR : ∀ s t, R < |s| → φ (s, t) = 0) :
    ∫ x, fderiv ℝ φ x (0, 1) ∂cylMeasure = 0 := by
  have hc : Continuous fun x => fderiv ℝ φ x (0, 1) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hI : Integrable (fun x => fderiv ℝ φ x (0, 1)) cylMeasure := by
    rw [← memLp_one_iff_integrable]
    exact memLp_of_vanish _ hc R fun s t hs => by simp [fderiv_eq_zero_of_vanish R hR hs]
  rw [cylMeasure_eq_prod] at hI ⊢
  rw [integral_prod _ hI]
  have h : ∀ s : ℝ, ∫ t in Set.Ico (0 : ℝ) 1, fderiv ℝ φ (s, t) (0, 1) = 0 := by
    intro s
    have hd : ∀ t, HasDerivAt (fun t => φ (s, t)) (fderiv ℝ φ (s, t) (0, 1)) t := by
      intro t
      have h1 : HasDerivAt (fun t : ℝ => (s, t)) ((0 : ℝ), (1 : ℝ)) t :=
        (hasDerivAt_const t s).prodMk (hasDerivAt_id t)
      exact ((hφ.differentiable (by simp)) (s, t)).hasFDerivAt.comp_hasDerivAt t h1
    rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
        ((hc.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)]
    have := hper s 0
    simp only [zero_add] at this
    rw [this, sub_self]
  simp [h]

lemma inner_toEuclideanLin (A : Mat n) (x y : Vec n) :
    inner ℝ (Matrix.toEuclideanLin A x) y = inner ℝ x (Matrix.toEuclideanLin Aᵀ y) := by
  have h := Matrix.toEuclideanLin_conjTranspose_eq_adjoint A
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  rw [h, LinearMap.adjoint_inner_right]

lemma fderiv_matCLM_comp {v : ℝ × ℝ → Vec n} (A : Mat n) {x : ℝ × ℝ}
    (hv : DifferentiableAt ℝ v x) (h : ℝ × ℝ) :
    fderiv ℝ (fun y => Matrix.toEuclideanLin A (v y)) x h =
      Matrix.toEuclideanLin A (fderiv ℝ v x h) := by
  have : (fun y => Matrix.toEuclideanLin A (v y)) = (matCLM n A) ∘ v := rfl
  rw [this, fderiv_comp x (matCLM n A).differentiableAt hv, ContinuousLinearMap.fderiv]
  rfl

end

end CauchyRiemannIndex

/-!
# Calculus helpers for the antilinear term on the cylinder
-/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

/-- `β ↦ A(β)` as a real-linear map. -/
def almL : ℂ →ₗ[ℝ] Mat 1 where
  toFun := antilinearMat
  map_add' := lap_alm_add
  map_smul' c b := by
    rw [RingHom.id_apply, ← lap_alm_smul, Complex.real_smul]

/-- `β ↦ (v ↦ A(β) v)` as a continuous real-linear map. -/
def almK : ℂ →L[ℝ] (Vec 1 →L[ℝ] Vec 1) :=
  LinearMap.toContinuousLinearMap (matCLM 1 ∘ₗ almL)

lemma almK_apply (b : ℂ) (v : Vec 1) :
    almK b v = Matrix.toEuclideanLin (antilinearMat b) v := rfl

/-- `∂ₛβ`. -/
def dS (β : ℝ × ℝ → ℂ) (x : ℝ × ℝ) : ℂ := fderiv ℝ β x (1, 0)

/-- `∂ₜβ`. -/
def dT (β : ℝ × ℝ → ℂ) (x : ℝ × ℝ) : ℂ := fderiv ℝ β x (0, 1)

lemma hasDerivAt_slice_s {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : ℝ × ℝ → E} (hu : Differentiable ℝ u) (s t : ℝ) :
    HasDerivAt (fun s => u (s, t)) (fderiv ℝ u (s, t) (1, 0)) s := by
  have h1 : HasDerivAt (fun s : ℝ => (s, t)) ((1 : ℝ), (0 : ℝ)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s t)
  exact (hu (s, t)).hasFDerivAt.comp_hasDerivAt s h1

lemma hasDerivAt_slice_t {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : ℝ × ℝ → E} (hu : Differentiable ℝ u) (s t : ℝ) :
    HasDerivAt (fun t => u (s, t)) (fderiv ℝ u (s, t) (0, 1)) t := by
  have h1 : HasDerivAt (fun t : ℝ => (s, t)) ((0 : ℝ), (1 : ℝ)) t :=
    (hasDerivAt_const t s).prodMk (hasDerivAt_id t)
  exact (hu (s, t)).hasFDerivAt.comp_hasDerivAt t h1

/-- `∫ g = 0` over the cylinder when `g = ∂ₛF` slice-wise, with `g` continuous and both `g` and
`F` vanishing for large `|s|`. -/
lemma lap_integral_s_eq_zero (g F : ℝ × ℝ → ℝ) (hg : Continuous g) (R : ℝ)
    (hgR : ∀ s t, R < |s| → g (s, t) = 0) (hFR : ∀ s t, R < |s| → F (s, t) = 0)
    (hF : ∀ s t, HasDerivAt (fun s => F (s, t)) (g (s, t)) s) :
    ∫ x, g x ∂cylMeasure = 0 := by
  have hI : Integrable g cylMeasure := by
    rw [← memLp_one_iff_integrable]
    exact memLp_of_vanish g hg R hgR
  rw [cylMeasure_eq_prod] at hI ⊢
  rw [integral_prod_symm _ hI]
  have h : ∀ t : ℝ, ∫ s, g (s, t) = 0 := by
    intro t
    have hFc : Continuous fun s => F (s, t) :=
      continuous_iff_continuousAt.2 fun s => (hF s t).continuousAt
    refine integral_eq_zero_of_hasDerivAt_of_integrable (fun s => hF s t) ?_ ?_
    · exact (hg.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
        (hasCompactSupport_of_vanish R fun s hs => hgR s t hs)
    · exact hFc.integrable_of_hasCompactSupport (hasCompactSupport_of_vanish R fun s hs => hFR s t hs)
  simp [h]

/-- `∫ g = 0` over the cylinder when `g = ∂ₜF` slice-wise, `F` is `1`-periodic in `t`, and `g`
is continuous and vanishes for large `|s|`. -/
lemma integral_t_eq_zero_of_hasDerivAt (g F : ℝ × ℝ → ℝ) (hg : Continuous g) (R : ℝ)
    (hgR : ∀ s t, R < |s| → g (s, t) = 0) (hper : ∀ s t, F (s, t + 1) = F (s, t))
    (hF : ∀ s t, HasDerivAt (fun t => F (s, t)) (g (s, t)) t) :
    ∫ x, g x ∂cylMeasure = 0 := by
  have hI : Integrable g cylMeasure := by
    rw [← memLp_one_iff_integrable]
    exact memLp_of_vanish g hg R hgR
  rw [cylMeasure_eq_prod] at hI ⊢
  rw [integral_prod _ hI]
  have h : ∀ s : ℝ, ∫ t in Set.Ico (0 : ℝ) 1, g (s, t) = 0 := by
    intro s
    rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hF s t)
        ((hg.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)]
    have := hper s 0
    simp only [zero_add] at this
    rw [this, sub_self]
  simp [h]

lemma lap_integrable {F : ℝ × ℝ → ℝ} (hF : Continuous F) (R : ℝ)
    (hR : ∀ s t, R < |s| → F (s, t) = 0) : Integrable F cylMeasure := by
  rw [← memLp_one_iff_integrable]
  exact memLp_of_vanish F hF R hR

end

end CauchyRiemannIndex

/-!
# Periodizing a function supported in `(-1/2, 1/2)`

`t ↦ f(t - c - round(t - c))` is smooth and `1`-periodic when `f` is smooth and vanishes on
`|w| ≥ b` for some `b < 1/2`; near `c + m` it equals `t ↦ f(t - c - m)`.
-/

namespace CauchyRiemannIndex

open Filter Topology
open scoped ContDiff

noncomputable section

/-- The representative of `t - c` in `[-1/2, 1/2)`. -/
def lapW (c t : ℝ) : ℝ := t - c - round (t - c)

lemma lapW_eq {c t : ℝ} {m : ℤ} (h : |t - c - m| < 1 / 2) : lapW c t = t - c - m := by
  unfold lapW
  congr 2
  rw [round_eq_iff]
  constructor <;> linarith [(abs_lt.1 h).1, (abs_lt.1 h).2]

lemma lapW_add_one (c t : ℝ) : lapW c (t + 1) = lapW c t := by
  unfold lapW
  rw [show t + 1 - c = t - c + 1 by ring, round_add_one]
  push_cast; ring

lemma lapW_le (c t : ℝ) (m : ℤ) : |lapW c t| ≤ |t - c - m| := round_le (t - c) m

lemma lapW_exists (c t : ℝ) : ∃ m : ℤ, lapW c t = t - c - m := ⟨round (t - c), rfl⟩

lemma lap_per_eventually {f : ℝ → ℝ} {b : ℝ} (hb : b < 1 / 2)
    (hfb : ∀ w, b ≤ |w| → f w = 0) (c t₀ : ℝ) :
    (∃ m : ℤ, (fun t => f (lapW c t)) =ᶠ[𝓝 t₀] fun t => f (t - c - m)) ∨
      (fun t => f (lapW c t)) =ᶠ[𝓝 t₀] fun _ => 0 := by
  set ε := (1 / 2 - b) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hball : ∀ᶠ t in 𝓝 t₀, |t - t₀| < ε := by
    have : Metric.ball t₀ ε ∈ 𝓝 t₀ := Metric.ball_mem_nhds t₀ hε0
    filter_upwards [this] with t ht
    rwa [Metric.mem_ball, Real.dist_eq] at ht
  by_cases hA : ∃ m : ℤ, |t₀ - c - m| < 1 / 2 - ε
  · obtain ⟨m, hm⟩ := hA
    refine Or.inl ⟨m, ?_⟩
    filter_upwards [hball] with t ht
    have : |t - c - m| < 1 / 2 := by
      calc |t - c - m| = |(t₀ - c - m) + (t - t₀)| := by ring_nf
        _ ≤ |t₀ - c - m| + |t - t₀| := abs_add_le _ _
        _ < 1 / 2 := by linarith
    rw [lapW_eq this]
  · push Not at hA
    refine Or.inr ?_
    filter_upwards [hball] with t ht
    obtain ⟨m, hm⟩ := lapW_exists c t
    apply hfb
    rw [hm]
    have h1 := hA m
    calc b = 1 / 2 - ε - ε := by rw [hε]; ring
      _ ≤ |t₀ - c - m| - |t - t₀| := by linarith
      _ ≤ |t - c - m| := by
        have := abs_sub_abs_le_abs_sub (t₀ - c - m) (t₀ - t)
        rw [abs_sub_comm t₀ t] at this
        calc |t₀ - c - m| - |t - t₀| ≤ |t₀ - c - m - (t₀ - t)| := this
          _ = |t - c - m| := by ring_nf

lemma lap_per_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {b : ℝ} (hb : b < 1 / 2)
    (hfb : ∀ w, b ≤ |w| → f w = 0) (c : ℝ) : ContDiff ℝ ∞ (fun t => f (lapW c t)) := by
  rw [contDiff_iff_contDiffAt]
  intro t₀
  rcases lap_per_eventually hb hfb c t₀ with ⟨m, hm⟩ | h0
  · have : ContDiffAt ℝ ∞ (fun t => f (t - c - m)) t₀ :=
      (ContDiff.comp hf ((contDiff_id.sub contDiff_const).sub contDiff_const)).contDiffAt
    exact this.congr_of_eventuallyEq hm
  · exact contDiffAt_const.congr_of_eventuallyEq h0

end

end CauchyRiemannIndex

/-!
# Gaussian approximate kernel elements at the positive zeros

`v_ζ(s, t) = h(s - ζₛ) h(t - ζₜ mod 1) e₁` with `h(y) = ψ(y) e^{-σ y²/2}`. In the normal-form
disc `D_σ (e^{-σ|z|²/2} e₁) = 0`, so `D_σ v_ζ` only sees the derivative of the cutoff, where the
Gaussian is `≤ e^{-σ a²/8}`.
-/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology Metric
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section


/-- `e₁`. -/
def lapE : Vec 1 := EuclideanSpace.single (Sum.inl 0 : Fin 1 ⊕ Fin 1) 1

lemma lapE_1 : lapE (Sum.inl 0 : Fin 1 ⊕ Fin 1) = 1 := by simp [lapE]
lemma lapE_2 : lapE (Sum.inr 0 : Fin 1 ⊕ Fin 1) = 0 := by simp [lapE]

/-- `G(y) = e^{-σ y² / 2}`. -/
def lapG (σ y : ℝ) : ℝ := Real.exp (-(σ * y ^ 2) / 2)

/-- `h(y) = ψ(y) G(y)`. -/
def lapH {a : ℝ} (ha : 0 < a) (σ y : ℝ) : ℝ := lapPsi ha y * lapG σ y

lemma lapG_hasDerivAt (σ y : ℝ) : HasDerivAt (lapG σ) (-(σ * y) * lapG σ y) y := by
  have h := ((((hasDerivAt_id y).pow 2).const_mul σ).neg.div_const 2).exp
  unfold lapG
  refine h.congr_deriv ?_
  simp; ring

lemma lapG_pos (σ y : ℝ) : 0 < lapG σ y := Real.exp_pos _

lemma lapG_le_one {σ : ℝ} (hσ : 0 ≤ σ) (y : ℝ) : lapG σ y ≤ 1 := by
  unfold lapG; rw [Real.exp_le_one_iff]
  have : 0 ≤ σ * y ^ 2 := by positivity
  linarith

lemma lapG_le {σ : ℝ} (hσ : 0 ≤ σ) {y b : ℝ} (hy : b ≤ |y|) (hb : 0 ≤ b) :
    lapG σ y ≤ Real.exp (-(σ * b ^ 2) / 2) := by
  unfold lapG
  rw [Real.exp_le_exp]
  have : b ^ 2 ≤ y ^ 2 := by
    have := pow_le_pow_left₀ hb hy 2; rwa [sq_abs] at this
  have : σ * b ^ 2 ≤ σ * y ^ 2 := mul_le_mul_of_nonneg_left this hσ
  linarith

lemma lapG_ge {σ : ℝ} (hσ : 0 ≤ σ) {y b : ℝ} (hy : |y| ≤ b) :
    Real.exp (-(σ * b ^ 2) / 2) ≤ lapG σ y := by
  unfold lapG
  rw [Real.exp_le_exp]
  have : y ^ 2 ≤ b ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg y) hy 2; rwa [sq_abs] at this
  have : σ * y ^ 2 ≤ σ * b ^ 2 := mul_le_mul_of_nonneg_left this hσ
  linarith

/-- `h'(y) = ψ'(y) G(y) - σ y h(y)`. -/
lemma lapH_hasDerivAt {a : ℝ} (ha : 0 < a) (σ y : ℝ) :
    HasDerivAt (lapH ha σ) (deriv (lapPsi ha) y * lapG σ y - σ * y * lapH ha σ y) y := by
  have h := ((lapPsi_diff ha) y).hasDerivAt.mul (lapG_hasDerivAt σ y)
  unfold lapH
  refine h.congr_deriv ?_
  ring

lemma lapH_contDiff {a : ℝ} (ha : 0 < a) (σ : ℝ) : ContDiff ℝ ∞ (lapH ha σ) := by
  unfold lapH lapG
  exact (lapPsi ha).contDiff.mul (Real.contDiff_exp.comp (by fun_prop))

lemma lapH_eq_zero {a : ℝ} (ha : 0 < a) (σ : ℝ) {y : ℝ} (hy : 3 * a / 4 ≤ |y|) :
    lapH ha σ y = 0 := by
  unfold lapH; rw [lapPsi_eq_zero ha hy, zero_mul]

lemma lapH_nonneg {a : ℝ} (ha : 0 < a) (σ y : ℝ) : 0 ≤ lapH ha σ y :=
  mul_nonneg (lapPsi ha).nonneg (lapG_pos σ y).le

lemma lapH_le_one {a : ℝ} (ha : 0 < a) {σ : ℝ} (hσ : 0 ≤ σ) (y : ℝ) : lapH ha σ y ≤ 1 := by
  unfold lapH
  calc lapPsi ha y * lapG σ y ≤ 1 * 1 :=
        mul_le_mul (lapPsi ha).le_one (lapG_le_one hσ y) (lapG_pos σ y).le zero_le_one
    _ = 1 := one_mul 1

lemma lapH_ge {a : ℝ} (ha : 0 < a) {σ : ℝ} (hσ : 0 ≤ σ) {y : ℝ} (hy : |y| ≤ a / 8) :
    Real.exp (-(σ * (a / 8) ^ 2) / 2) ≤ lapH ha σ y := by
  unfold lapH
  rw [lapPsi_eq_one ha (by linarith), one_mul]
  exact lapG_ge hσ hy

lemma lapPsi_deriv_bounded {a : ℝ} (ha : 0 < a) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u, |deriv (lapPsi ha) u| ≤ B := by
  have hc : Continuous (deriv (lapPsi ha)) :=
    ((lapPsi ha).contDiff (n := 1)).continuous_deriv le_rfl
  obtain ⟨B, hB⟩ := hc.bounded_above_of_compact_support
    (HasCompactSupport.intro (isCompact_Icc (a := -a) (b := a)) fun u hu => by
      refine lapPsi_deriv_eq_zero ha ?_
      have : a < |u| := by
        by_contra h
        exact hu (abs_le.1 (not_lt.1 h))
      linarith)
  exact ⟨max B 0, le_max_right _ _, fun u => (hB u).trans (le_max_left _ _)⟩

/-- The cutoff error `ψ'(y) G(y)` is exponentially small. -/
lemma lap_err_le {a : ℝ} (ha : 0 < a) {σ : ℝ} (hσ : 0 ≤ σ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ u, |deriv (lapPsi ha) u| ≤ B) (y : ℝ) :
    |deriv (lapPsi ha) y * lapG σ y| ≤ B * Real.exp (-(σ * (a / 2) ^ 2) / 2) := by
  by_cases hy : |y| < a / 2
  · rw [lapPsi_deriv_eq_zero' ha hy, zero_mul, abs_zero]; positivity
  · rw [abs_mul, abs_of_pos (lapG_pos σ y)]
    exact mul_le_mul (hB y) (lapG_le hσ (not_lt.1 hy) (by positivity)) (lapG_pos σ y).le hB0

/-! ### The section -/

/-- `F_ζ(s, t) = h(s - ζₛ) h(t - ζₜ mod 1)`. -/
def lapF {a : ℝ} (ha : 0 < a) (σ : ℝ) (ζ : ℝ × ℝ) (x : ℝ × ℝ) : ℝ :=
  lapH ha σ (x.1 - ζ.1) * lapH ha σ (lapW ζ.2 x.2)

/-- `v_ζ = F_ζ e₁`. -/
def lapV {a : ℝ} (ha : 0 < a) (σ : ℝ) (ζ : ℝ × ℝ) (x : ℝ × ℝ) : Vec 1 := lapF ha σ ζ x • lapE

lemma lapHper_contDiff {a : ℝ} (ha : 0 < a) (ha' : a ≤ 1 / 4) (σ c : ℝ) :
    ContDiff ℝ ∞ (fun t => lapH ha σ (lapW c t)) :=
  lap_per_contDiff (lapH_contDiff ha σ) (b := 3 * a / 4) (by linarith)
    (fun w hw => lapH_eq_zero ha σ hw) c

lemma lapF_contDiff {a : ℝ} (ha : 0 < a) (ha' : a ≤ 1 / 4) (σ : ℝ) (ζ : ℝ × ℝ) :
    ContDiff ℝ ∞ (lapF ha σ ζ) := by
  unfold lapF
  exact ((lapH_contDiff ha σ).comp (contDiff_fst.sub contDiff_const)).mul
    ((lapHper_contDiff ha ha' σ ζ.2).comp contDiff_snd)

lemma lapV_test {a : ℝ} (ha : 0 < a) (ha' : a ≤ 1 / 4) (σ : ℝ) (ζ : ℝ × ℝ) :
    IsTestSection (lapV ha σ ζ) := by
  refine ⟨(lapF_contDiff ha ha' σ ζ).smul contDiff_const, fun s t => ?_, |ζ.1| + 1,
    fun s t hs => ?_⟩
  · simp only [lapV, lapF, lapW_add_one]
  · have : 3 * a / 4 ≤ |s - ζ.1| := by
      have := abs_sub_abs_le_abs_sub s ζ.1
      linarith
    simp [lapV, lapF, lapH_eq_zero ha σ this]

lemma lapF_ne_zero {a : ℝ} (ha : 0 < a) (σ : ℝ) (ζ x : ℝ × ℝ) (h : lapF ha σ ζ x ≠ 0) :
    |x.1 - ζ.1| < 3 * a / 4 ∧ ∃ m : ℤ, |x.2 - ζ.2 - m| < 3 * a / 4 := by
  unfold lapF at h
  refine ⟨?_, ?_⟩
  · by_contra h'
    exact h (by rw [lapH_eq_zero ha σ (not_lt.1 h'), zero_mul])
  · obtain ⟨m, hm⟩ := lapW_exists ζ.2 x.2
    refine ⟨m, ?_⟩
    by_contra h'
    rw [← hm] at h'
    exact h (by rw [lapH_eq_zero ha σ (not_lt.1 h'), mul_zero])

/-- `∂ₛ` and `∂ₜ` of a product `p(s) q(t)`. -/
lemma lap_fderiv_prod {p q : ℝ → ℝ} {p' q' : ℝ} {x : ℝ × ℝ} (hp : Differentiable ℝ p)
    (hq : Differentiable ℝ q) (hp' : HasDerivAt p p' x.1) (hq' : HasDerivAt q q' x.2) :
    fderiv ℝ (fun y : ℝ × ℝ => p y.1 * q y.2) x (1, 0) = p' * q x.2 ∧
      fderiv ℝ (fun y : ℝ × ℝ => p y.1 * q y.2) x (0, 1) = p x.1 * q' := by
  have hd : Differentiable ℝ (fun y : ℝ × ℝ => p y.1 * q y.2) :=
    (hp.comp differentiable_fst).mul (hq.comp differentiable_snd)
  constructor
  · have h1 := hasDerivAt_slice_s hd x.1 x.2
    have h2 : HasDerivAt (fun s => p s * q x.2) (p' * q x.2) x.1 := hp'.mul_const _
    exact h1.unique h2
  · have h1 := hasDerivAt_slice_t hd x.1 x.2
    have h2 : HasDerivAt (fun t => p x.1 * q t) (p x.1 * q') x.2 := hq'.const_mul _
    exact h1.unique h2

lemma lap_partial_smul {F : ℝ × ℝ → ℝ} {x : ℝ × ℝ} (hF : DifferentiableAt ℝ F x) (h : ℝ × ℝ) :
    fderiv ℝ (fun y => F y • lapE) x h = fderiv ℝ F x h • lapE := by
  rw [fderiv_smul_const hF]
  rfl

/-- Pointwise bound for `D_σ v_ζ`: exponentially small, and zero unless `|s - ζₛ| < a`. -/
lemma lap_crOp_bound {a : ℝ} (ha : 0 < a) (ha' : a ≤ 1 / 4) {σ : ℝ} (hσ : 0 ≤ σ)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ u, |deriv (lapPsi ha) u| ≤ B)
    (S : ℝ × ℝ → Mat 1) (β : ℝ × ℝ → ℂ) (ζ : ℝ × ℝ)
    (hβloc : ∀ m : ℤ, ∀ u v : ℝ, |u| < a → |v| < a → β (ζ.1 + u, ζ.2 + m + v) = ⟨u, v⟩)
    (hSloc : ∀ m : ℤ, ∀ u v : ℝ, |u| < a → |v| < a → S (ζ.1 + u, ζ.2 + m + v) = 0)
    (x : ℝ × ℝ) :
    ‖crOp (fun x => S x + σ • antilinearMat (β x)) (lapV ha σ ζ) x‖ ^ 2 ≤
      Set.indicator {y : ℝ × ℝ | |y.1 - ζ.1| < a}
        (fun _ => 2 * (B * Real.exp (-(σ * (a / 2) ^ 2) / 2)) ^ 2) x := by
  set E := Real.exp (-(σ * (a / 2) ^ 2) / 2)
  set F := lapF ha σ ζ
  have hFd : Differentiable ℝ F := (lapF_contDiff ha ha' σ ζ).differentiable (by simp)
  have hpS : partialS (lapV ha σ ζ) x = fderiv ℝ F x (1, 0) • lapE :=
    lap_partial_smul (hFd x) _
  have hpT : partialT (lapV ha σ ζ) x = fderiv ℝ F x (0, 1) • lapE :=
    lap_partial_smul (hFd x) _
  have hnn : 0 ≤ Set.indicator {y : ℝ × ℝ | |y.1 - ζ.1| < a}
      (fun _ => 2 * (B * E) ^ 2) x := Set.indicator_nonneg (fun _ _ => by positivity) x
  -- when `F` and its derivative vanish at `x`
  have hzero : F x = 0 → fderiv ℝ F x (1, 0) = 0 → fderiv ℝ F x (0, 1) = 0 →
      crOp (fun x => S x + σ • antilinearMat (β x)) (lapV ha σ ζ) x = 0 := by
    intro h0 h1 h2
    simp only [crOp, hpS, hpT, h1, h2, zero_smul, map_zero, zero_add]
    simp [lapV, show lapF ha σ ζ x = 0 from h0]
  have hp := lap_per_eventually (f := lapH ha σ) (b := 3 * a / 4) (by linarith)
    (fun w hw => lapH_eq_zero ha σ hw) ζ.2 x.2
  have hsnd : Tendsto Prod.snd (𝓝 x) (𝓝 x.2) := continuous_snd.continuousAt
  rcases hp with ⟨m, hm⟩ | h0
  · set Φ : ℝ × ℝ → ℝ := fun y => lapH ha σ (y.1 - ζ.1) * lapH ha σ (y.2 - ζ.2 - m)
    have hev : F =ᶠ[𝓝 x] Φ := by
      filter_upwards [hm.comp_tendsto hsnd] with y hy
      simp only [F, Φ, lapF, Function.comp] at hy ⊢
      rw [hy]
    set u := x.1 - ζ.1
    set w := x.2 - ζ.2 - m
    have hhd := (lapH_contDiff ha σ).differentiable (n := ∞) (by simp)
    have hpd : Differentiable ℝ fun s => lapH ha σ (s - ζ.1) := hhd.comp (differentiable_id.sub_const _)
    have hqd : Differentiable ℝ fun t => lapH ha σ (t - ζ.2 - m) :=
      hhd.comp ((differentiable_id.sub_const _).sub_const _)
    have hp' : HasDerivAt (fun s => lapH ha σ (s - ζ.1))
        (deriv (lapPsi ha) u * lapG σ u - σ * u * lapH ha σ u) x.1 := by
      have := (lapH_hasDerivAt ha σ u).comp x.1 ((hasDerivAt_id x.1).sub_const ζ.1)
      rw [mul_one] at this; exact this
    have hq' : HasDerivAt (fun t => lapH ha σ (t - ζ.2 - m))
        (deriv (lapPsi ha) w * lapG σ w - σ * w * lapH ha σ w) x.2 := by
      have := (lapH_hasDerivAt ha σ w).comp x.2
        (((hasDerivAt_id x.2).sub_const ζ.2).sub_const (m : ℝ))
      rw [mul_one] at this; exact this
    obtain ⟨d1, d2⟩ := lap_fderiv_prod hpd hqd hp' hq'
    have hFx : F x = lapH ha σ u * lapH ha σ w := hev.eq_of_nhds
    have e1 : fderiv ℝ F x (1, 0) =
        (deriv (lapPsi ha) u * lapG σ u - σ * u * lapH ha σ u) * lapH ha σ w := by
      rw [hev.fderiv_eq]; exact d1
    have e2 : fderiv ℝ F x (0, 1) =
        lapH ha σ u * (deriv (lapPsi ha) w * lapG σ w - σ * w * lapH ha σ w) := by
      rw [hev.fderiv_eq]; exact d2
    by_cases hloc : |u| < a ∧ |w| < a
    · obtain ⟨hu, hw⟩ := hloc
      have hxe : x = (ζ.1 + u, ζ.2 + m + w) := by simp [u, w]
      have hβx : β x = ⟨u, w⟩ := by rw [hxe]; exact hβloc m u w hu hw
      have hSx : S x = 0 := by rw [hxe]; exact hSloc m u w hu hw
      set Y := crOp (fun x => S x + σ • antilinearMat (β x)) (lapV ha σ ζ) x
      have hY1 : Y (Sum.inl 0 : Fin 1 ⊕ Fin 1) = deriv (lapPsi ha) u * lapG σ u * lapH ha σ w := by
        simp only [Y, crOp, hpS, hpT, hSx, zero_add, PiLp.add_apply, PiLp.smul_apply,
          smul_eq_mul, lapE_1, mul_one, lap_J_1, lapE_2, mul_zero, neg_zero, add_zero]
        rw [map_smul, LinearMap.smul_apply, PiLp.smul_apply, lap_alm_1, hβx]
        simp only [lapV, PiLp.smul_apply, smul_eq_mul, lapE_1, lapE_2, mul_one, mul_zero,
          add_zero]
        rw [e1, show lapF ha σ ζ x = F x from rfl, hFx]
        ring
      have hY2 : Y (Sum.inr 0 : Fin 1 ⊕ Fin 1) = lapH ha σ u * (deriv (lapPsi ha) w * lapG σ w) := by
        simp only [Y, crOp, hpS, hpT, hSx, zero_add, PiLp.add_apply, PiLp.smul_apply,
          smul_eq_mul, lapE_2, mul_zero, lap_J_2, lapE_1, mul_one]
        rw [map_smul, LinearMap.smul_apply, PiLp.smul_apply, lap_alm_2, hβx]
        simp only [lapV, PiLp.smul_apply, smul_eq_mul, lapE_1, lapE_2, mul_one, mul_zero,
          sub_zero]
        rw [e2, show lapF ha σ ζ x = F x from rfl, hFx]
        ring
      have hb1 : |Y (Sum.inl 0 : Fin 1 ⊕ Fin 1)| ≤ B * E := by
        rw [hY1, abs_mul]
        have := lap_err_le ha hσ hB0 hB u
        have h1 : |lapH ha σ w| ≤ 1 := by
          rw [abs_of_nonneg (lapH_nonneg ha σ w)]; exact lapH_le_one ha hσ w
        calc |deriv (lapPsi ha) u * lapG σ u| * |lapH ha σ w| ≤ (B * E) * 1 :=
              mul_le_mul this h1 (abs_nonneg _) (by positivity)
          _ = B * E := mul_one _
      have hb2 : |Y (Sum.inr 0 : Fin 1 ⊕ Fin 1)| ≤ B * E := by
        rw [hY2, abs_mul]
        have := lap_err_le ha hσ hB0 hB w
        have h1 : |lapH ha σ u| ≤ 1 := by
          rw [abs_of_nonneg (lapH_nonneg ha σ u)]; exact lapH_le_one ha hσ u
        calc |lapH ha σ u| * |deriv (lapPsi ha) w * lapG σ w| ≤ 1 * (B * E) :=
              mul_le_mul h1 this (abs_nonneg _) zero_le_one
          _ = B * E := one_mul _
      rw [Set.indicator_of_mem (show x ∈ {y : ℝ × ℝ | |y.1 - ζ.1| < a} from hu), lap_norm_sq]
      have h1 := pow_le_pow_left₀ (abs_nonneg _) hb1 2
      have h2 := pow_le_pow_left₀ (abs_nonneg _) hb2 2
      rw [sq_abs] at h1 h2
      linarith
    · -- outside the local box: `F` and its derivative vanish at `x`
      have hdz : ∀ y : ℝ, a ≤ |y| → lapH ha σ y = 0 ∧
          deriv (lapPsi ha) y * lapG σ y - σ * y * lapH ha σ y = 0 := by
        intro y hy
        have h1 := lapH_eq_zero ha σ (show 3 * a / 4 ≤ |y| by linarith)
        refine ⟨h1, ?_⟩
        rw [lapPsi_deriv_eq_zero ha (by linarith), h1]; ring
      have hY : crOp (fun x => S x + σ • antilinearMat (β x)) (lapV ha σ ζ) x = 0 := by
        rcases not_and_or.1 hloc with hu | hw
        · obtain ⟨z1, z2⟩ := hdz u (not_lt.1 hu)
          exact hzero (by rw [hFx, z1, zero_mul]) (by rw [e1, z2, zero_mul])
            (by rw [e2, z1, zero_mul])
        · obtain ⟨z1, z2⟩ := hdz w (not_lt.1 hw)
          exact hzero (by rw [hFx, z1, mul_zero]) (by rw [e1, z1, mul_zero])
            (by rw [e2, z2, mul_zero])
      rw [hY, norm_zero]; simpa using hnn
  · have hev : F =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [h0.comp_tendsto hsnd] with y hy
      simp only [F, lapF, Function.comp] at hy ⊢
      rw [hy, mul_zero]
    have hd : fderiv ℝ F x = 0 := by rw [hev.fderiv_eq]; simp
    have hY := hzero hev.eq_of_nhds (by rw [hd]; rfl) (by rw [hd]; rfl)
    rw [hY, norm_zero]; simpa using hnn

lemma lap_meas_box (c d e f : ℝ) (hc : c ≤ d) (he : 0 ≤ e) (hef : e ≤ f) (hf : f ≤ 1) :
    cylMeasure (Set.Ioo c d ×ˢ Set.Ioo e f) = ENNReal.ofReal (d - c) * ENNReal.ofReal (f - e) := by
  rw [cylMeasure_eq_prod, Measure.prod_prod, Real.volume_Ioo,
    Measure.restrict_apply measurableSet_Ioo,
    Set.inter_eq_left.2 (show Set.Ioo e f ⊆ Set.Ico 0 1 from fun t ht =>
      ⟨he.trans ht.1.le, ht.2.trans_le hf⟩), Real.volume_Ioo]

lemma lap_meas_strip (c d : ℝ) :
    cylMeasure (Set.Ioo c d ×ˢ (Set.univ : Set ℝ)) = ENNReal.ofReal (d - c) := by
  rw [cylMeasure_eq_prod, Measure.prod_prod, Real.volume_Ioo, Measure.restrict_apply_univ,
    Real.volume_Ico]
  simp

/-- `∫ |D_σ v_ζ|² ≤ 4a (B e^{-σ a²/8})²`. -/
lemma lap_crOp_integral {a : ℝ} (ha : 0 < a) (ha' : a ≤ 1 / 4) {σ : ℝ} (hσ : 0 ≤ σ)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ u, |deriv (lapPsi ha) u| ≤ B)
    (S : ℝ × ℝ → Mat 1) (β : ℝ × ℝ → ℂ) (ζ : ℝ × ℝ)
    (hβloc : ∀ m : ℤ, ∀ u v : ℝ, |u| < a → |v| < a → β (ζ.1 + u, ζ.2 + m + v) = ⟨u, v⟩)
    (hSloc : ∀ m : ℤ, ∀ u v : ℝ, |u| < a → |v| < a → S (ζ.1 + u, ζ.2 + m + v) = 0) :
    ∫ x, ‖crOp (fun x => S x + σ • antilinearMat (β x)) (lapV ha σ ζ) x‖ ^ 2 ∂cylMeasure ≤
      2 * a * (2 * (B * Real.exp (-(σ * (a / 2) ^ 2) / 2)) ^ 2) := by
  have hset : {y : ℝ × ℝ | |y.1 - ζ.1| < a} = Set.Ioo (ζ.1 - a) (ζ.1 + a) ×ˢ Set.univ := by
    ext y; simp [abs_lt]; constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have hm : MeasurableSet {y : ℝ × ℝ | |y.1 - ζ.1| < a} := by
    rw [hset]; exact measurableSet_Ioo.prod MeasurableSet.univ
  calc ∫ x, ‖crOp (fun x => S x + σ • antilinearMat (β x)) (lapV ha σ ζ) x‖ ^ 2 ∂cylMeasure
      ≤ ∫ x, Set.indicator {y : ℝ × ℝ | |y.1 - ζ.1| < a}
          (fun _ => 2 * (B * Real.exp (-(σ * (a / 2) ^ 2) / 2)) ^ 2) x ∂cylMeasure := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun x => by positivity) ?_
          (Eventually.of_forall fun x => lap_crOp_bound ha ha' hσ hB0 hB S β ζ hβloc hSloc x)
        refine (integrable_indicator_iff hm).2 (integrableOn_const ?_ )
        rw [hset, lap_meas_strip]; exact ENNReal.ofReal_ne_top
    _ = 2 * a * (2 * (B * Real.exp (-(σ * (a / 2) ^ 2) / 2)) ^ 2) := by
        rw [integral_indicator_const _ hm, smul_eq_mul, Measure.real, hset, lap_meas_strip,
          ENNReal.toReal_ofReal (by linarith)]
        ring

/-- `∫ |v_ζ|² ≥ e^{-σ a²/32} a²/32`. -/
lemma lap_norm_lower {a : ℝ} (ha : 0 < a) (ha' : a ≤ 1 / 4) {σ : ℝ} (hσ : 0 ≤ σ)
    (ζ : ℝ × ℝ) (hζ : 0 ≤ ζ.2 ∧ ζ.2 < 1) :
    Real.exp (-(σ * (a / 8) ^ 2) / 2) ^ 4 * (a / 4 * (a / 8)) ≤
      ∫ x, ‖lapV ha σ ζ x‖ ^ 2 ∂cylMeasure := by
  set e := Real.exp (-(σ * (a / 8) ^ 2) / 2)
  set t₀ : ℝ := if ζ.2 + a / 8 ≤ 1 then ζ.2 else ζ.2 - a / 8
  have ht₀ : 0 ≤ t₀ ∧ t₀ + a / 8 ≤ 1 ∧ t₀ ≤ ζ.2 ∧ ζ.2 ≤ t₀ + a / 8 := by
    simp only [t₀]; split_ifs with h
    · exact ⟨hζ.1, h, le_rfl, by linarith⟩
    · push Not at h; refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  set Box := Set.Ioo (ζ.1 - a / 8) (ζ.1 + a / 8) ×ˢ Set.Ioo t₀ (t₀ + a / 8)
  have hmB : MeasurableSet Box := measurableSet_Ioo.prod measurableSet_Ioo
  have hint : Integrable (fun x => ‖lapV ha σ ζ x‖ ^ 2) cylMeasure := by
    have hv := lapV_test ha ha' σ ζ
    obtain ⟨R, hR⟩ := hv.2.2
    exact lap_integrable (by have := hv.continuous; fun_prop) R fun s t hs => by simp [hR s t hs]
  calc e ^ 4 * (a / 4 * (a / 8)) = ∫ x, Box.indicator (fun _ => e ^ 4) x ∂cylMeasure := by
        rw [integral_indicator_const _ hmB, smul_eq_mul, Measure.real,
          lap_meas_box _ _ _ _ (by linarith) ht₀.1 (by linarith) ht₀.2.1,
          ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith),
          ENNReal.toReal_ofReal (by linarith)]
        ring
    _ ≤ ∫ x, ‖lapV ha σ ζ x‖ ^ 2 ∂cylMeasure := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun x => ?_) hint
          (Eventually.of_forall fun x => ?_)
        · exact Set.indicator_nonneg (fun _ _ => by positivity) x
        · dsimp only
          by_cases hx : x ∈ Box
          · rw [Set.indicator_of_mem hx]
            obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hx
            have hu : |x.1 - ζ.1| ≤ a / 8 := abs_le.2 ⟨by linarith, by linarith⟩
            have hw' : |x.2 - ζ.2| ≤ a / 8 := abs_le.2 ⟨by linarith, by linarith⟩
            have hW : lapW ζ.2 x.2 = x.2 - ζ.2 := by
              have := lapW_eq (c := ζ.2) (t := x.2) (m := 0) (by simp; linarith)
              simpa using this
            have hF : e * e ≤ lapF ha σ ζ x := by
              unfold lapF; rw [hW]
              exact mul_le_mul (lapH_ge ha hσ hu) (lapH_ge ha hσ hw') (by positivity)
                (lapH_nonneg ha σ _)
            have hF0 : 0 ≤ lapF ha σ ζ x := mul_nonneg (lapH_nonneg _ _ _) (lapH_nonneg _ _ _)
            have hE : ‖lapE‖ = 1 := by simp [lapE]
            have hn : ‖lapV ha σ ζ x‖ = lapF ha σ ζ x := by
              rw [lapV, norm_smul, Real.norm_eq_abs, abs_of_nonneg hF0, hE, mul_one]
            rw [hn]
            have := pow_le_pow_left₀ (by positivity) hF 2
            calc e ^ 4 = (e * e) ^ 2 := by ring
              _ ≤ _ := this
          · rw [Set.indicator_of_notMem hx]; positivity

/-- Sections at distinct zeros are pointwise orthogonal. -/
lemma lapV_inner_eq_zero {a : ℝ} (ha : 0 < a) (σ : ℝ) {ζ ξ : ℝ × ℝ} (hne : ζ ≠ ξ)
    (hsep : ∀ m m' : ℤ, |ξ.1 - ζ.1| < 3 * a / 2 → |ξ.2 + m' - (ζ.2 + m)| < 3 * a / 2 → False)
    (x : ℝ × ℝ) : ⟪lapV ha σ ζ x, lapV ha σ ξ x⟫ = 0 := by
  by_cases h1 : lapF ha σ ζ x = 0
  · simp [lapV, h1]
  by_cases h2 : lapF ha σ ξ x = 0
  · simp [lapV, h2]
  exfalso
  obtain ⟨hu, m, hm⟩ := lapF_ne_zero ha σ ζ x h1
  obtain ⟨hu', m', hm'⟩ := lapF_ne_zero ha σ ξ x h2
  refine hsep m m' ?_ ?_
  · calc |ξ.1 - ζ.1| = |(x.1 - ζ.1) - (x.1 - ξ.1)| := by ring_nf
      _ ≤ |x.1 - ζ.1| + |x.1 - ξ.1| := abs_sub _ _
      _ < 3 * a / 2 := by linarith
  · calc |ξ.2 + m' - (ζ.2 + m)| = |(x.2 - ζ.2 - m) - (x.2 - ξ.2 - m')| := by ring_nf
      _ ≤ |x.2 - ζ.2 - m| + |x.2 - ξ.2 - m'| := abs_sub _ _
      _ < 3 * a / 2 := by linarith

end

end CauchyRiemannIndex

/-!
# `L²` norms and inner products of `toLp`
-/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

variable {n : ℕ}

lemma lap_norm_sq_toLp {g : ℝ × ℝ → Vec n} (hg : MemLp g 2 cylMeasure) :
    ‖hg.toLp g‖ ^ 2 = ∫ x, ‖g x‖ ^ 2 ∂cylMeasure := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hg.coeFn_toLp] with x hx
  rw [hx, real_inner_self_eq_norm_sq]

lemma lap_inner_toLp {g : ℝ × ℝ → Vec n} (hg : MemLp g 2 cylMeasure) (h : LpCyl n 2) :
    ⟪h, hg.toLp g⟫ = ∫ x, ⟪h x, g x⟫ ∂cylMeasure := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hg.coeFn_toLp] with x hx
  rw [hx]

end

end CauchyRiemannIndex

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff

noncomputable section

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The triple `(u, ∂ₛu, ∂ₜu)` of a test section. -/
def testTriple {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) : Triple n p :=
  ((hu.memLp (p := p)).toLp u, (hu.memLp_partialS (p := p)).toLp _, (hu.memLp_partialT (p := p)).toLp _)

lemma testTriple_mem {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) :
    testTriple (p := p) hu ∈ testTriples n p :=
  ⟨u, hu, (hu.memLp (p := p)).coeFn_toLp, (hu.memLp_partialS (p := p)).coeFn_toLp,
    (hu.memLp_partialT (p := p)).coeFn_toLp⟩

lemma span_testTriples_subset :
    (Submodule.span ℝ (testTriples n p) : Set (Triple n p)) ⊆ testTriples n p := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx => exact hx
  | zero =>
    refine ⟨0, isTestSection_zero, ?_, ?_, ?_⟩
    · exact Lp.coeFn_zero _ _ _
    · rw [partialS_zero]; exact Lp.coeFn_zero _ _ _
    · rw [partialT_zero]; exact Lp.coeFn_zero _ _ _
  | add x y _ _ hx hy =>
    obtain ⟨u, hu, h1, h2, h3⟩ := hx
    obtain ⟨v, hv, k1, k2, k3⟩ := hy
    refine ⟨u + v, hu.add hv, ?_, ?_, ?_⟩
    · exact (Lp.coeFn_add x.1 y.1).trans (h1.add k1)
    · rw [partialS_add hu hv]; exact (Lp.coeFn_add x.2.1 y.2.1).trans (h2.add k2)
    · rw [partialT_add hu hv]; exact (Lp.coeFn_add x.2.2 y.2.2).trans (h3.add k3)
  | smul c x _ hx =>
    obtain ⟨u, hu, h1, h2, h3⟩ := hx
    refine ⟨c • u, hu.smul c, ?_, ?_, ?_⟩
    · exact (Lp.coeFn_smul c x.1).trans (h1.const_smul c)
    · rw [partialS_smul hu]; exact (Lp.coeFn_smul c x.2.1).trans (h2.const_smul c)
    · rw [partialT_smul hu]; exact (Lp.coeFn_smul c x.2.2).trans (h3.const_smul c)

lemma crApply_ae_crOp (S : ℝ × ℝ → Mat n) {w : Triple n p} {u : ℝ × ℝ → Vec n}
    (h1 : (w.1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] u)
    (h2 : (w.2.1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] partialS u)
    (h3 : (w.2.2 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] partialT u) :
    crApply S w =ᵐ[cylMeasure] crOp S u := by
  filter_upwards [h1, h2, h3] with x e1 e2 e3
  simp only [crApply, crOp, e1, e2, e3]

lemma ofReal_norm_le_w1pNorm {w : Triple n p} {u : ℝ × ℝ → Vec n}
    (h1 : (w.1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] u)
    (h2 : (w.2.1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] partialS u)
    (h3 : (w.2.2 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] partialT u) :
    ENNReal.ofReal ‖w‖ ≤ w1pNorm p u := by
  have e1 : ENNReal.ofReal ‖w.1‖ = eLpNorm u p cylMeasure := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _), eLpNorm_congr_ae h1]
  have e2 : ENNReal.ofReal ‖w.2.1‖ = eLpNorm (partialS u) p cylMeasure := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _), eLpNorm_congr_ae h2]
  have e3 : ENNReal.ofReal ‖w.2.2‖ = eLpNorm (partialT u) p cylMeasure := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _), eLpNorm_congr_ae h3]
  rw [Prod.norm_def, Prod.norm_def, ENNReal.ofReal_max, ENNReal.ofReal_max, e1, e2, e3]
  unfold w1pNorm
  refine max_le ?_ (max_le ?_ ?_)
  · exact le_add_right (le_add_right le_rfl)
  · exact le_add_right (le_add_left le_rfl)
  · exact le_add_left le_rfl

lemma eLpNorm_const_mul_norm_le (g : LpCyl n p) {c : ℝ} (hc : 0 ≤ c) :
    eLpNorm (fun x => c * ‖g x‖) p cylMeasure ≤ ENNReal.ofReal c * ENNReal.ofReal ‖g‖ := by
  rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
  refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall fun x => ?_) p
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc (norm_nonneg _))]

lemma eLpNorm_le_of_pointwise {F : ℝ × ℝ → Vec n} {w : Triple n p} {M MJ : ℝ}
    (hM : 0 ≤ M) (hMJ : 0 ≤ MJ)
    (hF : ∀ᵐ x ∂cylMeasure, ‖F x‖ ≤ 1 * ‖w.2.1 x‖ + MJ * ‖w.2.2 x‖ + M * ‖w.1 x‖) :
    eLpNorm F p cylMeasure ≤ ENNReal.ofReal (1 + MJ + M) * ENNReal.ofReal ‖w‖ := by
  have hp1 : 1 ≤ p := Fact.out
  have m1 : AEStronglyMeasurable (fun x => 1 * ‖w.2.1 x‖) cylMeasure :=
    (Lp.aestronglyMeasurable w.2.1).norm.const_mul 1
  have m2 : AEStronglyMeasurable (fun x => MJ * ‖w.2.2 x‖) cylMeasure :=
    (Lp.aestronglyMeasurable w.2.2).norm.const_mul MJ
  have m3 : AEStronglyMeasurable (fun x => M * ‖w.1 x‖) cylMeasure :=
    (Lp.aestronglyMeasurable w.1).norm.const_mul M
  have n1 : ‖w.2.1‖ ≤ ‖w‖ := (norm_fst_le w.2).trans (norm_snd_le w)
  have n2 : ‖w.2.2‖ ≤ ‖w‖ := (norm_snd_le w.2).trans (norm_snd_le w)
  have n3 : ‖w.1‖ ≤ ‖w‖ := norm_fst_le w
  calc eLpNorm F p cylMeasure
      ≤ eLpNorm (fun x => 1 * ‖w.2.1 x‖ + MJ * ‖w.2.2 x‖ + M * ‖w.1 x‖) p cylMeasure :=
        eLpNorm_mono_ae_real hF
    _ ≤ eLpNorm (fun x => 1 * ‖w.2.1 x‖) p cylMeasure + eLpNorm (fun x => MJ * ‖w.2.2 x‖) p cylMeasure
          + eLpNorm (fun x => M * ‖w.1 x‖) p cylMeasure := by
        refine (eLpNorm_add_le (m1.add m2) m3 hp1).trans ?_
        gcongr
        exact eLpNorm_add_le m1 m2 hp1
    _ ≤ ENNReal.ofReal 1 * ENNReal.ofReal ‖w.2.1‖ + ENNReal.ofReal MJ * ENNReal.ofReal ‖w.2.2‖
          + ENNReal.ofReal M * ENNReal.ofReal ‖w.1‖ := by
        gcongr
        · exact eLpNorm_const_mul_norm_le _ zero_le_one
        · exact eLpNorm_const_mul_norm_le _ hMJ
        · exact eLpNorm_const_mul_norm_le _ hM
    _ ≤ ENNReal.ofReal 1 * ENNReal.ofReal ‖w‖ + ENNReal.ofReal MJ * ENNReal.ofReal ‖w‖
          + ENNReal.ofReal M * ENNReal.ofReal ‖w‖ := by
        gcongr
    _ = ENNReal.ofReal (1 + MJ + M) * ENNReal.ofReal ‖w‖ := by
        rw [ENNReal.ofReal_add (by positivity) hM, ENNReal.ofReal_add zero_le_one hMJ]
        ring

lemma aestronglyMeasurable_crApply (Sinf : ℝ → Mat n) (hc : Continuous Sinf) (w : Triple n p) :
    AEStronglyMeasurable (crApply (fun x : ℝ × ℝ => Sinf x.2) w) cylMeasure := by
  have hJ : AEStronglyMeasurable (fun x => matCLM n (J₀ n) (w.2.2 x)) cylMeasure :=
    (matCLM n (J₀ n)).continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable w.2.2)
  have hS : AEStronglyMeasurable (fun x : ℝ × ℝ => matCLM n (Sinf x.2) (w.1 x)) cylMeasure :=
    Continuous.comp_aestronglyMeasurable₂ (g := fun (A : Vec n →L[ℝ] Vec n) (v : Vec n) => A v)
      (continuous_fst.clm_apply continuous_snd)
      ((continuous_matCLM.comp (hc.comp continuous_snd)).aestronglyMeasurable)
      (Lp.aestronglyMeasurable w.1)
  exact ((Lp.aestronglyMeasurable w.2.1).add hJ).add hS

lemma crApply_sub_ae (S : ℝ × ℝ → Mat n) (w w' : Triple n p) :
    crApply S (w - w') =ᵐ[cylMeasure] crApply S w - crApply S w' := by
  filter_upwards [Lp.coeFn_sub w.1 w'.1, Lp.coeFn_sub w.2.1 w'.2.1,
    Lp.coeFn_sub w.2.2 w'.2.2] with x e1 e2 e3
  change (⇑(w.2.1 - w'.2.1) x + _ + Matrix.toEuclideanLin (S x) (⇑(w.1 - w'.1) x)) = _
  change _ + Matrix.toEuclideanLin (J₀ n) (⇑(w.2.2 - w'.2.2) x) + _ = _
  rw [e1, e2, e3]
  simp only [crApply, Pi.sub_apply, map_sub]
  abel

end

end CauchyRiemannIndex

/-!
# Wendl, Corollary 4.14 (`k = 1`): `D_S` is semi-Fredholm

`D_S` and the restriction `K : W^{1,p} → L^p([-R, R] × S¹)` are bounded operators on the Banach
space `W^{1,p}`. The global estimate (Lemma 4.13) extends from test sections to `W^{1,p}` by
density, `K` is compact by the Rellich milestone, and Lemma 4.12 gives a finite-dimensional
kernel and a closed range.
-/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff

noncomputable section

variable {n : ℕ}

lemma crs_per {β : Type*} {F : ℝ × ℝ → β} (hF : ∀ s t, F (s, t + 1) = F (s, t)) (s t : ℝ) :
    F (s, Int.fract t) = F (s, t) := by
  have hp : Function.Periodic (fun t => F (s, t)) 1 := fun t => hF s t
  have := hp.sub_int_mul_eq (x := t) ⌊t⌋
  rw [mul_one] at this
  exact this

lemma crs_matbound : ∃ B : ℝ, 0 ≤ B ∧ ∀ D : Mat n, (∀ i j, |D i j| ≤ 1) → ‖matCLM n D‖ ≤ B := by
  have hK : IsCompact {D : Mat n | ∀ i j, D i j ∈ Set.Icc (-1 : ℝ) 1} := by
    have e : {D : Mat n | ∀ i j, D i j ∈ Set.Icc (-1 : ℝ) 1} =
        Set.univ.pi (fun _ => Set.univ.pi fun _ => Set.Icc (-1 : ℝ) 1) := by
      ext D
      exact ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
    rw [e]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn continuous_matCLM.continuousOn
  exact ⟨max B 0, le_max_right _ _, fun D hD =>
    (hB D fun i j => Set.mem_Icc.2 (abs_le.1 (hD i j))).trans (le_max_left _ _)⟩

/-- An asymptotic coefficient is bounded. -/
lemma crs_Sbound {S : ℝ × ℝ → Mat n} {Splus Sminus : ℝ → Mat n} (hSp : IsSymLoop Splus)
    (hSm : IsSymLoop Sminus) (hS : IsAsymptoticTo S Splus Sminus) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x (v : Vec n), ‖Matrix.toEuclideanLin (S x) v‖ ≤ M * ‖v‖ := by
  obtain ⟨Mp, hMp0, hMp⟩ := exists_bound_loop Splus hSp.1 hSp.2.1
  obtain ⟨Mm, hMm0, hMm⟩ := exists_bound_loop Sminus hSm.1 hSm.2.1
  obtain ⟨B, hB0, hB⟩ := crs_matbound (n := n)
  obtain ⟨R, hR⟩ := hS.2.2 1 one_pos
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc :
    IsCompact (Set.Icc (-|R|) |R| ×ˢ Set.Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
      (continuous_matCLM.comp hS.1).continuousOn
  refine ⟨max C 0 + B + Mp + Mm, by positivity, fun x v => ?_⟩
  have hv := norm_nonneg v
  have hsplit : ∀ T : Mat n, Matrix.toEuclideanLin (S x) v =
      matCLM n (S x - T) v + Matrix.toEuclideanLin T v := by
    intro T
    rw [matCLM_apply, ← LinearMap.add_apply, ← map_add, sub_add_cancel]
  by_cases h1 : R ≤ x.1
  · rw [hsplit (Splus x.2)]
    have hD : ‖matCLM n (S x - Splus x.2)‖ ≤ B :=
      hB _ fun i j => by simpa using (hR x.1 x.2 i j).1 h1
    calc ‖matCLM n (S x - Splus x.2) v + Matrix.toEuclideanLin (Splus x.2) v‖
        ≤ ‖matCLM n (S x - Splus x.2)‖ * ‖v‖ + Mp * ‖v‖ :=
          (norm_add_le _ _).trans (add_le_add ((matCLM n _).le_opNorm v) (hMp _ v))
      _ ≤ B * ‖v‖ + Mp * ‖v‖ := by gcongr
      _ ≤ (max C 0 + B + Mp + Mm) * ‖v‖ := by
          nlinarith [le_max_right C 0]
  by_cases h2 : x.1 ≤ -R
  · rw [hsplit (Sminus x.2)]
    have hD : ‖matCLM n (S x - Sminus x.2)‖ ≤ B :=
      hB _ fun i j => by simpa using (hR x.1 x.2 i j).2 h2
    calc ‖matCLM n (S x - Sminus x.2) v + Matrix.toEuclideanLin (Sminus x.2) v‖
        ≤ ‖matCLM n (S x - Sminus x.2)‖ * ‖v‖ + Mm * ‖v‖ :=
          (norm_add_le _ _).trans (add_le_add ((matCLM n _).le_opNorm v) (hMm _ v))
      _ ≤ B * ‖v‖ + Mm * ‖v‖ := by gcongr
      _ ≤ (max C 0 + B + Mp + Mm) * ‖v‖ := by
          nlinarith [le_max_right C 0]
  push_neg at h1 h2
  have hx : (x.1, Int.fract x.2) ∈ Set.Icc (-|R|) |R| ×ˢ Set.Icc (0 : ℝ) 1 := by
    refine Set.mk_mem_prod ⟨?_, ?_⟩ ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
    · have := le_abs_self R; linarith
    · have := le_abs_self R; linarith
  have hCx := hC _ hx
  have e : S (x.1, Int.fract x.2) = S x := crs_per hS.2.1 x.1 x.2
  simp only [Function.comp, e] at hCx
  rw [← matCLM_apply]
  calc ‖matCLM n (S x) v‖ ≤ ‖matCLM n (S x)‖ * ‖v‖ := (matCLM n _).le_opNorm v
    _ ≤ max C 0 * ‖v‖ := by gcongr; exact hCx.trans (le_max_left _ _)
    _ ≤ (max C 0 + B + Mp + Mm) * ‖v‖ := by nlinarith

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

lemma crs_aesm (S : ℝ × ℝ → Mat n) (hc : Continuous S) (w : Triple n p) :
    AEStronglyMeasurable (crApply S w) cylMeasure := by
  have hJ : AEStronglyMeasurable (fun x => matCLM n (J₀ n) (w.2.2 x)) cylMeasure :=
    (matCLM n (J₀ n)).continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable w.2.2)
  have hS : AEStronglyMeasurable (fun x : ℝ × ℝ => matCLM n (S x) (w.1 x)) cylMeasure :=
    Continuous.comp_aestronglyMeasurable₂ (g := fun (A : Vec n →L[ℝ] Vec n) (v : Vec n) => A v)
      (continuous_fst.clm_apply continuous_snd)
      ((continuous_matCLM.comp hc).aestronglyMeasurable)
      (Lp.aestronglyMeasurable w.1)
  exact ((Lp.aestronglyMeasurable w.2.1).add hJ).add hS

/-- The operator-norm constant of `D_S` on triples. -/
def crsC (S : ℝ × ℝ → Mat n)
    (hb : ∃ M : ℝ, 0 ≤ M ∧ ∀ x (v : Vec n), ‖Matrix.toEuclideanLin (S x) v‖ ≤ M * ‖v‖) : ℝ :=
  1 + ‖matCLM n (J₀ n)‖ + hb.choose

lemma crsC_nonneg (S : ℝ × ℝ → Mat n)
    (hb : ∃ M : ℝ, 0 ≤ M ∧ ∀ x (v : Vec n), ‖Matrix.toEuclideanLin (S x) v‖ ≤ M * ‖v‖) :
    0 ≤ crsC S hb := by
  unfold crsC
  have := hb.choose_spec.1
  positivity

lemma crs_eLpNorm_le (S : ℝ × ℝ → Mat n)
    (hb : ∃ M : ℝ, 0 ≤ M ∧ ∀ x (v : Vec n), ‖Matrix.toEuclideanLin (S x) v‖ ≤ M * ‖v‖)
    (w : Triple n p) :
    eLpNorm (crApply S w) p cylMeasure ≤ ENNReal.ofReal (crsC S hb) * ENNReal.ofReal ‖w‖ := by
  unfold crsC
  refine eLpNorm_le_of_pointwise hb.choose_spec.1 (norm_nonneg _) (Eventually.of_forall fun x => ?_)
  unfold crApply
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · rw [one_mul]
  · rw [← matCLM_apply]; exact (matCLM n (J₀ n)).le_opNorm _
  · exact hb.choose_spec.2 x _

lemma crs_memLp (S : ℝ × ℝ → Mat n) (hc : Continuous S)
    (hb : ∃ M : ℝ, 0 ≤ M ∧ ∀ x (v : Vec n), ‖Matrix.toEuclideanLin (S x) v‖ ≤ M * ‖v‖)
    (w : Triple n p) : MemLp (crApply S w) p cylMeasure :=
  ⟨crs_aesm S hc w, (crs_eLpNorm_le S hb w).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)⟩

lemma crs_add_ae (S : ℝ × ℝ → Mat n) (w w' : Triple n p) :
    crApply S (w + w') =ᵐ[cylMeasure] crApply S w + crApply S w' := by
  filter_upwards [Lp.coeFn_add w.1 w'.1, Lp.coeFn_add w.2.1 w'.2.1,
    Lp.coeFn_add w.2.2 w'.2.2] with x e1 e2 e3
  change (⇑(w.2.1 + w'.2.1) x + _ + Matrix.toEuclideanLin (S x) (⇑(w.1 + w'.1) x)) = _
  change _ + Matrix.toEuclideanLin (J₀ n) (⇑(w.2.2 + w'.2.2) x) + _ = _
  rw [e1, e2, e3]
  simp only [crApply, Pi.add_apply, map_add]
  abel

lemma crs_smul_ae (S : ℝ × ℝ → Mat n) (c : ℝ) (w : Triple n p) :
    crApply S (c • w) =ᵐ[cylMeasure] c • crApply S w := by
  filter_upwards [Lp.coeFn_smul c w.1, Lp.coeFn_smul c w.2.1,
    Lp.coeFn_smul c w.2.2] with x e1 e2 e3
  change (⇑(c • w.2.1) x + _ + Matrix.toEuclideanLin (S x) (⇑(c • w.1) x)) = _
  change _ + Matrix.toEuclideanLin (J₀ n) (⇑(c • w.2.2) x) + _ = _
  rw [e1, e2, e3]
  simp only [crApply, Pi.smul_apply, map_smul, smul_add]

/-- `D_S` as a bounded operator `L^p × L^p × L^p → L^p`. -/
def crsT (S : ℝ × ℝ → Mat n) (hc : Continuous S)
    (hb : ∃ M : ℝ, 0 ≤ M ∧ ∀ x (v : Vec n), ‖Matrix.toEuclideanLin (S x) v‖ ≤ M * ‖v‖) :
    Triple n p →L[ℝ] LpCyl n p :=
  LinearMap.mkContinuous
    { toFun := fun w => (crs_memLp S hc hb w).toLp _
      map_add' := fun w w' => by
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (crs_memLp S hc hb (w + w')),
          Lp.coeFn_add ((crs_memLp S hc hb w).toLp _) ((crs_memLp S hc hb w').toLp _),
          MemLp.coeFn_toLp (crs_memLp S hc hb w), MemLp.coeFn_toLp (crs_memLp S hc hb w'),
          crs_add_ae S w w'] with x h1 h2 h3 h4 h5
        rw [h1, h2, Pi.add_apply, h3, h4, h5, Pi.add_apply]
      map_smul' := fun c w => by
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (crs_memLp S hc hb (c • w)),
          Lp.coeFn_smul c ((crs_memLp S hc hb w).toLp _),
          MemLp.coeFn_toLp (crs_memLp S hc hb w), crs_smul_ae S c w] with x h1 h2 h3 h4
        rw [RingHom.id_apply, h1, h2, Pi.smul_apply, h3, h4, Pi.smul_apply] }
    (crsC S hb) (fun w => by
      change ‖(crs_memLp S hc hb w).toLp _‖ ≤ _
      rw [Lp.norm_toLp]
      refine ENNReal.toReal_le_of_le_ofReal (mul_nonneg (crsC_nonneg S hb) (norm_nonneg _)) ?_
      rw [ENNReal.ofReal_mul (crsC_nonneg S hb)]
      exact crs_eLpNorm_le S hb w)

lemma crsT_ae (S : ℝ × ℝ → Mat n) (hc : Continuous S)
    (hb : ∃ M : ℝ, 0 ≤ M ∧ ∀ x (v : Vec n), ‖Matrix.toEuclideanLin (S x) v‖ ≤ M * ‖v‖)
    (w : Triple n p) : (crsT S hc hb w : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] crApply S w :=
  MemLp.coeFn_toLp (crs_memLp S hc hb w)

variable (n p) in
/-- The strip `[-R, R] × S¹` (as a subset of the fundamental domain). -/
abbrev crsμ (R : ℝ) : Measure (ℝ × ℝ) := cylMeasure.restrict (Set.Icc (-R) R ×ˢ Set.univ)

variable (n p) in
/-- `(u, v, w) ↦ u|_{[-R, R] × S¹}`. -/
def crsK (R : ℝ) : Triple n p →L[ℝ] Lp (Vec n) p (crsμ R) :=
  (LpToLpRestrictCLM (ℝ × ℝ) (Vec n) ℝ cylMeasure p (Set.Icc (-R) R ×ˢ Set.univ)).comp
    (ContinuousLinearMap.fst ℝ (LpCyl n p) (LpCyl n p × LpCyl n p))

lemma crsK_ae (R : ℝ) (w : Triple n p) :
    (crsK n p R w : ℝ × ℝ → Vec n) =ᵐ[crsμ R] w.1 :=
  LpToLpRestrictCLM_coeFn ℝ _ w.1

/-- `w1pNorm u ≤ 3 ‖(u, ∂ₛu, ∂ₜu)‖`. -/
lemma crs_w1p_le {w : Triple n p} {u : ℝ × ℝ → Vec n}
    (h1 : (w.1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] u)
    (h2 : (w.2.1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] partialS u)
    (h3 : (w.2.2 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] partialT u) :
    w1pNorm p u ≤ ENNReal.ofReal (3 * ‖w‖) := by
  have e1 : ENNReal.ofReal ‖w.1‖ = eLpNorm u p cylMeasure := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _), eLpNorm_congr_ae h1]
  have e2 : ENNReal.ofReal ‖w.2.1‖ = eLpNorm (partialS u) p cylMeasure := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _), eLpNorm_congr_ae h2]
  have e3 : ENNReal.ofReal ‖w.2.2‖ = eLpNorm (partialT u) p cylMeasure := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _), eLpNorm_congr_ae h3]
  have n1 : ‖w.2.1‖ ≤ ‖w‖ := (norm_fst_le w.2).trans (norm_snd_le w)
  have n2 : ‖w.2.2‖ ≤ ‖w‖ := (norm_snd_le w.2).trans (norm_snd_le w)
  have n3 : ‖w.1‖ ≤ ‖w‖ := norm_fst_le w
  unfold w1pNorm
  rw [← e1, ← e2, ← e3, ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _),
    ← ENNReal.ofReal_add (by positivity) (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- The global estimate on the closed span of test triples. -/
lemma crs_estimate (S : ℝ × ℝ → Mat n) (hc : Continuous S)
    (hb : ∃ M : ℝ, 0 ≤ M ∧ ∀ x (v : Vec n), ‖Matrix.toEuclideanLin (S x) v‖ ≤ M * ‖v‖)
    (R : ℝ) (c : ℝ≥0)
    (hest : ∀ u : ℝ × ℝ → Vec n, IsTestSection u →
      w1pNorm p u ≤ c * eLpNorm (crOp S u) p cylMeasure + c * eLpNorm u p (crsμ R)) :
    ∀ w ∈ W1p p n, ‖w‖ ≤ c * ‖crsT S hc hb w‖ + c * ‖crsK n p R w‖ := by
  have htest : ∀ w ∈ testTriples n p, ‖w‖ ≤ c * ‖crsT S hc hb w‖ + c * ‖crsK n p R w‖ := by
    rintro w ⟨u, hu, h1, h2, h3⟩
    have eT : ENNReal.ofReal ‖crsT S hc hb w‖ = eLpNorm (crOp S u) p cylMeasure := by
      rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _),
        eLpNorm_congr_ae ((crsT_ae S hc hb w).trans (crApply_ae_crOp S h1 h2 h3))]
    have eK : ENNReal.ofReal ‖crsK n p R w‖ = eLpNorm u p (crsμ R) := by
      rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _),
        eLpNorm_congr_ae ((crsK_ae R w).trans (ae_restrict_of_ae h1))]
    have h := (ofReal_norm_le_w1pNorm h1 h2 h3).trans (hest u hu)
    have h' : ENNReal.ofReal ‖w‖ ≤
        ENNReal.ofReal ((c : ℝ) * ‖crsT S hc hb w‖ + (c : ℝ) * ‖crsK n p R w‖) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul c.coe_nonneg,
        ENNReal.ofReal_mul c.coe_nonneg, eT, eK, ENNReal.ofReal_coe_nnreal]
      exact h
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h'
  have hcl : IsClosed {w : Triple n p | ‖w‖ ≤ c * ‖crsT S hc hb w‖ + c * ‖crsK n p R w‖} :=
    isClosed_le continuous_norm
      ((continuous_const.mul (crsT S hc hb).continuous.norm).add
        (continuous_const.mul (crsK n p R).continuous.norm))
  intro w hw
  have hsub : (W1p p n : Set (Triple n p)) ⊆
      {w : Triple n p | ‖w‖ ≤ c * ‖crsT S hc hb w‖ + c * ‖crsK n p R w‖} := by
    unfold W1p
    rw [Submodule.topologicalClosure_coe]
    exact closure_minimal (fun w hw => htest w (span_testTriples_subset hw)) hcl
  exact hsub hw

end

end CauchyRiemannIndex

/-!
# Wendl, Proposition 5.24 (kernel lower bound), `n = 1`, `p = 2`

For large `σ` the adjoint estimate makes `D_σ` solvable with `‖w‖₂ ≤ ‖f‖₂`. Correcting the
Gaussian sections `v_ζ` by solutions `w_ζ` of `D_σ w_ζ = D_σ v_ζ` gives kernel elements
`v_ζ - w_ζ`; they are independent because the `v_ζ` are orthogonal with `‖v_ζ‖₂` much larger
than `‖w_ζ‖₂`.
-/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

lemma lap_per_int_gen {X : Type*} {F : ℝ × ℝ → X} (hper : ∀ s t, F (s, t + 1) = F (s, t))
    (s t : ℝ) (m : ℤ) : F (s, t + m) = F (s, t) := by
  have hp : Function.Periodic (fun t => F (s, t)) 1 := fun t => hper s t
  have := hp.int_mul m t
  simpa [mul_one, add_comm] using this

lemma lap_beta_bounded (β : ℝ × ℝ → ℂ) (hβc : Continuous β)
    (hβper : ∀ s t, β (s, t + 1) = β (s, t))
    (hβends : ∃ (R c : ℝ), 0 < c ∧ ∀ s t, R ≤ |s| → c ≤ ‖β (s, t)‖ ∧ ‖β (s, t)‖ ≤ 1 / c) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖β x‖ ≤ M := by
  obtain ⟨R, c, hc, hends⟩ := hβends
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc :
    IsCompact (Set.Icc (-|R|) |R| ×ˢ Set.Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
      hβc.continuousOn
  refine ⟨max C 0 + 1 / c, by positivity, fun x => ?_⟩
  by_cases hs : |x.1| ≤ |R|
  · have hx : (x.1, Int.fract x.2) ∈ Set.Icc (-|R|) |R| ×ˢ Set.Icc (0 : ℝ) 1 :=
      Set.mk_mem_prod (abs_le.1 hs) ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
    have e : β (x.1, Int.fract x.2) = β x := crs_per hβper x.1 x.2
    have := hC _ hx
    rw [e] at this
    have : 0 ≤ 1 / c := by positivity
    linarith [le_max_left C 0]
  · have := (hends x.1 x.2 ((le_abs_self R).trans (not_le.1 hs).le)).2
    linarith [le_max_right C 0]

lemma lap_alm_continuous {β : ℝ × ℝ → ℂ} (hβc : Continuous β) :
    Continuous fun x => antilinearMat (β x) :=
  (LinearMap.continuous_of_finiteDimensional almL).comp hβc

theorem large_antilinear_kernel_ge_aux (Splus Sminus : ℝ → Mat 1) (hSplus : IsSymLoop Splus)
    (hSminus : IsSymLoop Sminus) (hplus : IsNondegenerate Splus) (hminus : IsNondegenerate Sminus)
    (S : ℝ × ℝ → Mat 1) (hS : IsAsymptoticTo S Splus Sminus)
    (β : ℝ × ℝ → ℂ) (hβ : ContDiff ℝ ∞ β) (hβper : ∀ s t, β (s, t + 1) = β (s, t))
    (hβC1 : ∃ C : ℝ, ∀ x, ‖fderiv ℝ β x‖ ≤ C)
    (hβends : ∃ (R c : ℝ), 0 < c ∧ ∀ s t, R ≤ |s| → c ≤ ‖β (s, t)‖ ∧ ‖β (s, t)‖ ≤ 1 / c)
    (Zplus Zminus : Finset (ℝ × ℝ)) (hZ : ∀ ζ ∈ Zplus ∪ Zminus, 0 ≤ ζ.2 ∧ ζ.2 < 1)
    (hdisj : Disjoint Zplus Zminus)
    (hzero : ∀ x : ℝ × ℝ, β x = 0 ↔ ∃ ζ ∈ Zplus ∪ Zminus, ∃ m : ℤ, x = (ζ.1, ζ.2 + m))
    (r : ℝ) (hr : 0 < r)
    (hplusZ : ∀ ζ ∈ Zplus, ∀ z : ℂ, ‖z‖ < r →
      β (ζ.1 + z.re, ζ.2 + z.im) = z ∧ S (ζ.1 + z.re, ζ.2 + z.im) = 0)
    (hminusZ : ∀ ζ ∈ Zminus, ∀ z : ℂ, ‖z‖ < r →
      β (ζ.1 + z.re, ζ.2 + z.im) = (starRingEnd ℂ) z ∧ S (ζ.1 + z.re, ζ.2 + z.im) = 0)
    (hZminus : Zminus = ∅) :
    ∃ σ₀ : ℝ, ∀ σ ≥ σ₀,
      ∃ v : Fin Zplus.card → crKernel 2 (fun x => S x + σ • antilinearMat (β x)),
        LinearIndependent ℝ v := by
  -- the adjoint estimate
  subst hZminus
  simp only [Finset.union_empty] at hZ hzero
  obtain ⟨σ₁, hest⟩ := large_antilinear_adjoint_estimate Splus Sminus hSplus hSminus S hS β
    hβ hβper hβC1 hβends Zplus hZ hzero r hr hplusZ
  -- the box size
  set a : ℝ := min r 1 / 4 with ha_def
  have ha : 0 < a := by positivity
  have ha' : a ≤ 1 / 4 := by have := min_le_right r 1; linarith
  have ha4 : 4 * a ≤ r := by have := min_le_left r 1; linarith
  have hplusβ : ∀ ζ ∈ Zplus, ∀ z : ℂ, ‖z‖ < r → β (ζ.1 + z.re, ζ.2 + z.im) = z :=
    fun ζ hζ z hz => (hplusZ ζ hζ z hz).1
  have hβloc : ∀ ζ ∈ Zplus, ∀ m : ℤ, ∀ u v : ℝ, |u| < a → |v| < a →
      β (ζ.1 + u, ζ.2 + m + v) = ⟨u, v⟩ := by
    intro ζ hζ m u v hu hv
    exact lap_local hβper hplusβ hζ m (by have := lap_norm_lt hu hv; linarith)
  have hSloc : ∀ ζ ∈ Zplus, ∀ m : ℤ, ∀ u v : ℝ, |u| < a → |v| < a →
      S (ζ.1 + u, ζ.2 + m + v) = 0 := by
    intro ζ hζ m u v hu hv
    have hn : ‖(⟨u, v⟩ : ℂ)‖ < r := by have := lap_norm_lt hu hv; linarith
    have h := (hplusZ ζ hζ ⟨u, v⟩ hn).2
    rw [show ζ.2 + m + v = ζ.2 + v + m by ring, lap_per_int_gen hS.2.1]
    exact h
  have hsep : ∀ ζ ∈ Zplus, ∀ ξ ∈ Zplus, ζ ≠ ξ → ∀ m m' : ℤ, |ξ.1 - ζ.1| < 3 * a / 2 →
      |ξ.2 + m' - (ζ.2 + m)| < 3 * a / 2 → False := by
    intro ζ hζ ξ hξ hne m m' h1 h2
    exact hne (lap_sep (m := m) (m' := m') hβper hZ hzero hplusβ hζ hξ (by linarith)
      (by linarith)).1
  -- constants
  obtain ⟨Bψ, hBψ0, hBψ⟩ := lapPsi_deriv_bounded ha
  obtain ⟨Mβ, hMβ0, hMβ⟩ := lap_beta_bounded β hβ.continuous hβper hβends
  set N := Zplus.card
  set K₀ : ℝ := (N : ℝ) ^ 2 * (2 * a * (2 * Bψ ^ 2))
  set c₀ : ℝ := a / 4 * (a / 8)
  have hc₀ : 0 < c₀ := by positivity
  have hK₀ : 0 ≤ K₀ := by positivity
  set D : ℝ := 7 * a ^ 2 / 32
  have hD : 0 < D := by positivity
  set q : ℝ := c₀ / (K₀ + 1)
  have hq : 0 < q := by positivity
  set σ₂ : ℝ := -Real.log q / D
  refine ⟨max σ₁ (max σ₂ 0), fun σ hσ => ?_⟩
  have hσ₁ : σ₁ ≤ σ := (le_max_left _ _).trans hσ
  have hσ₂ : σ₂ ≤ σ := ((le_max_left _ _).trans (le_max_right _ _)).trans hσ
  have hσ0 : 0 ≤ σ := ((le_max_right _ _).trans (le_max_right _ _)).trans hσ
  set T : ℝ × ℝ → Mat 1 := fun x => S x + σ • antilinearMat (β x) with hTdef
  have hTc : Continuous T := hS.1.add ((lap_alm_continuous hβ.continuous).const_smul σ)
  -- solvability with `‖w‖ ≤ ‖f‖`
  have hBb : ∃ M : ℝ, 0 ≤ M ∧ ∀ x (v : Vec 1),
      ‖Matrix.toEuclideanLin (σ • antilinearMat (β x)) v‖ ≤ M * ‖v‖ := by
    refine ⟨σ * Mβ, by positivity, fun x v => ?_⟩
    rw [map_smul, LinearMap.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg hσ0]
    have h := lap_norm_alm_sq (β x) v
    have h' : ‖Matrix.toEuclideanLin (antilinearMat (β x)) v‖ = ‖β x‖ * ‖v‖ := by
      rw [← Real.sqrt_sq (norm_nonneg _), h, ← mul_pow, Real.sqrt_sq (by positivity)]
    rw [h', ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hMβ x) hσ0) (norm_nonneg _)
  have hsolve := exists_solution_of_adjoint_estimate 1 Splus Sminus hSplus hSminus S hS
    (fun x => σ • antilinearMat (β x)) ((lap_alm_continuous hβ.continuous).const_smul σ) hBb 1
    zero_le_one (fun φ hφ => by rw [one_mul]; exact hest σ hσ₁ φ hφ)
  rw [Real.sqrt_one] at hsolve
  -- the sections
  have hv : ∀ ζ : Zplus, IsTestSection (lapV ha σ ζ.1) := fun ζ => lapV_test ha ha' σ ζ.1
  have hcrc : ∀ ζ : Zplus, MemLp (crOp T (lapV ha σ ζ.1)) 2 cylMeasure := by
    intro ζ
    obtain ⟨R, hR⟩ := (hv ζ).2.2
    refine memLp_of_vanish _ ?_ R fun s t hs => ?_
    · exact (((hv ζ).continuous_partialS).add ((matCLM 1 (J₀ 1)).continuous.comp
        (hv ζ).continuous_partialT)).add ((continuous_matCLM.comp hTc).clm_apply (hv ζ).continuous)
    · simp [crOp, hR s t hs, partialS_eq_zero R hR hs, partialT_eq_zero R hR hs]
  set f : Zplus → LpCyl 1 2 := fun ζ => (hcrc ζ).toLp _
  choose w hwW hwf hwn using fun ζ => hsolve (f ζ)
  set V : Zplus → LpCyl 1 2 := fun ζ => ((hv ζ).memLp (p := 2)).toLp _
  set k : Zplus → Triple 1 2 := fun ζ => testTriple (p := 2) (hv ζ) - w ζ
  have hkW : ∀ ζ, k ζ ∈ W1p 2 1 := by
    intro ζ
    refine Submodule.sub_mem _ ?_ (hwW ζ)
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span (testTriple_mem (hv ζ)))
  have hkker : ∀ ζ, k ζ ∈ crKernel 2 T := by
    intro ζ
    refine Submodule.subset_span ⟨hkW ζ, ?_⟩
    have h1 : crApply T (testTriple (p := 2) (hv ζ)) =ᵐ[cylMeasure] crOp T (lapV ha σ ζ.1) :=
      crApply_ae_crOp T ((hv ζ).memLp (p := 2)).coeFn_toLp
        ((hv ζ).memLp_partialS (p := 2)).coeFn_toLp ((hv ζ).memLp_partialT (p := 2)).coeFn_toLp
    filter_upwards [crApply_sub_ae T (testTriple (p := 2) (hv ζ)) (w ζ), h1, hwf ζ,
      (hcrc ζ).coeFn_toLp] with x e1 e2 e3 e4
    rw [e1, Pi.sub_apply, e2, e3, e4, Pi.zero_apply, sub_self]
  -- norms
  set E : ℝ := Real.exp (-(σ * (a / 2) ^ 2) / 2)
  set e : ℝ := Real.exp (-(σ * (a / 8) ^ 2) / 2)
  have hfn : ∀ ζ, ‖f ζ‖ ^ 2 ≤ 2 * a * (2 * (Bψ * E) ^ 2) := by
    intro ζ
    rw [lap_norm_sq_toLp]
    exact lap_crOp_integral ha ha' hσ0 hBψ0 hBψ S β ζ.1 (hβloc ζ.1 ζ.2) (hSloc ζ.1 ζ.2)
  have hVn : ∀ ζ, e ^ 4 * c₀ ≤ ‖V ζ‖ ^ 2 := by
    intro ζ
    rw [lap_norm_sq_toLp]
    exact lap_norm_lower ha ha' hσ0 ζ.1 (hZ ζ.1 ζ.2)
  have hVV : ∀ ζ ξ : Zplus, ζ ≠ ξ → ⟪V ξ, V ζ⟫ = 0 := by
    intro ζ ξ hne
    rw [lap_inner_toLp]
    have : (fun x => ⟪V ξ x, lapV ha σ ζ.1 x⟫) =ᵐ[cylMeasure] fun _ => 0 := by
      filter_upwards [((hv ξ).memLp (p := 2)).coeFn_toLp] with x hx
      rw [hx, real_inner_comm]
      exact lapV_inner_eq_zero ha σ (fun h => hne (Subtype.ext h))
        (hsep ζ.1 ζ.2 ξ.1 ξ.2 (fun h => hne (Subtype.ext h))) x
    rw [integral_congr_ae this, integral_zero]
  -- the smallness condition
  have hsmall : (N : ℝ) ^ 2 * (2 * a * (2 * (Bψ * E) ^ 2)) < e ^ 4 * c₀ := by
    have hE2 : E ^ 2 = e ^ 4 * Real.exp (-(D * σ)) := by
      simp only [E, e, D]
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1; push_cast; ring
    have hexp : Real.exp (-(D * σ)) ≤ q := by
      rw [← Real.exp_log hq, Real.exp_le_exp]
      have : -Real.log q / D ≤ σ := hσ₂
      rw [div_le_iff₀ hD] at this
      linarith
    have he4 : 0 < e ^ 4 := by positivity
    calc (N : ℝ) ^ 2 * (2 * a * (2 * (Bψ * E) ^ 2)) = K₀ * E ^ 2 := by
          simp only [K₀]; ring
      _ = K₀ * Real.exp (-(D * σ)) * e ^ 4 := by rw [hE2]; ring
      _ ≤ K₀ * q * e ^ 4 := by gcongr
      _ < c₀ * e ^ 4 := by
          apply mul_lt_mul_of_pos_right _ he4
          simp only [q]
          rw [mul_div_assoc']
          rw [div_lt_iff₀ (by positivity)]
          nlinarith
      _ = e ^ 4 * c₀ := mul_comm _ _
  -- the family
  set ε := Real.sqrt (2 * a * (2 * (Bψ * E) ^ 2))
  have hwε : ∀ ζ, ‖(w ζ).1‖ ≤ ε := fun ζ => by
    have := hwn ζ
    rw [one_mul] at this
    exact this.trans ((le_abs_self _).trans (Real.abs_le_sqrt (hfn ζ)))
  let eqv := Zplus.equivFin
  refine ⟨fun i => ⟨k (eqv.symm i), hkker _⟩, ?_⟩
  have hind := linearIndependent_sub_of_orthogonal V (fun ζ => (w ζ).1) (e ^ 4 * c₀) ε hVV hVn hwε (by
    rw [Fintype.card_coe, Real.sq_sqrt (by positivity)]; exact hsmall)
  have hind' := (linearIndependent_equiv eqv.symm).2 hind
  refine LinearIndependent.of_comp ((LinearMap.fst ℝ (LpCyl 1 2) (LpCyl 1 2 × LpCyl 1 2)).comp
    (crKernel 2 T).subtype) ?_
  have hfun : ((LinearMap.fst ℝ (LpCyl 1 2) (LpCyl 1 2 × LpCyl 1 2)).comp
      (crKernel 2 T).subtype ∘ fun i => (⟨k (eqv.symm i), hkker _⟩ : crKernel 2 T)) =
      (fun ζ => V ζ - (w ζ).1) ∘ eqv.symm := by
    funext i
    rfl
  rw [hfun]
  exact hind'

end

end CauchyRiemannIndex

open CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

theorem solution (Splus Sminus : ℝ → Mat 1) (hSplus : IsSymLoop Splus)
    (hSminus : IsSymLoop Sminus) (hplus : IsNondegenerate Splus) (hminus : IsNondegenerate Sminus)
    (S : ℝ × ℝ → Mat 1) (hS : IsAsymptoticTo S Splus Sminus)
    (β : ℝ × ℝ → ℂ) (hβ : ContDiff ℝ ∞ β) (hβper : ∀ s t, β (s, t + 1) = β (s, t))
    (hβC1 : ∃ C : ℝ, ∀ x, ‖fderiv ℝ β x‖ ≤ C)
    (hβends : ∃ (R c : ℝ), 0 < c ∧ ∀ s t, R ≤ |s| → c ≤ ‖β (s, t)‖ ∧ ‖β (s, t)‖ ≤ 1 / c)
    (Zplus Zminus : Finset (ℝ × ℝ)) (hZ : ∀ ζ ∈ Zplus ∪ Zminus, 0 ≤ ζ.2 ∧ ζ.2 < 1)
    (hdisj : Disjoint Zplus Zminus)
    (hzero : ∀ x : ℝ × ℝ, β x = 0 ↔ ∃ ζ ∈ Zplus ∪ Zminus, ∃ m : ℤ, x = (ζ.1, ζ.2 + m))
    (r : ℝ) (hr : 0 < r)
    (hplusZ : ∀ ζ ∈ Zplus, ∀ z : ℂ, ‖z‖ < r →
      β (ζ.1 + z.re, ζ.2 + z.im) = z ∧ S (ζ.1 + z.re, ζ.2 + z.im) = 0)
    (hminusZ : ∀ ζ ∈ Zminus, ∀ z : ℂ, ‖z‖ < r →
      β (ζ.1 + z.re, ζ.2 + z.im) = (starRingEnd ℂ) z ∧ S (ζ.1 + z.re, ζ.2 + z.im) = 0)
    (hZminus : Zminus = ∅) :
    ∃ σ₀ : ℝ, ∀ σ ≥ σ₀,
      ∃ v : Fin Zplus.card → crKernel 2 (fun x => S x + σ • antilinearMat (β x)),
        LinearIndependent ℝ v :=
  large_antilinear_kernel_ge_aux Splus Sminus hSplus hSminus hplus hminus S hS β hβ hβper hβC1 hβends Zplus Zminus hZ hdisj hzero r hr hplusZ hminusZ hZminus
