-- Prove2me | solution 1 for CauchyRiemannIndex.loopOp_inner_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T16:11:07.830686+00:00
-- url     : https://prove2.me/submissions/b59735cc-65fa-4f45-8915-ea8c25bcf940

import Mathlib
import Definitions.Def_FiniteEnergyPlane_Asymptotics

set_option linter.all false

section HD_a

/-! Global existence for linear ODEs `x' = L t (x t)` with bounded coefficients (Picard series). -/

open scoped Topology
open Set Filter

namespace HDecay

lemma abs_integral_abs_pow (k : ℕ) (t : ℝ) :
    |∫ τ in (0:ℝ)..t, |τ| ^ k| = |t| ^ (k + 1) / (k + 1) := by
  rcases le_total 0 t with ht | ht
  · have : ∫ τ in (0:ℝ)..t, |τ| ^ k = ∫ τ in (0:ℝ)..t, τ ^ k := by
      refine intervalIntegral.integral_congr (fun τ hτ => ?_)
      rw [uIcc_of_le ht] at hτ
      simp [abs_of_nonneg hτ.1]
    rw [this, integral_pow, abs_of_nonneg ht]
    simp only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true, zero_pow,
      sub_zero]
    rw [abs_of_nonneg (by positivity)]
  · have h1 : ∫ τ in (0:ℝ)..t, |τ| ^ k = -∫ τ in (0:ℝ)..(-t), τ ^ k := by
      rw [intervalIntegral.integral_symm]
      have := intervalIntegral.integral_comp_neg (a := (0:ℝ)) (b := -t) (fun τ => |τ| ^ k)
      simp only [neg_zero, neg_neg, abs_neg] at this
      rw [← this]
      congr 1
      refine intervalIntegral.integral_congr (fun τ hτ => ?_)
      rw [uIcc_of_le (by linarith)] at hτ
      simp [abs_of_nonneg hτ.1]
    rw [h1, integral_pow, abs_of_nonpos ht]
    simp only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true, zero_pow,
      sub_zero, abs_neg]
    rw [abs_of_nonneg (by have : 0 ≤ -t := by linarith
                          positivity)]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Picard iterates. -/
noncomputable def pic (L : ℝ → E →L[ℝ] E) (x0 : E) : ℕ → ℝ → E
  | 0 => fun _ => x0
  | k + 1 => fun t => ∫ τ in (0:ℝ)..t, L τ (pic L x0 k τ)

lemma pic_spec (L : ℝ → E →L[ℝ] E) (x0 : E) (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ t, ‖L t‖ ≤ M)
    (hL : ∀ y : ℝ → E, Continuous y → Continuous (fun t => L t (y t))) (k : ℕ) :
    Continuous (pic L x0 k) ∧ ∀ t, ‖pic L x0 k t‖ ≤ ‖x0‖ * (M * |t|) ^ k / k.factorial := by
  induction k with
  | zero => exact ⟨continuous_const, fun t => by simp [pic]⟩
  | succ k ih =>
    obtain ⟨hc, hb⟩ := ih
    have hci := hL _ hc
    refine ⟨?_, fun t => ?_⟩
    · show Continuous (fun t => ∫ τ in (0:ℝ)..t, L τ (pic L x0 k τ))
      exact intervalIntegral.continuous_primitive (fun a b => hci.intervalIntegrable a b) 0
    · show ‖∫ τ in (0:ℝ)..t, L τ (pic L x0 k τ)‖ ≤ _
      have hb2 : ∀ τ, ‖L τ (pic L x0 k τ)‖ ≤ ‖x0‖ * M ^ (k+1) / k.factorial * |τ| ^ k := by
        intro τ
        calc ‖L τ (pic L x0 k τ)‖ ≤ ‖L τ‖ * ‖pic L x0 k τ‖ := (L τ).le_opNorm _
          _ ≤ M * (‖x0‖ * (M * |τ|) ^ k / k.factorial) :=
            mul_le_mul (hM τ) (hb τ) (norm_nonneg _) hM0
          _ = _ := by rw [mul_pow]; ring
      refine (intervalIntegral.norm_integral_le_abs_of_norm_le
        (Eventually.of_forall (fun τ => hb2 τ)) ?_).trans ?_
      · exact (continuous_const.mul ((continuous_abs).pow k)).intervalIntegrable _ _
      rw [intervalIntegral.integral_const_mul, abs_mul, abs_integral_abs_pow,
        abs_of_nonneg (by positivity), Nat.factorial_succ]
      push_cast
      rw [mul_pow, pow_succ M, pow_succ |t|]
      field_simp
      exact le_rfl

lemma pic_hasDerivAt (L : ℝ → E →L[ℝ] E) (x0 : E) (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ t, ‖L t‖ ≤ M)
    (hL : ∀ y : ℝ → E, Continuous y → Continuous (fun t => L t (y t))) (k : ℕ) (t : ℝ) :
    HasDerivAt (pic L x0 (k+1)) (L t (pic L x0 k t)) t := by
  have hci := hL _ (pic_spec L x0 M hM0 hM hL k).1
  exact intervalIntegral.integral_hasDerivAt_right (hci.intervalIntegrable _ _)
    (hci.stronglyMeasurableAtFilter _ _) hci.continuousAt

theorem ode_exists (L : ℝ → E →L[ℝ] E) (x0 : E) (M : ℝ) (hM : ∀ t, ‖L t‖ ≤ M)
    (hL : ∀ y : ℝ → E, Continuous y → Continuous (fun t => L t (y t))) :
    ∃ x : ℝ → E, x 0 = x0 ∧ ∀ t, HasDerivAt x (L t (x t)) t := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have spec := pic_spec L x0 M hM0 hM hL
  -- summability on each ball
  have hsum : ∀ T : ℝ, Summable (fun k : ℕ => ‖x0‖ * (M * T) ^ k / k.factorial) := by
    intro T
    have := (Real.summable_pow_div_factorial (M * T)).mul_left ‖x0‖
    simpa [mul_div_assoc] using this
  have hsumm : ∀ t, Summable (fun k => pic L x0 k t) := by
    intro t
    refine Summable.of_norm_bounded (hsum |t|) (fun k => ?_)
    exact (spec k).2 t
  refine ⟨fun t => ∑' k, pic L x0 k t, ?_, fun t => ?_⟩
  · show ∑' k, pic L x0 k 0 = x0
    rw [(hsumm 0).tsum_eq_zero_add]
    have : ∀ k, pic L x0 (k+1) 0 = 0 := fun k => by simp [pic]
    simp [this, pic]
  · -- derivative on the ball |y| < |t| + 1
    set T := |t| + 1
    have hderiv : ∀ k y, HasDerivAt (fun z => pic L x0 k z)
        (if k = 0 then 0 else L y (pic L x0 (k-1) y)) y := by
      intro k y
      cases k with
      | zero => simpa [pic] using hasDerivAt_const y x0
      | succ k => simpa using pic_hasDerivAt L x0 M hM0 hM hL k y
    have hb : ∀ k y, y ∈ Ioo (-T) T →
        ‖(if k = 0 then 0 else L y (pic L x0 (k-1) y))‖ ≤
          (if k = 0 then 0 else M * (‖x0‖ * (M * T) ^ (k-1) / (k-1).factorial)) := by
      intro k y hy
      have hyT : |y| ≤ T := (abs_lt.2 hy).le
      split_ifs with hk
      · simp
      · refine ((L y).le_opNorm _).trans (mul_le_mul (hM y) ((spec _).2 y |>.trans ?_)
          (norm_nonneg _) hM0)
        gcongr
    have hus : Summable (fun k : ℕ => (if k = 0 then 0 else
        M * (‖x0‖ * (M * T) ^ (k-1) / (k-1).factorial))) := by
      rw [← summable_nat_add_iff 1]
      simpa using (hsum T).mul_left M
    have hT : t ∈ Ioo (-T) T := by
      constructor <;> [have := neg_abs_le t; have := le_abs_self t] <;> simp only [T] <;> linarith
    have h := hasDerivAt_tsum_of_isPreconnected hus isOpen_Ioo isPreconnected_Ioo
      (fun k y _ => hderiv k y) hb hT (hsumm t) hT
    convert h using 1
    rw [(Summable.of_norm_bounded hus (fun k => hb k t hT)).tsum_eq_zero_add]
    · simp only [if_true, zero_add, Nat.add_sub_cancel, add_eq_zero, one_ne_zero, and_false,
        if_false]
      exact ((L t).map_tsum (hsumm t))

end HDecay

end HD_a

section HD_b

/-! Fundamental solution of `Ψ' = J₀ S∞ Ψ`, its inverse, and the sup-norm gap estimate. -/

open scoped Topology
open Set Filter CauchyRiemannIndex

namespace HDecay

variable {n : ℕ}

abbrev Op (n : ℕ) := Vec n →L[ℝ] Vec n

/-- matrices as operators -/
noncomputable def TL (n : ℕ) : Mat n ≃L[ℝ] (Op n) :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n ⊕ Fin n)).toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv

lemma TL_apply (M : Mat n) (v : Vec n) : TL n M v = Matrix.toEuclideanLin M v := rfl

lemma TL_mul (M N : Mat n) : TL n (M * N) = TL n M * TL n N :=
  map_mul (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n ⊕ Fin n)) M N

lemma TL_one : TL n 1 = 1 := map_one (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n ⊕ Fin n))

lemma periodic_bound {F : Type*} [NormedAddCommGroup F] (f : ℝ → F) (hf : Continuous f)
    (hp : Function.Periodic f 1) : ∃ M, ∀ t, ‖f t‖ ≤ M := by
  obtain ⟨M, hM⟩ := (hp.isBounded_of_continuous one_ne_zero hf).exists_norm_le
  exact ⟨M, fun t => hM _ ⟨t, rfl⟩⟩

theorem fund_exists (Sinf : ℝ → Mat n) (hS : IsSymLoop Sinf) :
    ∃ Ψ Φ : ℝ → Mat n, IsFundamentalSolution Sinf Ψ ∧ Φ 0 = 1 ∧
      (∀ t, HasDerivAt Φ (-(Φ t * (J₀ n * Sinf t))) t) ∧
      (∀ t, Φ t * Ψ t = 1) ∧ (∀ t, Ψ t * Φ t = 1) := by
  set A : ℝ → Op n := fun t => TL n (J₀ n * Sinf t) with hAdef
  have hAc : Continuous A := (TL n).continuous.comp (continuous_const.mul hS.1)
  have hAp : Function.Periodic A 1 := fun t => by simp only [A, hS.2.1 t]
  obtain ⟨M, hM⟩ := periodic_bound A hAc hAp
  -- left equation
  obtain ⟨X, hX0, hX⟩ := ode_exists
    (fun t => ContinuousLinearMap.compL ℝ (Vec n) (Vec n) (Vec n) (A t)) (1 : Op n) M
    (fun t => by
      refine ContinuousLinearMap.opNorm_le_bound _ ((norm_nonneg _).trans (hM t)) (fun x => ?_)
      simp only [ContinuousLinearMap.compL_apply]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right (hM t) (norm_nonneg _)))
    (fun y hy => by
      simp only [ContinuousLinearMap.compL_apply]
      exact hAc.clm_comp hy)
  -- right equation
  obtain ⟨Y, hY0, hY⟩ := ode_exists
    (fun t => (ContinuousLinearMap.compL ℝ (Vec n) (Vec n) (Vec n)).flip (-A t)) (1 : Op n) M
    (fun t => by
      refine ContinuousLinearMap.opNorm_le_bound _ ((norm_nonneg _).trans (hM t)) (fun x => ?_)
      simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply]
      calc ‖x.comp (-A t)‖ ≤ ‖x‖ * ‖-A t‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ M * ‖x‖ := by
          rw [norm_neg, mul_comm]; exact mul_le_mul_of_nonneg_right (hM t) (norm_nonneg _))
    (fun y hy => by
      simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply]
      exact hy.clm_comp hAc.neg)
  simp only [ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply,
    ← ContinuousLinearMap.mul_def] at hX hY
  -- Y * X = 1
  have hYX : ∀ t, Y t * X t = 1 := by
    have hd : ∀ t, HasDerivAt (fun t => Y t * X t) 0 t := by
      intro t
      have := (hY t).clm_comp (hX t)
      simp only [← ContinuousLinearMap.mul_def] at this
      refine this.congr_deriv ?_
      rw [mul_neg, neg_mul, mul_assoc, neg_add_cancel]
    intro t
    have := is_const_of_deriv_eq_zero (f := fun t => Y t * X t)
      (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) t 0
    simpa only [hY0, hX0, mul_one] using this
  let _ : NormedAddCommGroup (Mat n) := Matrix.normedAddCommGroup
  let _ : NormedSpace ℝ (Mat n) := Matrix.normedSpace
  refine ⟨fun t => (TL n).symm (X t), fun t => (TL n).symm (Y t), ⟨?_, fun t => ?_⟩, ?_,
    fun t => ?_, fun t => ?_, fun t => ?_⟩
  · simp only [hX0, ← TL_one, ContinuousLinearEquiv.symm_apply_apply]
  · have := (TL n).symm.hasFDerivAt.comp_hasDerivAt t (hX t)
    have hv : (TL n).symm (A t * X t) = J₀ n * Sinf t * (TL n).symm (X t) := by
      apply (TL n).injective
      simp only [TL_mul, ContinuousLinearEquiv.apply_symm_apply, A]
    exact this.congr_deriv hv
  · simp only [hY0, ← TL_one, ContinuousLinearEquiv.symm_apply_apply]
  · have := (TL n).symm.hasFDerivAt.comp_hasDerivAt t (hY t)
    have hv : (TL n).symm (Y t * -A t) = -((TL n).symm (Y t) * (J₀ n * Sinf t)) := by
      apply (TL n).injective
      simp only [TL_mul, mul_neg, map_neg, ContinuousLinearEquiv.apply_symm_apply, A]
    exact this.congr_deriv hv
  · apply (TL n).injective
    simp only [TL_mul, ContinuousLinearEquiv.apply_symm_apply, hYX t, TL_one]
  · have h1 : (TL n).symm (Y t) * (TL n).symm (X t) = 1 := by
      apply (TL n).injective
      simp only [TL_mul, ContinuousLinearEquiv.apply_symm_apply, hYX t, TL_one]
    exact mul_eq_one_comm.1 h1

end HDecay

end HD_b

section HD_c

/-! Sup-norm gap estimate for the nondegenerate asymptotic operator `-J₀ ∂ₜ - S∞`. -/

open scoped Topology
open Set Filter CauchyRiemannIndex

namespace HDecay

variable {n : ℕ}

/-- `J₀` as an operator. -/
noncomputable abbrev Jop (n : ℕ) : Op n := TL n (J₀ n)

lemma Jop_Jop (v : Vec n) : Jop n (Jop n v) = -v := by
  have : Jop n * Jop n = -1 := by
    rw [Jop, ← TL_mul, Matrix.J_squared, map_neg, TL_one]
  have h := congrArg (fun T : Op n => T v) this
  simpa using h

lemma TL_cont_bound (Ψ : ℝ → Mat n) (hc : Continuous fun t => TL n (Ψ t)) :
    ∃ M, 0 ≤ M ∧ ∀ t ∈ Icc (0:ℝ) 1, ‖TL n (Ψ t)‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_bound_of_continuousOn
    hc.continuousOn
  exact ⟨max M 0, le_max_right _ _, fun t ht => (hM t ht).trans (le_max_left _ _)⟩

end HDecay

end HD_c

section HD_d

/-! Partial derivatives on the half-cylinder `Ω = (0, ∞) × ℝ`. -/

open scoped Topology ContDiff
open Set Filter CauchyRiemannIndex

namespace HDecay

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ### Operator-valued coefficients -/

variable {n : ℕ}

end HDecay

end HD_d

section HD_e

/-! `t`-integrals over a period: differentiation in `s` and integration by parts in `t`. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

end HDecay

end HD_e

section HD_f

/-! Bounds on the coefficient field `S` from its `C^∞` convergence to `S∞`. -/

open scoped Topology ContDiff
open Set Filter CauchyRiemannIndex

namespace HDecay

variable {n : ℕ}

end HDecay

end HD_f

section HD_g

/-! Second derivative of the energy `∫₀¹ |η(s, t)|² dt`. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

lemma inner_TL_left (M : Mat n) (v w : Vec n) :
    ⟪TL n M v, w⟫ = ⟪v, TL n (Matrix.transpose M) w⟫ := by
  have h := Matrix.toEuclideanLin_conjTranspose_eq_adjoint M
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  rw [TL_apply, TL_apply, h, LinearMap.adjoint_inner_right]

lemma inner_Jop (v w : Vec n) : ⟪v, Jop n w⟫ = -⟪Jop n v, w⟫ := by
  rw [Jop, inner_TL_left, Matrix.J_transpose, map_neg, ContinuousLinearMap.neg_apply, inner_neg_right,
    neg_neg]

lemma inner_symm {M : Mat n} (hM : M.IsSymm) (v w : Vec n) : ⟪TL n M v, w⟫ = ⟪v, TL n M w⟫ := by
  rw [inner_TL_left, hM.eq]

section energy

variable (A : ℝ × ℝ → Op n) (η : ℝ × ℝ → Vec n)

variable {A η}

end energy

end HDecay

end HD_g

section HD_h

/-! Jensen, the `L²` gap estimate, and two one-variable decay lemmas. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

lemma sq_integral_le (g : ℝ → ℝ) (hg : Continuous g) :
    (∫ t in (0:ℝ)..1, g t) ^ 2 ≤ ∫ t in (0:ℝ)..1, g t ^ 2 := by
  set m := ∫ t in (0:ℝ)..1, g t
  have h0 : 0 ≤ ∫ t in (0:ℝ)..1, (g t - m) ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one fun _ _ => sq_nonneg _
  have e : ∫ t in (0:ℝ)..1, (g t - m) ^ 2 = (∫ t in (0:ℝ)..1, g t ^ 2) - m ^ 2 := by
    have : (fun t => (g t - m) ^ 2) = fun t => (g t ^ 2 - 2 * m * g t) + m ^ 2 := by
      funext t; ring
    have i1 : IntervalIntegrable (fun t => g t ^ 2) volume 0 1 := (hg.pow 2).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun t => 2 * m * g t) volume 0 1 :=
      (continuous_const.mul hg).intervalIntegrable _ _
    rw [this, intervalIntegral.integral_add (i1.sub i2) intervalIntegrable_const,
      intervalIntegral.integral_sub i1 i2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul, one_mul]
    ring
  linarith

end HDecay

end HD_h

section HD_i

/-! Generic lower bounds for the energy's second derivative. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

end HDecay

end HD_i

section HD_j

/-! One-variable lemmas used to pass from energy inequalities to decay. -/

open scoped Topology
open Set Filter MeasureTheory

namespace HDecay

end HDecay

end HD_j

section AF_a

/-! Gap estimate with kernel: periodic loops are sup-close to periodic solutions. -/

open scoped Topology
open Set Filter CauchyRiemannIndex

namespace HDecay

variable {n : ℕ}

lemma dist_ker {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : E →L[ℝ] E) : ∃ C, 0 ≤ C ∧ ∀ x : E, ∃ k, L k = 0 ∧ ‖x - k‖ ≤ C * ‖L x‖ := by
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl (LinearMap.ker (L : E →ₗ[ℝ] E))
  set f : W →ₗ[ℝ] E := (L : E →ₗ[ℝ] E).comp W.subtype
  have hf : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro w hw
    have h1 : (w : E) ∈ LinearMap.ker (L : E →ₗ[ℝ] E) := hw
    have h2 : (w : E) ∈ W := w.2
    have := hW.disjoint.le_bot ⟨h1, h2⟩
    exact Subtype.ext (by simpa only [ZeroMemClass.coe_zero, ZeroMemClass.coe_eq_zero, Submodule.mem_bot] using this)
  obtain ⟨K, hK0, hK⟩ := f.exists_antilipschitzWith hf
  refine ⟨K, K.2, fun x => ?_⟩
  obtain ⟨⟨k, hk⟩, ⟨w, hw⟩, hkw, -⟩ := Submodule.existsUnique_add_of_isCompl hW x
  refine ⟨k, by simpa only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] using hk, ?_⟩
  have hx : x - k = w := by rw [← hkw]; abel
  have hLx : L x = f ⟨w, hw⟩ := by
    have : L k = 0 := by simpa only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] using hk
    simp only [← hkw, map_add, this, zero_add, LinearMap.coe_comp, ContinuousLinearMap.coe_coe,
      Submodule.coe_subtype, Function.comp_apply, f]
  rw [hx, hLx]
  have := hK.le_mul_dist (⟨w, hw⟩ : W) 0
  simpa only [ge_iff_le, dist_eq_norm, sub_zero, Submodule.coe_norm, map_zero] using this

lemma floquet (Sinf : ℝ → Mat n) (hS : IsSymLoop Sinf) (Ψ Φ : ℝ → Mat n)
    (hΨ : ∀ t, HasDerivAt Ψ (J₀ n * Sinf t * Ψ t) t)
    (hΦ0 : Φ 0 = 1) (hΦ : ∀ t, HasDerivAt Φ (-(Φ t * (J₀ n * Sinf t))) t)
    (hΨΦ : ∀ t, Ψ t * Φ t = 1) (t : ℝ) : Ψ (t + 1) = Ψ t * Ψ 1 := by
  let _ : NormedAddCommGroup (Mat n) := Matrix.normedAddCommGroup
  let _ : NormedSpace ℝ (Mat n) := Matrix.normedSpace
  have hP : ∀ t, HasDerivAt (fun t => TL n (Ψ (t + 1))) (TL n (J₀ n * Sinf t * Ψ (t + 1))) t := by
    intro t
    have := (TL n).hasFDerivAt.comp_hasDerivAt t ((hΨ (t + 1)).comp_add_const t 1)
    rw [hS.2.1 t] at this
    exact this
  have hQ : ∀ t, HasDerivAt (fun t => TL n (Φ t)) (TL n (-(Φ t * (J₀ n * Sinf t)))) t :=
    fun t => (TL n).hasFDerivAt.comp_hasDerivAt t (hΦ t)
  have hd : ∀ t, HasDerivAt (fun t => TL n (Φ t) * TL n (Ψ (t + 1))) 0 t := by
    intro t
    have := (hQ t).mul (hP t)
    refine this.congr_deriv ?_
    simp only [← TL_mul, ← map_add]
    rw [show -(Φ t * (J₀ n * Sinf t)) * Ψ (t + 1) + Φ t * (J₀ n * Sinf t * Ψ (t + 1)) = 0 by
      noncomm_ring]
    simp only [map_zero]
  have hc := is_const_of_deriv_eq_zero (f := fun t => TL n (Φ t) * TL n (Ψ (t + 1)))
    (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) t 0
  simp only [hΦ0, TL_one, one_mul, zero_add, ← TL_mul] at hc
  have h1 : Φ t * Ψ (t + 1) = Ψ 1 := (TL n).injective hc
  calc Ψ (t + 1) = Ψ t * Φ t * Ψ (t + 1) := by rw [hΨΦ t, one_mul]
    _ = Ψ t * Ψ 1 := by rw [mul_assoc, h1]

/-- Gap estimate with kernel: every `1`-periodic `C¹` loop `η` is sup-close to the periodic
solution `Ψ(·) k` of `-J₀ e' - S∞ e = 0`, with error `C ∫₀¹ |-J₀ η' - S∞ η|`. -/
theorem gap_ker (Sinf : ℝ → Mat n) (hS : IsSymLoop Sinf) :
    ∃ Ψ : ℝ → Mat n, IsFundamentalSolution Sinf Ψ ∧ (∀ t, Ψ (t + 1) = Ψ t * Ψ 1) ∧
    (∃ Φ : ℝ → Mat n, Continuous (fun t => TL n (Φ t)) ∧ ∀ t, Φ t * Ψ t = 1) ∧
    ∃ C, 0 ≤ C ∧ ∀ η η' : ℝ → Vec n, (∀ t, HasDerivAt η (η' t) t) → Continuous η' →
      Function.Periodic η 1 → ∃ k : Vec n, TL n (Ψ 1) k = k ∧ ∀ t, ‖η t - TL n (Ψ t) k‖ ≤
        C * ∫ τ in (0:ℝ)..1, ‖-(Jop n (η' τ)) - TL n (Sinf τ) (η τ)‖ := by
  obtain ⟨Ψ, Φ, ⟨hΨ0, hΨ⟩, hΦ0, hΦ, hΦΨ, hΨΦ⟩ := fund_exists Sinf hS
  have hfl := floquet Sinf hS Ψ Φ hΨ hΦ0 hΦ hΨΦ
  let _ : NormedAddCommGroup (Mat n) := Matrix.normedAddCommGroup
  let _ : NormedSpace ℝ (Mat n) := Matrix.normedSpace
  have hP : ∀ t, HasDerivAt (fun t => TL n (Ψ t)) (TL n (J₀ n * Sinf t * Ψ t)) t :=
    fun t => (TL n).hasFDerivAt.comp_hasDerivAt t (hΨ t)
  have hQ : ∀ t, HasDerivAt (fun t => TL n (Φ t)) (TL n (-(Φ t * (J₀ n * Sinf t)))) t :=
    fun t => (TL n).hasFDerivAt.comp_hasDerivAt t (hΦ t)
  have hΨc : Continuous fun t => TL n (Ψ t) :=
    continuous_iff_continuousAt.2 fun t => (hP t).continuousAt
  have hΦc : Continuous fun t => TL n (Φ t) :=
    continuous_iff_continuousAt.2 fun t => (hQ t).continuousAt
  obtain ⟨MP, hMP0, hMP⟩ := TL_cont_bound Ψ hΨc
  obtain ⟨MQ, hMQ0, hMQ⟩ := TL_cont_bound Φ hΦc
  obtain ⟨Cd, hCd0, hCd⟩ := dist_ker (TL n (1 - Ψ 1))
  set cJ : ℝ := ‖Jop n‖
  set C0 : ℝ := Cd * (MP * (MQ * cJ))
  have hcJ : 0 ≤ cJ := norm_nonneg _
  have hC0 : 0 ≤ C0 := mul_nonneg hCd0 (mul_nonneg hMP0 (mul_nonneg hMQ0 hcJ))
  refine ⟨Ψ, ⟨hΨ0, hΨ⟩, hfl, ⟨Φ, hΦc, hΦΨ⟩, MP * (C0 + MQ * cJ),
    mul_nonneg hMP0 (add_nonneg hC0 (mul_nonneg hMQ0 hcJ)), ?_⟩
  intro η η' hη hη' hper
  have hηc : Continuous η := continuous_iff_continuousAt.2 fun t => (hη t).continuousAt
  set g : ℝ → Vec n := fun τ => -(Jop n (η' τ)) - TL n (Sinf τ) (η τ) with hg
  have hgc : Continuous g := by
    refine ((Jop n).continuous.comp hη').neg.sub ?_
    exact (((TL n).continuous.comp hS.1).clm_apply hηc)
  set w : ℝ → Vec n := fun t => TL n (Φ t) (η t)
  have hw : ∀ t, HasDerivAt w (TL n (Φ t) (Jop n (g t))) t := by
    intro t
    have := (hQ t).clm_apply (hη t)
    refine this.congr_deriv ?_
    have hJg : Jop n (g t) = η' t - Jop n (TL n (Sinf t) (η t)) := by
      simp only [g, map_sub, map_neg, Jop_Jop, neg_neg]
    rw [hJg, map_sub]
    simp only [map_neg, TL_mul, ContinuousLinearMap.neg_apply, ContinuousLinearMap.mul_apply]
    abel
  have hint : ∀ t, w t - w 0 = ∫ τ in (0:ℝ)..t, TL n (Φ τ) (Jop n (g τ)) := by
    intro t
    have hc : Continuous fun τ => TL n (Φ τ) (Jop n (g τ)) :=
      hΦc.clm_apply ((Jop n).continuous.comp hgc)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hw x)
      (hc.intervalIntegrable _ _)]
  have hw0 : w 0 = η 0 := by simp only [hΦ0, TL_one, one_apply_eq_self, w]
  set I1 : ℝ := ∫ τ in (0:ℝ)..1, ‖g τ‖
  have hI : ∀ t ∈ Icc (0:ℝ) 1, ‖∫ τ in (0:ℝ)..t, TL n (Φ τ) (Jop n (g τ))‖ ≤ MQ * cJ * I1 := by
    intro t ht
    refine (intervalIntegral.norm_integral_le_integral_norm ht.1).trans ?_
    have hb : ∀ τ ∈ Icc (0:ℝ) t, ‖TL n (Φ τ) (Jop n (g τ))‖ ≤ MQ * cJ * ‖g τ‖ := by
      intro τ hτ
      calc ‖TL n (Φ τ) (Jop n (g τ))‖ ≤ ‖TL n (Φ τ)‖ * ‖Jop n (g τ)‖ := (TL n (Φ τ)).le_opNorm _
        _ ≤ MQ * (cJ * ‖g τ‖) := mul_le_mul (hMQ τ ⟨hτ.1, hτ.2.trans ht.2⟩)
            ((Jop n).le_opNorm _) (norm_nonneg _) hMQ0
        _ = _ := by ring
    have hc : Continuous fun τ => ‖TL n (Φ τ) (Jop n (g τ))‖ :=
      (hΦc.clm_apply ((Jop n).continuous.comp hgc)).norm
    calc ∫ τ in (0:ℝ)..t, ‖TL n (Φ τ) (Jop n (g τ))‖ ≤ ∫ τ in (0:ℝ)..t, MQ * cJ * ‖g τ‖ :=
          intervalIntegral.integral_mono_on ht.1 (hc.intervalIntegrable _ _)
            ((continuous_const.mul hgc.norm).intervalIntegrable _ _) hb
      _ = MQ * cJ * ∫ τ in (0:ℝ)..t, ‖g τ‖ := intervalIntegral.integral_const_mul _ _
      _ ≤ MQ * cJ * I1 :=
          mul_le_mul_of_nonneg_left (intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
            (Eventually.of_forall fun _ => norm_nonneg _) (hgc.norm.intervalIntegrable _ _))
            (mul_nonneg hMQ0 hcJ)
  have hI1 : 0 ≤ I1 := intervalIntegral.integral_nonneg zero_le_one fun _ _ => norm_nonneg _
  obtain ⟨k, hk, hk0⟩ := hCd (η 0)
  have hk1 : TL n (Ψ 1) k = k := by
    have : TL n (1 - Ψ 1) k = k - TL n (Ψ 1) k := by rw [map_sub, TL_one]; rfl
    rw [this, sub_eq_zero] at hk
    exact hk.symm
  have h0 : ‖η 0 - k‖ ≤ C0 * I1 := by
    have key : TL n (1 - Ψ 1) (η 0) = TL n (Ψ 1) (w 1 - w 0) := by
      have : w 1 = TL n (Φ 1) (η 0) := by simp only [← hper 0, zero_add, w]
      have h1 : TL n (Ψ 1) (TL n (Φ 1) (η 0)) = η 0 := by
        rw [← ContinuousLinearMap.mul_apply, ← TL_mul, hΨΦ, TL_one]; rfl
      rw [this, hw0, map_sub, TL_one, map_sub, h1]
      simp only [sub_apply, one_apply_eq_self]
    refine hk0.trans ?_
    rw [key, hint 1]
    calc Cd * ‖TL n (Ψ 1) (∫ τ in (0:ℝ)..1, TL n (Φ τ) (Jop n (g τ)))‖
        ≤ Cd * (‖TL n (Ψ 1)‖ * ‖∫ τ in (0:ℝ)..1, TL n (Φ τ) (Jop n (g τ))‖) :=
          mul_le_mul_of_nonneg_left ((TL n (Ψ 1)).le_opNorm _) hCd0
      _ ≤ Cd * (MP * (MQ * cJ * I1)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul (hMP 1 ⟨zero_le_one, le_rfl⟩)
            (hI 1 ⟨zero_le_one, le_rfl⟩) (norm_nonneg _) hMP0) hCd0
      _ = C0 * I1 := by simp only [C0]; ring
  have hIcc : ∀ t ∈ Ico (0:ℝ) 1, ‖η t - TL n (Ψ t) k‖ ≤ MP * (C0 + MQ * cJ) * I1 := by
    intro t ht
    have ht' : t ∈ Icc (0:ℝ) 1 := Ico_subset_Icc_self ht
    have hv : η t = TL n (Ψ t) (w t) := by
      simp only [w, ← ContinuousLinearMap.mul_apply, ← TL_mul, hΨΦ, TL_one]; rfl
    have hwt : w t = (η 0 - k) + (∫ τ in (0:ℝ)..t, TL n (Φ τ) (Jop n (g τ))) + k := by
      rw [← hint t, hw0]; abel
    rw [hv, hwt, map_add, add_sub_cancel_right]
    calc ‖TL n (Ψ t) ((η 0 - k) + ∫ τ in (0:ℝ)..t, TL n (Φ τ) (Jop n (g τ)))‖
        ≤ ‖TL n (Ψ t)‖ * ‖(η 0 - k) + ∫ τ in (0:ℝ)..t, TL n (Φ τ) (Jop n (g τ))‖ :=
          (TL n (Ψ t)).le_opNorm _
      _ ≤ MP * (C0 * I1 + MQ * cJ * I1) :=
          mul_le_mul (hMP t ht') ((norm_add_le _ _).trans (add_le_add h0 (hI t ht')))
            (norm_nonneg _) hMP0
      _ = _ := by ring
  have hper2 : Function.Periodic (fun t => η t - TL n (Ψ t) k) 1 := by
    intro t
    simp only [hper t, hfl t, TL_mul, ContinuousLinearMap.mul_apply, hk1]
  refine ⟨k, hk1, fun t => ?_⟩
  obtain ⟨y, hy, hyt⟩ := hper2.exists_mem_Ico₀ zero_lt_one t
  rw [show η t - TL n (Ψ t) k = η y - TL n (Ψ y) k from hyt]
  exact hIcc y hy

end HDecay

end AF_a

section AF_b

/-! Cauchy–Schwarz for `Ip` and the differential inequality for `α = ⟨ζ, ∂ₛζ⟩ / |ζ|²`. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

end HDecay

end AF_b

section AF_c

/-! One-variable lemmas: forward positivity (unique continuation) and barriers. -/

open scoped Topology
open Set Filter MeasureTheory

namespace HDecay

end HDecay

end AF_c

section AF_d

/-! Convergence of `α` under an integrable (exponentially small) defect. -/

open scoped Topology
open Set Filter MeasureTheory

namespace HDecay

section

variable (α α1 q F ε : ℝ → ℝ) (s1 K d C0 δ0 : ℝ)

variable {α α1 q F ε s1 K d C0 δ0}

end

end HDecay

end AF_d

section AF_e

/-! Exponential rate for `α → μ` given a spectral gap inequality. -/

open scoped Topology
open Set Filter MeasureTheory

namespace HDecay

variable {α α1 q F ε : ℝ → ℝ} {s1 K d C0 δ0 : ℝ}

end HDecay

end AF_e

section AF_f

/-! Exponentially small coefficients from `IsExpAsymptoticTo`. -/

open scoped Topology ContDiff
open Set Filter CauchyRiemannIndex

namespace HDecay

variable {n : ℕ}

end HDecay

end AF_f

section AF_g

/-! The quantities `F, D, G, α, q` of a solution and their derivatives. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

section sol

variable (A : ℝ × ℝ → Op n) (ζ : ℝ × ℝ → Vec n)

variable {A ζ}

end sol

end HDecay

end AF_g

section AF_h

/-! Unique continuation: `‖ζ(s)‖_{L²} > 0` for all `s ≥ s₀` once it is positive at `s₀`. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

end HDecay

end AF_h

section AF_i

/-! The `α`-hypotheses for a solution of the linear Cauchy–Riemann equation. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

end HDecay

end AF_i

section AF_j

/-! Spectral gap inequality for `A∞ - μ`, valid for every `μ ∈ ℝ`. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

lemma isSymLoop_shift (Sinf : ℝ → Mat n) (hS : IsSymLoop Sinf) (μ : ℝ) :
    IsSymLoop (fun t => Sinf t + μ • (1 : Mat n)) := by
  refine ⟨hS.1.add continuous_const, fun t => by simp only [hS.2.1 t], fun t => ?_⟩
  exact (hS.2.2 t).add (Matrix.isSymm_one.smul μ)

lemma TL_shift (M : Mat n) (μ : ℝ) (v : Vec n) : TL n (M + μ • (1 : Mat n)) v = TL n M v + μ • v := by
  simp [map_add, map_smul, TL_one]

lemma TL_mul3 (A B D : Mat n) (k : Vec n) : TL n (A * B * D) k = TL n A (TL n B (TL n D k)) := by
  rw [TL_mul, TL_mul]; rfl

lemma inner_Jop_Jop (v w : Vec n) : ⟪Jop n v, Jop n w⟫ = ⟪v, w⟫ := by
  rw [inner_Jop, Jop_Jop, inner_neg_left, neg_neg]

theorem gap_mu (Sinf : ℝ → Mat n) (hS : IsSymLoop Sinf) (μ : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ η η' : ℝ → Vec n, (∀ t, HasDerivAt η (η' t) t) → Continuous η' →
      Function.Periodic η 1 →
      |∫ t in (0:ℝ)..1, ⟪η t, -(Jop n (η' t)) - TL n (Sinf t) (η t) - μ • η t⟫| ≤
        C * ∫ t in (0:ℝ)..1, ‖-(Jop n (η' t)) - TL n (Sinf t) (η t) - μ • η t‖ ^ 2 := by
  have hS' := isSymLoop_shift Sinf hS μ
  obtain ⟨Ψ, ⟨hΨ0, hΨ⟩, hfl, -, C, hC0, hC⟩ := gap_ker _ hS'
  refine ⟨C, hC0, fun η η' hη hη' hper => ?_⟩
  set g : ℝ → Vec n := fun t => -(Jop n (η' t)) - TL n (Sinf t) (η t) - μ • η t with hg
  have hηc : Continuous η := continuous_iff_continuousAt.2 fun t => (hη t).continuousAt
  have hgc : Continuous g :=
    (((Jop n).continuous.comp hη').neg.sub (((TL n).continuous.comp hS.1).clm_apply hηc)).sub
      (hηc.const_smul μ)
  obtain ⟨k, hk, hkb⟩ := hC η η' hη hη' hper
  have hkb' : ∀ t, ‖η t - TL n (Ψ t) k‖ ≤ C * ∫ τ in (0:ℝ)..1, ‖g τ‖ := by
    intro t
    refine (hkb t).trans_eq ?_
    congr 1
    refine intervalIntegral.integral_congr fun τ _ => ?_
    simp only [g, TL_shift, sub_sub]
  set e : ℝ → Vec n := fun t => TL n (Ψ t) k
  have he' : ∀ t, HasDerivAt e (Jop n (TL n (Sinf t + μ • (1 : Mat n)) (e t))) t := by
    intro t
    let _ : NormedAddCommGroup (Mat n) := Matrix.normedAddCommGroup
    let _ : NormedSpace ℝ (Mat n) := Matrix.normedSpace
    have := ((TL n).hasFDerivAt.comp_hasDerivAt t (hΨ t)).clm_apply (hasDerivAt_const t k)
    refine this.congr_deriv ?_
    simp only [map_zero, add_zero, e]
    exact TL_mul3 _ _ _ k
  have hec : Continuous e := continuous_iff_continuousAt.2 fun t => (he' t).continuousAt
  have heper : Function.Periodic e 1 := fun t => by
    simp only [e]; rw [hfl t, TL_mul]; simp [hk]
  -- `∫ ⟪g, e⟫ = 0`
  have hf : ∀ t, HasDerivAt (fun t => ⟪Jop n (η t), e t⟫) (-⟪g t, e t⟫) t := by
    intro t
    have := (((Jop n).hasFDerivAt.comp_hasDerivAt t (hη t))).inner ℝ (he' t)
    refine this.congr_deriv ?_
    simp only [Function.comp, ContinuousLinearMap.coe_coe] at *
    rw [inner_Jop_Jop, ← inner_symm (hS'.2.2 t), TL_shift]
    simp only [g, inner_sub_left, inner_neg_left, inner_add_left]
    ring
  have hge : ∫ t in (0:ℝ)..1, ⟪g t, e t⟫ = 0 := by
    have h1 := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1) (fun t _ => hf t)
      ((hgc.inner hec).neg.intervalIntegrable _ _)
    rw [intervalIntegral.integral_neg] at h1
    have h2 : ⟪Jop n (η 1), e 1⟫ = ⟪Jop n (η 0), e 0⟫ := by
      have a := hper 0; have b := heper 0; simp only [zero_add] at a b; rw [a, b]
    linarith
  set I1 := ∫ τ in (0:ℝ)..1, ‖g τ‖
  have hI1 : 0 ≤ I1 := intervalIntegral.integral_nonneg zero_le_one fun _ _ => norm_nonneg _
  have heq : ∫ t in (0:ℝ)..1, ⟪η t, g t⟫ = ∫ t in (0:ℝ)..1, ⟪η t - e t, g t⟫ := by
    have : (fun t => ⟪η t - e t, g t⟫) = fun t => ⟪η t, g t⟫ - ⟪g t, e t⟫ := by
      funext t; rw [inner_sub_left, real_inner_comm (e t)]
    rw [this, intervalIntegral.integral_sub ((hηc.inner hgc).intervalIntegrable _ _)
      ((hgc.inner hec).intervalIntegrable _ _), hge, sub_zero]
  rw [heq]
  calc |∫ t in (0:ℝ)..1, ⟪η t - e t, g t⟫|
      ≤ ∫ t in (0:ℝ)..1, |⟪η t - e t, g t⟫| := by
        rw [← Real.norm_eq_abs]
        refine (intervalIntegral.norm_integral_le_integral_norm zero_le_one).trans_eq ?_
        simp only [Real.norm_eq_abs]
    _ ≤ ∫ t in (0:ℝ)..1, C * I1 * ‖g t‖ := by
        refine intervalIntegral.integral_mono_on zero_le_one
          (((hηc.sub hec).inner hgc).abs.intervalIntegrable _ _)
          ((continuous_const.mul hgc.norm).intervalIntegrable _ _) fun t _ => ?_
        refine (abs_real_inner_le_norm _ _).trans ?_
        gcongr
        exact hkb' t
    _ = C * I1 ^ 2 := by
        rw [intervalIntegral.integral_const_mul]; ring
    _ ≤ C * ∫ t in (0:ℝ)..1, ‖g t‖ ^ 2 := by
        gcongr; exact sq_integral_le _ hgc.norm

end HDecay

end AF_j

section SP5

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

theorem solution {n : ℕ} (Sinf : ℝ → CauchyRiemannIndex.Mat n)
    (hSinf : CauchyRiemannIndex.IsSymLoop Sinf) (μ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η η' : ℝ → CauchyRiemannIndex.Vec n, (∀ t, HasDerivAt η (η' t) t) →
      Continuous η' → Function.Periodic η 1 →
      |∫ t in (0:ℝ)..1, ⟪η t, -(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ n) (η' t)) -
          Matrix.toEuclideanLin (Sinf t) (η t) - μ • η t⟫| ≤
        C * ∫ t in (0:ℝ)..1, ‖-(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ n) (η' t)) -
          Matrix.toEuclideanLin (Sinf t) (η t) - μ • η t‖ ^ 2 :=
  HDecay.gap_mu Sinf hSinf μ

end SP5
