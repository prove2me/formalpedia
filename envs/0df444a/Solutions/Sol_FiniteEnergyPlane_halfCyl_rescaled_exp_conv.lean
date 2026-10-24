-- Prove2me | solution 1 for FiniteEnergyPlane.halfCyl_rescaled_exp_conv
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T15:36:58.065369+00:00
-- url     : https://prove2.me/submissions/b8b69a3c-c190-41ea-b09c-603d756f6596

import Mathlib
import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Theorems.Thm_FiniteEnergyPlane_halfCyl_alpha_eta_bounds

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

/-- The open half-cylinder (as a strip). -/
def Ω : Set (ℝ × ℝ) := Ioi 0 ×ˢ univ

lemma isOpen_Ω : IsOpen Ω := isOpen_Ioi.prod isOpen_univ

lemma mem_Ω {s t : ℝ} (hs : 0 < s) : (s, t) ∈ Ω := ⟨hs, trivial⟩

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `∂ₛu`. -/
noncomputable def pS (u : ℝ × ℝ → F) (x : ℝ × ℝ) : F := fderiv ℝ u x (1, 0)
/-- `∂ₜu`. -/
noncomputable def pT (u : ℝ × ℝ → F) (x : ℝ × ℝ) : F := fderiv ℝ u x (0, 1)

/-- Smooth on `Ω`. -/
abbrev Sm (u : ℝ × ℝ → F) : Prop := ContDiffOn ℝ ∞ u Ω

lemma Sm.dS {u : ℝ × ℝ → F} (hu : Sm u) : Sm (pS u) :=
  (hu.fderiv_of_isOpen isOpen_Ω (by simp)).clm_apply contDiffOn_const

lemma Sm.dT {u : ℝ × ℝ → F} (hu : Sm u) : Sm (pT u) :=
  (hu.fderiv_of_isOpen isOpen_Ω (by simp)).clm_apply contDiffOn_const

lemma Sm.diffAt {u : ℝ × ℝ → F} (hu : Sm u) {x : ℝ × ℝ} (hx : x ∈ Ω) :
    DifferentiableAt ℝ u x :=
  (hu.contDiffAt (isOpen_Ω.mem_nhds hx)).differentiableAt (by simp)

lemma Sm.cont {u : ℝ × ℝ → F} (hu : Sm u) : ContinuousOn u Ω := hu.continuousOn

lemma Sm.hasDerivAt_s {u : ℝ × ℝ → F} (hu : Sm u) {s t : ℝ} (hs : 0 < s) :
    HasDerivAt (fun σ => u (σ, t)) (pS u (s, t)) s := by
  have h := (hu.diffAt (mem_Ω (t := t) hs)).hasFDerivAt.comp_hasDerivAt s
    ((hasDerivAt_id s).prodMk (hasDerivAt_const s t))
  exact h

lemma Sm.hasDerivAt_t {u : ℝ × ℝ → F} (hu : Sm u) {s t : ℝ} (hs : 0 < s) :
    HasDerivAt (fun τ => u (s, τ)) (pT u (s, t)) t := by
  have h := (hu.diffAt (mem_Ω (t := t) hs)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t s).prodMk (hasDerivAt_id t))
  exact h

lemma Sm.add {u v : ℝ × ℝ → F} (hu : Sm u) (hv : Sm v) : Sm (u + v) := ContDiffOn.add hu hv
lemma Sm.sub {u v : ℝ × ℝ → F} (hu : Sm u) (hv : Sm v) : Sm (u - v) := ContDiffOn.sub hu hv
lemma Sm.neg {u : ℝ × ℝ → F} (hu : Sm u) : Sm (-u) := ContDiffOn.neg hu

lemma pS_add {u v : ℝ × ℝ → F} (hu : Sm u) (hv : Sm v) {x} (hx : x ∈ Ω) :
    pS (u + v) x = pS u x + pS v x := by
  simp [pS, fderiv_add (hu.diffAt hx) (hv.diffAt hx)]

lemma pT_add {u v : ℝ × ℝ → F} (hu : Sm u) (hv : Sm v) {x} (hx : x ∈ Ω) :
    pT (u + v) x = pT u x + pT v x := by
  simp [pT, fderiv_add (hu.diffAt hx) (hv.diffAt hx)]

lemma pS_neg (u : ℝ × ℝ → F) (x) : pS (-u) x = -pS u x := by
  simp [pS, show (-u) = fun y => -u y from rfl]

lemma pT_neg (u : ℝ × ℝ → F) (x) : pT (-u) x = -pT u x := by
  simp [pT, show (-u) = fun y => -u y from rfl]

/-- mixed partials commute -/
lemma pS_pT {u : ℝ × ℝ → F} (hu : Sm u) {x} (hx : x ∈ Ω) : pS (pT u) x = pT (pS u) x := by
  have hc : ContDiffAt ℝ ∞ u x := hu.contDiffAt (isOpen_Ω.mem_nhds hx)
  have hsymm := hc.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top)
  have hd2 : DifferentiableAt ℝ (fderiv ℝ u) x := by
    have := (hu.fderiv_of_isOpen isOpen_Ω (m := 1) (WithTop.coe_le_coe.2 le_top)).contDiffAt (isOpen_Ω.mem_nhds hx)
    exact this.differentiableAt one_ne_zero
  show fderiv ℝ (fun y => fderiv ℝ u y (0, 1)) x (1, 0) =
    fderiv ℝ (fun y => fderiv ℝ u y (1, 0)) x (0, 1)
  rw [show (fun y => fderiv ℝ u y (0, 1)) = fun y => (fderiv ℝ u y) ((fun _ => ((0:ℝ), (1:ℝ))) y)
    from rfl, fderiv_clm_apply hd2 (differentiableAt_const _),
    show (fun y => fderiv ℝ u y (1, 0)) = fun y => (fderiv ℝ u y) ((fun _ => ((1:ℝ), (0:ℝ))) y)
    from rfl, fderiv_clm_apply hd2 (differentiableAt_const _)]
  simp only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  exact hsymm _ _

/-- `t`-periodicity -/
def TPer (u : ℝ × ℝ → F) : Prop := ∀ s t : ℝ, u (s, t + 1) = u (s, t)

lemma TPer.fderiv {u : ℝ × ℝ → F} (hu : TPer u) (s t : ℝ) :
    fderiv ℝ u (s, t + 1) = fderiv ℝ u (s, t) := by
  have : u = fun y => u (y + (0, 1)) := by
    funext y; obtain ⟨a, b⟩ := y; simp [hu a b]
  conv_rhs => rw [this]
  rw [fderiv_comp_add_right]
  simp

lemma TPer.pS {u : ℝ × ℝ → F} (hu : TPer u) : TPer (pS u) := fun s t => by
  simp [HDecay.pS, hu.fderiv s t]

lemma TPer.periodic {u : ℝ × ℝ → F} (hu : TPer u) (s : ℝ) :
    Function.Periodic (fun t => u (s, t)) 1 := fun t => hu s t

/-! ### Operator-valued coefficients -/

variable {n : ℕ}

lemma pS_apply {A : ℝ × ℝ → Op n} {v : ℝ × ℝ → Vec n} (hA : Sm A) (hv : Sm v) {x} (hx : x ∈ Ω) :
    pS (fun y => A y (v y)) x = pS A x (v x) + A x (pS v x) := by
  simp only [pS]
  rw [fderiv_clm_apply (hA.diffAt hx) (hv.diffAt hx)]
  simp [add_comm]

lemma Sm.apply {A : ℝ × ℝ → Op n} {v : ℝ × ℝ → Vec n} (hA : Sm A) (hv : Sm v) :
    Sm (fun y => A y (v y)) := hA.clm_apply hv

lemma pS_constOp (T : Op n) {v : ℝ × ℝ → Vec n} (hv : Sm v) {x} (hx : x ∈ Ω) :
    pS (fun y => T (v y)) x = T (pS v x) := by
  simp only [pS]
  rw [fderiv_clm_apply (differentiableAt_const _) (hv.diffAt hx)]
  simp

/-- matrix fields as operator fields -/
lemma TL_eq_sum (M : Mat n) :
    TL n M = ∑ i, ∑ j, M i j • TL n (Matrix.single i j 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single M]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← map_smul]
  congr 1
  ext a b
  simp [Matrix.single_apply]

lemma contDiff_TL {k : WithTop ℕ∞} (S : ℝ × ℝ → Mat n)
    (hS : ∀ i j, ContDiff ℝ k (fun p : ℝ × ℝ => S p i j)) :
    ContDiff ℝ k (fun p => TL n (S p)) := by
  have : (fun p => TL n (S p)) = fun p => ∑ i, ∑ j, S p i j • TL n (Matrix.single i j 1) := by
    funext p; exact TL_eq_sum _
  rw [this]
  exact ContDiff.sum fun i _ => ContDiff.sum fun j _ => (hS i j).smul contDiff_const

lemma contDiff_TL1 {k : WithTop ℕ∞} (S : ℝ → Mat n)
    (hS : ∀ i j, ContDiff ℝ k (fun t => S t i j)) :
    ContDiff ℝ k (fun t => TL n (S t)) := by
  have : (fun t => TL n (S t)) = fun t => ∑ i, ∑ j, S t i j • TL n (Matrix.single i j 1) := by
    funext p; exact TL_eq_sum _
  rw [this]
  exact ContDiff.sum fun i _ => ContDiff.sum fun j _ => (hS i j).smul contDiff_const

lemma norm_TL_le (M : Mat n) :
    ‖TL n M‖ ≤ ∑ i, ∑ j, |M i j| * ‖TL n (Matrix.single i j 1)‖ := by
  rw [TL_eq_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_smul, Real.norm_eq_abs]

end HDecay

end HD_d

section HD_e

/-! `t`-integrals over a period: differentiation in `s` and integration by parts in `t`. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

lemma cont_slice {F : Type*} [TopologicalSpace F] {w : ℝ × ℝ → F} (hw : ContinuousOn w Ω)
    {s : ℝ} (hs : 0 < s) : Continuous fun t => w (s, t) :=
  hw.comp_continuous (continuous_const.prodMk continuous_id) fun _ => mem_Ω hs

/-- differentiation under the integral sign -/
lemma param_deriv (F F' : ℝ × ℝ → ℝ) (hF : ContinuousOn F Ω) (hF' : ContinuousOn F' Ω)
    (hd : ∀ σ t, 0 < σ → HasDerivAt (fun σ => F (σ, t)) (F' (σ, t)) σ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun σ => ∫ t in (0:ℝ)..1, F (σ, t)) (∫ t in (0:ℝ)..1, F' (s, t)) s := by
  have hK : IsCompact (Metric.closedBall s (s / 2) ×ˢ Icc (0:ℝ) 1) :=
    (isCompact_closedBall _ _).prod isCompact_Icc
  have hKΩ : Metric.closedBall s (s / 2) ×ˢ Icc (0:ℝ) 1 ⊆ Ω := by
    rintro ⟨a, b⟩ ⟨ha, -⟩
    refine ⟨?_, trivial⟩
    rw [Metric.mem_closedBall, Real.dist_eq] at ha
    show 0 < a
    have := neg_abs_le (a - s)
    linarith
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hF'.mono hKΩ)
  have hball : Metric.ball s (s / 2) ⊆ Ioi 0 := by
    intro a ha
    rw [Metric.mem_ball, Real.dist_eq] at ha
    show 0 < a
    have := neg_abs_le (a - s)
    linarith
  have := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (a := 0) (b := 1) (F := fun σ t => F (σ, t)) (F' := fun σ t => F' (σ, t)) (x₀ := s)
    (bound := fun _ => M) (Metric.ball_mem_nhds s (by linarith : 0 < s / 2))
    ?_ ?_ ?_ ?_ intervalIntegrable_const ?_
  · exact this.2
  · filter_upwards [Ioi_mem_nhds hs] with σ hσ
    exact (cont_slice hF hσ).aestronglyMeasurable
  · exact (cont_slice hF hs).intervalIntegrable _ _
  · exact (cont_slice hF' hs).aestronglyMeasurable
  · refine Eventually.of_forall fun t ht σ hσ => hM (σ, t) ⟨Metric.ball_subset_closedBall hσ, ?_⟩
    rw [uIoc_of_le zero_le_one] at ht
    exact Ioc_subset_Icc_self ht
  · exact Eventually.of_forall fun t _ σ hσ => hd σ t (hball hσ)

variable {n : ℕ}

/-- `∫₀¹ ⟪u(s, t), v(s, t)⟫ dt` -/
noncomputable def Ip (u v : ℝ × ℝ → Vec n) (s : ℝ) : ℝ := ∫ t in (0:ℝ)..1, ⟪u (s, t), v (s, t)⟫

lemma cont_inner {u v : ℝ × ℝ → Vec n} (hu : ContinuousOn u Ω) (hv : ContinuousOn v Ω) {s : ℝ}
    (hs : 0 < s) : Continuous fun t => ⟪u (s, t), v (s, t)⟫ :=
  (cont_slice hu hs).inner (cont_slice hv hs)

lemma Ip_hasDerivAt {u v : ℝ × ℝ → Vec n} (hu : Sm u) (hv : Sm v) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (Ip u v) (Ip (pS u) v s + Ip u (pS v) s) s := by
  have h := param_deriv (fun x => ⟪u x, v x⟫) (fun x => ⟪pS u x, v x⟫ + ⟪u x, pS v x⟫)
    (hu.cont.inner hv.cont) ((hu.dS.cont.inner hv.cont).add (hu.cont.inner hv.dS.cont))
    (fun σ t hσ => ((hu.hasDerivAt_s hσ).inner ℝ (hv.hasDerivAt_s hσ)).congr_deriv
      (add_comm _ _)) hs
  refine h.congr_deriv ?_
  simp only [Ip]
  exact intervalIntegral.integral_add ((cont_inner hu.dS.cont hv.cont hs).intervalIntegrable _ _)
    ((cont_inner hu.cont hv.dS.cont hs).intervalIntegrable _ _)

lemma Ip_comm (u v : ℝ × ℝ → Vec n) (s : ℝ) : Ip u v s = Ip v u s := by
  simp only [Ip, real_inner_comm]

lemma Ip_self_nonneg (u : ℝ × ℝ → Vec n) (s : ℝ) : 0 ≤ Ip u u s :=
  intervalIntegral.integral_nonneg zero_le_one fun _ _ => real_inner_self_nonneg

end HDecay

end HD_e

section HD_f

/-! Bounds on the coefficient field `S` from its `C^∞` convergence to `S∞`. -/

open scoped Topology ContDiff
open Set Filter CauchyRiemannIndex

namespace HDecay

variable {n : ℕ}

lemma pS_le0 (g : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : |pS g x| ≤ ‖iteratedFDeriv ℝ 1 g x‖ := by
  rw [norm_iteratedFDeriv_one]
  have := (fderiv ℝ g x).le_opNorm (1, 0)
  simpa only [pS, ge_iff_le, Real.norm_eq_abs, Prod.norm_mk, norm_one, norm_zero, zero_le_one,
    sup_of_le_left, mul_one] using this

lemma pS_pS_le (g : ℝ × ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (x : ℝ × ℝ) :
    |pS (pS g) x| ≤ ‖iteratedFDeriv ℝ 2 g x‖ := by
  have hd2 : DifferentiableAt ℝ (fderiv ℝ g) x :=
    ((hg.fderiv_right (m := 1) (WithTop.coe_le_coe.2 le_top)).differentiable one_ne_zero) x
  have h : pS (pS g) x = fderiv ℝ (fderiv ℝ g) x (1, 0) (1, 0) := by
    show fderiv ℝ (fun y => fderiv ℝ g y (1, 0)) x (1, 0) = _
    rw [show (fun y => fderiv ℝ g y (1, 0)) = fun y => (fderiv ℝ g y) ((fun _ => ((1:ℝ), (0:ℝ))) y)
      from rfl, fderiv_clm_apply hd2 (differentiableAt_const _)]
    simp only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.comp_zero, zero_add,
      ContinuousLinearMap.flip_apply]
  rw [h, show fderiv ℝ (fderiv ℝ g) x (1, 0) (1, 0) = iteratedFDeriv ℝ 2 g x ![(1, 0), (1, 0)] by
    rw [iteratedFDeriv_two_apply]; rfl]
  have := (iteratedFDeriv ℝ 2 g x).le_opNorm ![(1, 0), (1, 0)]
  simpa only [ge_iff_le, Real.norm_eq_abs, Fin.prod_univ_two, Fin.isValue, Matrix.cons_val_zero,
    Prod.norm_mk, norm_one, norm_zero, zero_le_one, sup_of_le_left, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, mul_one] using this

/-- `∂ₛ` of an operator field built from a matrix field. -/
lemma hasFDerivAt_TL (S : ℝ × ℝ → Mat n) (hS : ∀ i j, Differentiable ℝ (fun p => S p i j))
    (x : ℝ × ℝ) : pS (fun p => TL n (S p)) x =
      TL n (Matrix.of fun i j => pS (fun p => S p i j) x) := by
  have hd : HasFDerivAt (fun p => TL n (S p))
      (∑ i, ∑ j, (fderiv ℝ (fun p => S p i j) x).smulRight (TL n (Matrix.single i j 1))) x := by
    have hsum : (fun p => TL n (S p)) = fun p => ∑ i, ∑ j, S p i j • TL n (Matrix.single i j 1) :=
      funext fun p => TL_eq_sum _
    rw [hsum]
    refine HasFDerivAt.fun_sum fun i _ => HasFDerivAt.fun_sum fun j _ => ?_
    exact ((hS i j) x).hasFDerivAt.smul_const (TL n (Matrix.single i j (1:ℝ)))
  refine (congrArg (fun L => L (1, 0)) hd.fderiv).trans (Eq.trans ?_ (TL_eq_sum _).symm)
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.smulRight_apply,
    Matrix.of_apply, pS]

lemma contDiff_of_pS (S : ℝ × ℝ → Mat n) (hS : ∀ i j, ContDiff ℝ ∞ (fun p => S p i j)) :
    ∀ i j, ContDiff ℝ ∞ (fun p => (Matrix.of fun i j => pS (fun p => S p i j) p) i j) := by
  intro i j
  simp only [Matrix.of_apply, pS]
  exact (hS i j).fderiv_right (m := ∞) (by simp) |>.clm_apply contDiff_const

/-- entrywise smallness gives operator smallness -/
lemma op_small : ∃ c, 0 < c ∧ ∀ (M : Mat n) (δ : ℝ), 0 ≤ δ → (∀ i j, |M i j| ≤ δ) →
    ‖TL n M‖ ≤ c * δ := by
  set c0 := ∑ i, ∑ j, ‖TL n (Matrix.single i j (1:ℝ))‖
  have hc0 : 0 ≤ c0 := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
  refine ⟨1 + c0, by linarith only [hc0], fun M δ hδ hM => (norm_TL_le M).trans ?_⟩
  calc ∑ i, ∑ j, |M i j| * ‖TL n (Matrix.single i j 1)‖
      ≤ ∑ i, ∑ j, δ * ‖TL n (Matrix.single i j (1:ℝ))‖ :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_right (hM i j) (norm_nonneg _)
    _ = δ * c0 := by simp only [c0, Finset.mul_sum]
    _ ≤ (1 + c0) * δ := by nlinarith only [hδ, hc0]

lemma pS_snd (f : ℝ → ℝ) (hf : Differentiable ℝ f) (x : ℝ × ℝ) : pS (fun p => f p.2) x = 0 := by
  have : HasFDerivAt (fun p : ℝ × ℝ => f p.2) ((fderiv ℝ f x.2).comp (ContinuousLinearMap.snd ℝ ℝ ℝ)) x :=
    (hf x.2).hasFDerivAt.comp x hasFDerivAt_snd
  simp only [pS, this.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd',
    fderiv_eq_smul_deriv, smul_eq_mul, zero_mul]

lemma pS_entry (S : ℝ × ℝ → Mat n) (hS : ∀ i j, ContDiff ℝ ∞ (fun p => S p i j))
    (Sinf : ℝ → Mat n) (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j)) (i j) :
    pS (fun p => S p i j) = pS (fun p => S p i j - Sinf p.2 i j) := by
  funext x
  have h1 : DifferentiableAt ℝ (fun p : ℝ × ℝ => S p i j) x := ((hS i j).differentiable (by simp)) x
  have h2 : DifferentiableAt ℝ (fun p : ℝ × ℝ => Sinf p.2 i j) x :=
    (((hSinf' i j).differentiable (by simp)) x.2).comp x differentiableAt_snd
  have := pS_snd (fun t => Sinf t i j) ((hSinf' i j).differentiable (by simp)) x
  simp only [pS] at this ⊢
  rw [fderiv_fun_sub h1 h2]
  simp only [sub_apply, this, sub_zero]

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

lemma pS_sub {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {u v : ℝ × ℝ → F}
    (hu : Sm u) (hv : Sm v) {x} (hx : x ∈ Ω) : pS (u - v) x = pS u x - pS v x := by
  rw [sub_eq_add_neg, pS_add hu hv.neg hx, pS_neg, ← sub_eq_add_neg]

section energy

variable (A : ℝ × ℝ → Op n) (η : ℝ × ℝ → Vec n)

/-- residual `∂ₛη + J₀ ∂ₜη + A η` -/
noncomputable def res (x : ℝ × ℝ) : Vec n := pS η x + Jop n (pT η x) + A x (η x)

variable {A η}

lemma Sm.jop {v : ℝ × ℝ → Vec n} (hv : Sm v) : Sm (fun x => Jop n (v x)) :=
  (contDiffOn_const (c := Jop n)).clm_apply hv

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

lemma pS_congr {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {u v : ℝ × ℝ → F}
    (h : EqOn u v Ω) {x} (hx : x ∈ Ω) : pS u x = pS v x := by
  have : u =ᶠ[𝓝 x] v := Filter.eventuallyEq_of_mem (isOpen_Ω.mem_nhds hx) h
  simp only [pS, this.fderiv_eq]

end HDecay

end HD_i

section HD_j

/-! One-variable lemmas used to pass from energy inequalities to decay. -/

open scoped Topology
open Set Filter MeasureTheory

namespace HDecay

lemma int_exp_le {c : ℝ} (hc : 0 < c) {a b : ℝ} (hab : a ≤ b) :
    ∫ x in a..b, Real.exp (-(c * x)) ≤ Real.exp (-(c * a)) / c := by
  have hd : ∀ x ∈ uIcc a b, HasDerivAt (fun x => -Real.exp (-(c * x)) / c) (Real.exp (-(c * x))) x := by
    intro x _
    have := (((hasDerivAt_id x).const_mul c).neg.exp.neg).div_const c
    refine this.congr_deriv ?_
    simp only [id, mul_one, Pi.neg_apply]
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).intervalIntegrable _ _)]
  have := Real.exp_pos (-(c * b))
  have e : -Real.exp (-(c * b)) / c - -Real.exp (-(c * a)) / c =
      Real.exp (-(c * a)) / c - Real.exp (-(c * b)) / c := by ring
  rw [e]
  have : 0 < Real.exp (-(c * b)) / c := by positivity
  linarith

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

lemma cs_real (a b : ℝ → ℝ) (ha : Continuous a) (hb : Continuous b) :
    (∫ t in (0:ℝ)..1, a t * b t) ^ 2 ≤ (∫ t in (0:ℝ)..1, a t ^ 2) * ∫ t in (0:ℝ)..1, b t ^ 2 := by
  have iaa : IntervalIntegrable (fun t => a t ^ 2) volume 0 1 := (ha.pow 2).intervalIntegrable _ _
  have ibb : IntervalIntegrable (fun t => b t ^ 2) volume 0 1 := (hb.pow 2).intervalIntegrable _ _
  have iab : IntervalIntegrable (fun t => a t * b t) volume 0 1 := (ha.mul hb).intervalIntegrable _ _
  have h : ∀ x : ℝ, 0 ≤ (∫ t in (0:ℝ)..1, b t ^ 2) * x * x + 2 * (∫ t in (0:ℝ)..1, a t * b t) * x +
      ∫ t in (0:ℝ)..1, a t ^ 2 := by
    intro x
    have h0 : 0 ≤ ∫ t in (0:ℝ)..1, (a t + x * b t) ^ 2 :=
      intervalIntegral.integral_nonneg zero_le_one fun t _ => sq_nonneg _
    have e : ∫ t in (0:ℝ)..1, (a t + x * b t) ^ 2 = ∫ t in (0:ℝ)..1,
        (a t ^ 2 + (2 * x) * (a t * b t) + (x * x) * b t ^ 2) := by
      congr 1; funext t; ring
    rw [e, intervalIntegral.integral_add (iaa.add (iab.const_mul _)) (ibb.const_mul _),
      intervalIntegral.integral_add iaa (iab.const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul] at h0
    linarith
  set P := ∫ t in (0:ℝ)..1, b t ^ 2
  set Q := ∫ t in (0:ℝ)..1, a t * b t
  set R := ∫ t in (0:ℝ)..1, a t ^ 2
  have h' : ∀ x : ℝ, 0 ≤ P * (x * x) + (2 * Q) * x + R := fun x => by
    have := h x; rw [← mul_assoc]; exact this
  have := discrim_le_zero h'
  simp only [discrim] at this
  nlinarith

/-- `∫ |u| |v| ≤ √(Ip u u) √(Ip v v)` -/
lemma cs_Ip {u v : ℝ × ℝ → Vec n} (hu : ContinuousOn u Ω) (hv : ContinuousOn v Ω) {s : ℝ}
    (hs : 0 < s) : ∫ t in (0:ℝ)..1, ‖u (s, t)‖ * ‖v (s, t)‖ ≤
      Real.sqrt (Ip u u s) * Real.sqrt (Ip v v s) := by
  have hu' := (cont_slice hu hs).norm
  have hv' := (cont_slice hv hs).norm
  have hc := cs_real _ _ hu' hv'
  have e1 : Ip u u s = ∫ t in (0:ℝ)..1, ‖u (s, t)‖ ^ 2 := by
    simp only [Ip, real_inner_self_eq_norm_sq]
  have e2 : Ip v v s = ∫ t in (0:ℝ)..1, ‖v (s, t)‖ ^ 2 := by
    simp only [Ip, real_inner_self_eq_norm_sq]
  rw [← e1, ← e2] at hc
  have h0 : 0 ≤ ∫ t in (0:ℝ)..1, ‖u (s, t)‖ * ‖v (s, t)‖ :=
    intervalIntegral.integral_nonneg zero_le_one fun t _ => by positivity
  rw [← Real.sqrt_mul (Ip_self_nonneg u s)]
  exact Real.le_sqrt_of_sq_le hc

lemma cs_Ip' {u v : ℝ × ℝ → Vec n} (hu : ContinuousOn u Ω) (hv : ContinuousOn v Ω) {s : ℝ}
    (hs : 0 < s) : Ip u v s ^ 2 ≤ Ip u u s * Ip v v s := by
  have h1 : |Ip u v s| ≤ ∫ t in (0:ℝ)..1, ‖u (s, t)‖ * ‖v (s, t)‖ := by
    refine (intervalIntegral.abs_integral_le_integral_abs zero_le_one).trans ?_
    exact intervalIntegral.integral_mono_on zero_le_one
      ((cont_slice (hu.inner hv) hs).abs.intervalIntegrable _ _)
      (((cont_slice hu hs).norm.mul (cont_slice hv hs).norm).intervalIntegrable _ _)
      fun t _ => abs_real_inner_le_norm _ _
  have h2 := (h1.trans (cs_Ip hu hv hs))
  have h3 := sq_le_sq' (neg_le_of_abs_le h2) (le_of_abs_le h2)
  rw [mul_pow, Real.sq_sqrt (Ip_self_nonneg _ _), Real.sq_sqrt (Ip_self_nonneg _ _)] at h3
  exact h3

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

theorem coeff_exp (S : ℝ × ℝ → Mat n) (hS : ∀ i j, ContDiff ℝ ∞ (fun p => S p i j))
    (Sinf : ℝ → Mat n) (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j)) (d : ℝ)
    (hSas : FiniteEnergyPlane.IsExpAsymptoticTo S Sinf d) :
    ∃ K > 0, ∃ s1 > 0, ∀ s ≥ s1, ∀ t, ‖TL n (S (s, t)) - TL n (Sinf t)‖ ≤ K * Real.exp (-(d * s)) ∧
      ‖pS (fun p => TL n (S p)) (s, t)‖ ≤ K * Real.exp (-(d * s)) ∧
      ‖pS (pS (fun p => TL n (S p))) (s, t)‖ ≤ K * Real.exp (-(d * s)) := by
  obtain ⟨c, hc, hcM⟩ := op_small (n := n)
  have h := fun i j (m : ℕ) => (hSas i j).2 m
  choose Cf s1f hs1f using h
  set Cm := ∑ i, ∑ j, (|Cf i j 0| + |Cf i j 1| + |Cf i j 2|) + 1
  set s1 := ∑ i, ∑ j, (|s1f i j 0| + |s1f i j 1| + |s1f i j 2|) + 1
  have hsum : ∀ (g : Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℕ → ℝ) i j,
      |g i j 0| + |g i j 1| + |g i j 2| ≤ ∑ i, ∑ j, (|g i j 0| + |g i j 1| + |g i j 2|) := by
    intro g i j
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, (|g i j 0| + |g i j 1| +
      |g i j 2|)) (fun i _ => by positivity) (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun j => |g i j 0| + |g i j 1| + |g i j 2|)
      (fun j _ => by positivity) (Finset.mem_univ j)
  have hle : ∀ (g : Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℕ → ℝ) i j, g i j 0 ≤ ∑ i, ∑ j, (|g i j 0| + |g i j 1| + |g i j 2|) + 1 ∧
      g i j 1 ≤ ∑ i, ∑ j, (|g i j 0| + |g i j 1| + |g i j 2|) + 1 ∧
      g i j 2 ≤ ∑ i, ∑ j, (|g i j 0| + |g i j 1| + |g i j 2|) + 1 := by
    intro g i j
    have := hsum g i j
    have := le_abs_self (g i j 0); have := le_abs_self (g i j 1)
    have := le_abs_self (g i j 2); have := abs_nonneg (g i j 0)
    have := abs_nonneg (g i j 1); have := abs_nonneg (g i j 2)
    refine ⟨by linarith, by linarith, by linarith⟩
  have hs1pos : 0 < s1 := by
    have : 0 ≤ ∑ i, ∑ j, (|s1f i j 0| + |s1f i j 1| + |s1f i j 2|) := by positivity
    linarith
  have hCm : 0 < Cm := by
    have : 0 ≤ ∑ i, ∑ j, (|Cf i j 0| + |Cf i j 1| + |Cf i j 2|) := by positivity
    linarith
  refine ⟨c * Cm, by positivity, s1, hs1pos, fun s hs t => ⟨?_, ?_, ?_⟩⟩
  · rw [← map_sub, mul_assoc]
    refine hcM _ _ (by positivity) fun i j => ?_
    have := hs1f i j 0 s ((hle s1f i j).1.trans hs) t
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    simp only [Matrix.sub_apply]
    exact this.trans (mul_le_mul_of_nonneg_right (hle Cf i j).1 (Real.exp_pos _).le)
  · rw [hasFDerivAt_TL S (fun i j => (hS i j).differentiable (by simp)), mul_assoc]
    refine hcM _ _ (by positivity) fun i j => ?_
    have := hs1f i j 1 s ((hle s1f i j).2.1.trans hs) t
    simp only [Matrix.of_apply, pS_entry S hS Sinf hSinf']
    exact ((pS_le0 _ _).trans this).trans
      (mul_le_mul_of_nonneg_right (hle Cf i j).2.1 (Real.exp_pos _).le)
  · have hfun : pS (fun p => TL n (S p)) = fun p => TL n (Matrix.of fun i j => pS (fun p => S p i j) p) :=
      funext (hasFDerivAt_TL S (fun i j => (hS i j).differentiable (by simp)))
    rw [hfun, hasFDerivAt_TL _ (fun i j => (contDiff_of_pS S hS i j).differentiable (by simp)),
      mul_assoc]
    refine hcM _ _ (by positivity) fun i j => ?_
    have := hs1f i j 2 s ((hle s1f i j).2.2.trans hs) t
    simp only [Matrix.of_apply, pS_entry S hS Sinf hSinf']
    have hg : ContDiff ℝ ∞ (fun p : ℝ × ℝ => S p i j - Sinf p.2 i j) :=
      (hS i j).sub ((hSinf' i j).comp contDiff_snd)
    exact ((pS_pS_le _ hg _).trans this).trans
      (mul_le_mul_of_nonneg_right (hle Cf i j).2.2 (Real.exp_pos _).le)

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

noncomputable def Fz (s : ℝ) : ℝ := Ip ζ ζ s
noncomputable def Dz (s : ℝ) : ℝ := Ip ζ (pS ζ) s
noncomputable def Gz (s : ℝ) : ℝ := Ip (pS ζ) (pS ζ) s
noncomputable def αz (s : ℝ) : ℝ := Dz ζ s / Fz ζ s
noncomputable def qz (s : ℝ) : ℝ := Gz ζ s / Fz ζ s - (αz ζ s) ^ 2
variable {A ζ}

lemma Fz_hasDerivAt (hζ : Sm ζ) {s : ℝ} (hs : 0 < s) : HasDerivAt (Fz ζ) (2 * Dz ζ s) s :=
  (Ip_hasDerivAt hζ hζ hs).congr_deriv (by simp only [Dz]; rw [Ip_comm (pS ζ) ζ]; ring)

lemma Fz_hasDerivAt' (hζ : Sm ζ) {s : ℝ} (hs : 0 < s) (hF : 0 < Fz ζ s) :
    HasDerivAt (Fz ζ) (2 * αz ζ s * Fz ζ s) s :=
  (Fz_hasDerivAt hζ hs).congr_deriv (by simp only [αz]; field_simp)

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

end HDecay

end AF_j

section AF_k

/-! The gap inequality `|α - μ| ≤ κ (q + ε)` near `μ`, for a solution of the linear CR equation. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

end HDecay

end AF_k

section AF_l

/-! Exponential convergence of `α` to a limit `μ ≤ δ₀` for a solution. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

end HDecay

end AF_l

section AF_m

/-! A one-dimensional mean value inequality: `f'' ≥ -g`, `f ≥ 0` ⇒ `f(a) ≤ ∫ f + ∫ g`. -/

open scoped Topology
open Set Filter MeasureTheory

namespace HDecay

lemma le_of_deriv_nonneg_Icc (f f' : ℝ → ℝ) {x y : ℝ} (hxy : x ≤ y)
    (hd : ∀ z ∈ Icc x y, HasDerivAt f (f' z) z) (h : ∀ z ∈ Icc x y, 0 ≤ f' z) : f x ≤ f y := by
  have hc : ContinuousOn f (Icc x y) := fun z hz => (hd z hz).continuousAt.continuousWithinAt
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc x y) hc
    (fun z hz => (hd z (interior_subset hz)).hasDerivWithinAt)
    (fun z hz => h z (interior_subset hz)) ⟨le_rfl, hxy⟩ ⟨hxy, le_rfl⟩ hxy

end HDecay

end AF_m

section AF_n

/-! Pointwise decay of `‖∂ₛζ - μζ‖²_{L²}` relative to `‖ζ‖²_{L²}`. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

/-- `∂ₛζ - μζ` -/
noncomputable def ηm (ζ : ℝ × ℝ → Vec n) (μ : ℝ) : ℝ × ℝ → Vec n := fun x => pS ζ x - μ • ζ x

lemma pS_smul' {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (c : ℝ) {u : ℝ × ℝ → F}
    (hu : Sm u) {x} (hx : x ∈ Ω) : pS (fun y => c • u y) x = c • pS u x := by
  simp only [pS]
  rw [show (fun y => c • u y) = c • u from rfl, fderiv_const_smul (hu.diffAt hx)]
  rfl

lemma pT_smul' {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (c : ℝ) {u : ℝ × ℝ → F}
    (hu : Sm u) {x} (hx : x ∈ Ω) : pT (fun y => c • u y) x = c • pT u x := by
  simp only [pT]
  rw [show (fun y => c • u y) = c • u from rfl, fderiv_const_smul (hu.diffAt hx)]
  rfl

lemma pT_sub' {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {u v : ℝ × ℝ → F}
    (hu : Sm u) (hv : Sm v) {x} (hx : x ∈ Ω) : pT (u - v) x = pT u x - pT v x := by
  rw [sub_eq_add_neg, pT_add hu hv.neg hx, pT_neg, ← sub_eq_add_neg]

lemma Sm.ηm {ζ : ℝ × ℝ → Vec n} (hζ : Sm ζ) (μ : ℝ) : Sm (ηm ζ μ) :=
  hζ.dS.sub (hζ.const_smul μ)

lemma TPer.ηm {ζ : ℝ × ℝ → Vec n} (hζ : TPer ζ) (μ : ℝ) : TPer (ηm ζ μ) := fun s t => by
  simp only [HDecay.ηm, hζ.pS s t, hζ s t]

lemma res_ηm {A : ℝ × ℝ → Op n} {ζ : ℝ × ℝ → Vec n} (hA : Sm A) (hζ : Sm ζ)
    (hres0 : ∀ x ∈ Ω, res A ζ x = 0) (μ : ℝ) :
    ∀ x ∈ Ω, res A (ηm ζ μ) x = -(pS A x (ζ x)) := by
  intro x hx
  have hpres0 : pS (res A ζ) x = 0 := by
    rw [pS_congr (v := fun _ => (0 : Vec n)) hres0 hx]
    simp [pS]
  have e : res A ζ = (pS ζ + fun y => Jop n (pT ζ y)) + fun y => A y (ζ y) := rfl
  rw [e, pS_add (hζ.dS.add hζ.dT.jop) (hA.apply hζ) hx, pS_add hζ.dS hζ.dT.jop hx,
    pS_constOp _ hζ.dT hx, pS_pT hζ hx, pS_apply hA hζ hx] at hpres0
  have h0 := hres0 x hx
  have e2 : ηm ζ μ = pS ζ - fun y => μ • ζ y := rfl
  have hsm : Sm fun y => μ • ζ y := hζ.const_smul μ
  simp only [res] at h0 ⊢
  rw [e2, pS_sub hζ.dS hsm hx, pT_sub' hζ.dS hsm hx, pS_smul' μ hζ hx, pT_smul' μ hζ hx]
  have : pS (pS ζ) x - μ • pS ζ x + Jop n (pT (pS ζ) x - μ • pT ζ x) +
      A x (pS ζ x - μ • ζ x) = (pS (pS ζ) x + Jop n (pT (pS ζ) x) + (pS A x (ζ x) + A x (pS ζ x)))
        - μ • (pS ζ x + Jop n (pT ζ x) + A x (ζ x)) - pS A x (ζ x) := by
    simp only [map_sub, map_smul, smul_add]; abel
  simp only [Pi.sub_apply]
  rw [this, hpres0, h0]; simp

end HDecay

end AF_n

section AF_o

/-! `‖∂ₛζ - μζ‖²_{L²}(s) ≤ C e^{-a s} ‖ζ‖²_{L²}(s)`. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

end HDecay

end AF_o

section AF_p

/-! The rescaled solution `χ = e^{-μs} ζ`: derivatives and two-sided `L²` bounds. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

/-- `χ = e^{-μs} ζ` -/
noncomputable def χr (ζ : ℝ × ℝ → Vec n) (μ : ℝ) : ℝ × ℝ → Vec n :=
  fun x => Real.exp (-(μ * x.1)) • ζ x

lemma contDiff_expw (μ : ℝ) : ContDiff ℝ ∞ (fun x : ℝ × ℝ => Real.exp (-(μ * x.1))) :=
  Real.contDiff_exp.comp ((contDiff_const.mul contDiff_fst).neg)

lemma Sm.χr {ζ : ℝ × ℝ → Vec n} (hζ : Sm ζ) (μ : ℝ) : Sm (χr ζ μ) :=
  (contDiff_expw μ).contDiffOn.smul hζ

lemma TPer.χr {ζ : ℝ × ℝ → Vec n} (hζ : TPer ζ) (μ : ℝ) : TPer (χr ζ μ) := fun s t => by
  simp only [HDecay.χr, hζ s t]

lemma pS_χr {ζ : ℝ × ℝ → Vec n} (hζ : Sm ζ) (μ : ℝ) {s t : ℝ} (hs : 0 < s) :
    pS (χr ζ μ) (s, t) = Real.exp (-(μ * s)) • ηm ζ μ (s, t) := by
  have h1 := (hζ.χr μ).hasDerivAt_s (t := t) hs
  have he : HasDerivAt (fun σ : ℝ => Real.exp (-(μ * σ))) (Real.exp (-(μ * s)) * (-μ)) s := by
    have := ((hasDerivAt_id s).const_mul μ).neg.exp
    simpa using this
  have h2 := he.smul (hζ.hasDerivAt_s (t := t) hs)
  have := h1.unique h2
  rw [this]
  simp only [ηm, smul_sub, smul_smul]
  module

lemma pT_χr {ζ : ℝ × ℝ → Vec n} (hζ : Sm ζ) (μ : ℝ) {s t : ℝ} (hs : 0 < s) :
    pT (χr ζ μ) (s, t) = Real.exp (-(μ * s)) • pT ζ (s, t) := by
  have h1 := (hζ.χr μ).hasDerivAt_t (t := t) hs
  have h2 := (hζ.hasDerivAt_t (t := t) hs).const_smul (Real.exp (-(μ * s)))
  exact h1.unique h2

lemma Ip_χr (ζ : ℝ × ℝ → Vec n) (μ s : ℝ) :
    Ip (χr ζ μ) (χr ζ μ) s = Real.exp (-(2 * μ * s)) * Fz ζ s := by
  simp only [Ip, Fz, χr, real_inner_smul_left, real_inner_smul_right]
  rw [← intervalIntegral.integral_const_mul]
  congr 1; funext t
  rw [← mul_assoc, ← Real.exp_add]; ring_nf

lemma Ip_pSχr {ζ : ℝ × ℝ → Vec n} (hζ : Sm ζ) (μ : ℝ) {s : ℝ} (hs : 0 < s) :
    Ip (pS (χr ζ μ)) (pS (χr ζ μ)) s = Real.exp (-(2 * μ * s)) * Ip (ηm ζ μ) (ηm ζ μ) s := by
  simp only [Ip, pS_χr hζ μ hs, real_inner_smul_left, real_inner_smul_right]
  rw [← intervalIntegral.integral_const_mul]
  congr 1; funext t
  rw [← mul_assoc, ← Real.exp_add]; ring_nf

/-- the equation for `χ`, in the form needed for the gap estimate -/
lemma χr_eq {A : ℝ × ℝ → Op n} {ζ : ℝ × ℝ → Vec n} (hζ : Sm ζ)
    (hres0 : ∀ x ∈ Ω, res A ζ x = 0) (Sinf : ℝ → Mat n) (μ : ℝ) {s : ℝ} (hs : 0 < s) (t : ℝ) :
    -(Jop n (pT (χr ζ μ) (s, t))) - TL n (Sinf t) (χr ζ μ (s, t)) - μ • χr ζ μ (s, t) =
      pS (χr ζ μ) (s, t) + (A (s, t) - TL n (Sinf t)) (χr ζ μ (s, t)) := by
  have h0 := hres0 (s, t) (mem_Ω hs)
  rw [pT_χr hζ μ hs, pS_χr hζ μ hs]
  show -(Jop n (Real.exp (-(μ * s)) • pT ζ (s, t))) - TL n (Sinf t) (Real.exp (-(μ * s)) • ζ (s, t)) -
    μ • (Real.exp (-(μ * s)) • ζ (s, t)) = Real.exp (-(μ * s)) • ηm ζ μ (s, t) +
      (A (s, t) - TL n (Sinf t)) (Real.exp (-(μ * s)) • ζ (s, t))
  simp only [res] at h0
  have e : pS ζ (s, t) = -(Jop n (pT ζ (s, t))) - A (s, t) (ζ (s, t)) := by
    rw [eq_sub_iff_add_eq, eq_neg_iff_add_eq_zero, ← h0]; abel
  simp only [ηm, e, map_smul, ContinuousLinearMap.sub_apply, smul_sub, smul_neg, smul_smul]
  module

lemma H_bounds (F α : ℝ → ℝ) (μ a Cr s3 : ℝ) (ha : 0 < a) (hCr : 0 ≤ Cr)
    (hd : ∀ s ≥ s3, HasDerivAt F (2 * α s * F s) s) (hpos : ∀ s ≥ s3, 0 < F s)
    (hrate : ∀ s ≥ s3, |α s - μ| ≤ Cr * Real.exp (-(a * s))) :
    ∃ Hlo > 0, ∃ Hhi, ∀ s ≥ s3, Hlo ≤ Real.exp (-(2 * μ * s)) * F s ∧
      Real.exp (-(2 * μ * s)) * F s ≤ Hhi := by
  set φ : ℝ → ℝ := fun x => 2 * Cr / a * Real.exp (-(a * x))
  have hφd : ∀ x, HasDerivAt φ (-(2 * Cr * Real.exp (-(a * x)))) x := by
    intro x
    have h0 : HasDerivAt (fun y : ℝ => -(a * y)) (-a) x :=
      ((hasDerivAt_id' x).const_mul a).neg.congr_deriv (by ring)
    refine (h0.exp.const_mul (2 * Cr / a)).congr_deriv ?_
    field_simp
  have hφ0 : ∀ x, 0 ≤ φ x := fun x => by positivity
  have hφle : ∀ x ≥ s3, φ x ≤ φ s3 := fun x hx => by
    simp only [φ]; gcongr
  set H : ℝ → ℝ := fun x => Real.exp (-(2 * μ * x)) * F x
  have hHd : ∀ x ≥ s3, HasDerivAt H (2 * (α x - μ) * H x) x := by
    intro x hx
    have h0 : HasDerivAt (fun y : ℝ => -(2 * μ * y)) (-(2 * μ)) x :=
      ((hasDerivAt_id' x).const_mul (2 * μ)).neg.congr_deriv (by ring)
    refine (h0.exp.mul (hd x hx)).congr_deriv ?_
    simp only [H]; ring
  set H3 := H s3
  have hH3 : 0 < H3 := mul_pos (Real.exp_pos _) (hpos s3 le_rfl)
  refine ⟨H3 * Real.exp (-φ s3), by positivity, H3 * Real.exp (φ s3), fun s hs => ⟨?_, ?_⟩⟩
  · have key := le_of_deriv_nonneg_Icc (fun x => H x * Real.exp (-φ x))
      (fun x => H x * Real.exp (-φ x) * (2 * (α x - μ) + 2 * Cr * Real.exp (-(a * x)))) hs
      (fun x hx => ((hHd x hx.1).mul (hφd x).neg.exp).congr_deriv (by simp only [Pi.neg_apply]; ring))
      (fun x hx => by
        have h1 := hrate x hx.1
        have h2 : 0 < H x := mul_pos (Real.exp_pos _) (hpos x hx.1)
        have : 0 ≤ 2 * (α x - μ) + 2 * Cr * Real.exp (-(a * x)) := by
          linarith [neg_abs_le (α x - μ)]
        positivity)
    have : H s * Real.exp (-φ s) ≤ H s := by
      have : 0 < H s := mul_pos (Real.exp_pos _) (hpos s hs)
      have : Real.exp (-φ s) ≤ 1 := Real.exp_le_one_iff.2 (by linarith [hφ0 s])
      nlinarith
    show H3 * Real.exp (-φ s3) ≤ H s
    linarith
  · have key := le_of_deriv_nonneg_Icc (fun x => -(H x * Real.exp (φ x)))
      (fun x => -(H x * Real.exp (φ x) * (2 * (α x - μ) - 2 * Cr * Real.exp (-(a * x))))) hs
      (fun x hx => ((hHd x hx.1).mul (hφd x).exp).neg.congr_deriv (by ring))
      (fun x hx => by
        have h1 := hrate x hx.1
        have h2 : 0 < H x := mul_pos (Real.exp_pos _) (hpos x hx.1)
        have : 2 * (α x - μ) - 2 * Cr * Real.exp (-(a * x)) ≤ 0 := by
          linarith [le_abs_self (α x - μ)]
        have : 0 ≤ H x * Real.exp (φ x) * -(2 * (α x - μ) - 2 * Cr * Real.exp (-(a * x))) := by
          have : 0 ≤ -(2 * (α x - μ) - 2 * Cr * Real.exp (-(a * x))) := by linarith
          positivity
        linarith)
    simp only [neg_le_neg_iff] at key
    have : H s ≤ H s * Real.exp (φ s) := by
      have : 0 < H s := mul_pos (Real.exp_pos _) (hpos s hs)
      have : 1 ≤ Real.exp (φ s) := Real.one_le_exp (hφ0 s)
      nlinarith
    show H s ≤ H3 * Real.exp (φ s3)
    linarith

end HDecay

end AF_p

section AF_q

/-! `∫ |χ(s₁) - χ(s₀)| ≤ ∫_{s₀}^{s₁} ‖∂ₛχ‖_{L²}`. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

lemma int_norm_le_sqrt' {v : ℝ × ℝ → Vec n} (hv : Sm v) {s : ℝ} (hs : 0 < s) :
    ∫ t in (0:ℝ)..1, ‖v (s, t)‖ ≤ Real.sqrt (Ip v v s) := by
  apply Real.le_sqrt_of_sq_le
  have := sq_integral_le (fun t => ‖v (s, t)‖) (cont_slice hv.cont hs).norm
  simp only [Ip, real_inner_self_eq_norm_sq]
  exact this

theorem diff_bound {χ : ℝ × ℝ → Vec n} (hχ : Sm χ) {s0 s1 : ℝ} (hs0 : 0 < s0) (h01 : s0 ≤ s1) :
    ∫ t in (0:ℝ)..1, ‖χ (s1, t) - χ (s0, t)‖ ≤
      ∫ σ in s0..s1, Real.sqrt (Ip (pS χ) (pS χ) σ) := by
  set w : ℝ × ℝ → Vec n := fun x => χ x - χ (s0, x.2)
  have hg : ContDiff ℝ ∞ (fun x : ℝ × ℝ => ((s0, x.2) : ℝ × ℝ)) :=
    contDiff_const.prodMk contDiff_snd
  have hw : Sm w := hχ.sub (hχ.comp hg.contDiffOn fun x _ => mem_Ω hs0)
  have hpw : ∀ σ > 0, ∀ t, pS w (σ, t) = pS χ (σ, t) := by
    intro σ hσ t
    have h1 := hw.hasDerivAt_s (t := t) hσ
    have h2 := (hχ.hasDerivAt_s (t := t) hσ).sub_const (χ (s0, t))
    exact h1.unique h2
  have hIp : ∀ σ > 0, Ip w (pS w) σ = Ip w (pS χ) σ := by
    intro σ hσ; simp only [Ip, hpw σ hσ]
  have hIpp : ∀ σ > 0, Ip (pS w) (pS w) σ = Ip (pS χ) (pS χ) σ := by
    intro σ hσ; simp only [Ip, hpw σ hσ]
  set M := Ip w w
  set E := Ip (pS χ) (pS χ)
  have hMd : ∀ σ > 0, HasDerivAt M (2 * Ip w (pS χ) σ) σ := fun σ hσ =>
    (Ip_hasDerivAt hw hw hσ).congr_deriv (by rw [Ip_comm (pS w) w, hIp σ hσ]; ring)
  have hEd : ∀ σ > 0, HasDerivAt E (Ip (pS (pS χ)) (pS χ) σ + Ip (pS χ) (pS (pS χ)) σ) σ :=
    fun σ hσ => Ip_hasDerivAt hχ.dS hχ.dS hσ
  have hEc : ContinuousOn (fun σ => Real.sqrt (E σ)) (Ioi 0) :=
    fun σ hσ => ((hEd σ hσ).continuousAt.sqrt).continuousWithinAt
  have hCS : ∀ σ > 0, |Ip w (pS χ) σ| ≤ Real.sqrt (M σ) * Real.sqrt (E σ) := by
    intro σ hσ
    have h := cs_Ip' hw.cont hw.dS.cont hσ
    rw [hIp σ hσ, hIpp σ hσ] at h
    rw [← Real.sqrt_mul (Ip_self_nonneg _ _)]
    exact Real.abs_le_sqrt h
  have hM0 : M s0 = 0 := by simp [M, Ip, w]
  have hsub : Icc s0 s1 ⊆ Ioi 0 := fun x hx => lt_of_lt_of_le hs0 hx.1
  have hΓ : ∀ x ∈ Icc s0 s1, HasDerivAt (fun x => ∫ σ in s0..x, Real.sqrt (E σ))
      (Real.sqrt (E x)) x := by
    intro x hx
    have hx0 : 0 < x := hsub hx
    refine intervalIntegral.integral_hasDerivAt_right ?_
      (hEc.stronglyMeasurableAtFilter isOpen_Ioi x hx0) (hEc.continuousAt (isOpen_Ioi.mem_nhds hx0))
    refine (hEc.mono ?_).intervalIntegrable
    intro y hy
    rw [uIcc_of_le hx.1] at hy
    exact lt_of_lt_of_le hs0 hy.1
  have key : ∀ l > 0, Real.sqrt (M s1 + l) ≤ Real.sqrt l + ∫ σ in s0..s1, Real.sqrt (E σ) := by
    intro l hl
    have hR := le_of_deriv_nonneg_Icc
      (fun x => -(Real.sqrt (M x + l) - ∫ σ in s0..x, Real.sqrt (E σ)))
      (fun x => -((2 * Ip w (pS χ) x) / (2 * Real.sqrt (M x + l)) - Real.sqrt (E x))) h01
      (fun x hx => by
        have hx0 := hsub hx
        have hpos : 0 < M x + l := by have := Ip_self_nonneg w x; linarith
        exact (((hMd x hx0).add_const l).sqrt hpos.ne').sub (hΓ x hx) |>.neg)
      (fun x hx => by
        have hx0 := hsub hx
        have hMn := Ip_self_nonneg w x
        have hpos : 0 < M x + l := by linarith
        have hsq : 0 < Real.sqrt (M x + l) := Real.sqrt_pos.2 hpos
        have h1 := hCS x hx0
        have h2 : Real.sqrt (M x) ≤ Real.sqrt (M x + l) := Real.sqrt_le_sqrt (by linarith)
        have h3 : 2 * Ip w (pS χ) x / (2 * Real.sqrt (M x + l)) ≤ Real.sqrt (E x) := by
          rw [div_le_iff₀ (by positivity)]
          have := le_abs_self (Ip w (pS χ) x)
          have hE0 := Real.sqrt_nonneg (E x)
          nlinarith [mul_le_mul_of_nonneg_right h2 hE0]
        linarith)
    simp only [intervalIntegral.integral_same, sub_zero, hM0, zero_add, neg_le_neg_iff] at hR
    linarith
  have hM1 : Real.sqrt (M s1) ≤ ∫ σ in s0..s1, Real.sqrt (E σ) := by
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    have := key ((ε / 2) ^ 2) (by positivity)
    rw [Real.sqrt_sq (by positivity)] at this
    have h2 : Real.sqrt (M s1) ≤ Real.sqrt (M s1 + (ε / 2) ^ 2) :=
      Real.sqrt_le_sqrt (le_add_of_nonneg_right (by positivity))
    linarith
  exact (int_norm_le_sqrt' hw (lt_of_lt_of_le hs0 h01)).trans hM1

end HDecay

end AF_q

section AF_r

/-! Uniform exponential convergence of `χ(s, ·)` to a nonzero periodic solution `Ψ(·) k`. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

lemma exp_half_sq (b s : ℝ) : Real.sqrt (Real.exp (-(b * s))) = Real.exp (-(b / 2 * s)) := by
  rw [show -(b / 2 * s) = (-(b * s)) / 2 by ring, Real.exp_half]

theorem unif_conv (Sinf : ℝ → Mat n) (hS : IsSymLoop Sinf) (μ : ℝ) {χ : ℝ × ℝ → Vec n}
    (hχ : Sm χ) (hpχ : TPer χ) {s4 b P Q Hlo : ℝ} (hs4 : 0 < s4) (hb : 0 < b) (hP : 0 ≤ P)
    (hE : ∀ s ≥ s4, Ip (pS χ) (pS χ) s ≤ P * Real.exp (-(b * s)))
    (hG : ∀ s ≥ s4, ∫ t in (0:ℝ)..1,
      ‖-(Jop n (pT χ (s, t))) - TL n (Sinf t) (χ (s, t)) - μ • χ (s, t)‖ ≤ Q * Real.exp (-(b * s)))
    (hHlo : 0 < Hlo) (hH : ∀ s ≥ s4, Hlo ≤ Ip χ χ s) :
    ∃ Ψ : ℝ → Mat n, IsFundamentalSolution (fun t => Sinf t + μ • (1 : Mat n)) Ψ ∧
      (∀ t, Ψ (t + 1) = Ψ t * Ψ 1) ∧ ∃ k : Vec n, k ≠ 0 ∧ TL n (Ψ 1) k = k ∧
      ∃ Cc, ∀ s ≥ s4, ∀ t, ‖χ (s, t) - TL n (Ψ t) k‖ ≤ Cc * Real.exp (-(b / 2 * s)) := by
  obtain ⟨Ψ, hfund, hfl, ⟨Φ, hΦc, hΦΨ⟩, Cg, hCg0, hC⟩ := gap_ker _ (isSymLoop_shift Sinf hS μ)
  have hΨc : Continuous fun t => TL n (Ψ t) := by
    let _ : NormedAddCommGroup (Mat n) := Matrix.normedAddCommGroup
    let _ : NormedSpace ℝ (Mat n) := Matrix.normedSpace
    exact continuous_iff_continuousAt.2 fun t =>
      ((TL n).hasFDerivAt.comp_hasDerivAt t (hfund.2 t)).continuousAt
  obtain ⟨MP, hMP0, hMP⟩ := TL_cont_bound Ψ hΨc
  obtain ⟨MQ, hMQ0, hMQ⟩ := TL_cont_bound Φ hΦc
  have hQ : 0 ≤ Q := by
    have h1 := hG s4 le_rfl
    have h2 : 0 ≤ ∫ t in (0:ℝ)..1,
        ‖-(Jop n (pT χ (s4, t))) - TL n (Sinf t) (χ (s4, t)) - μ • χ (s4, t)‖ :=
      intervalIntegral.integral_nonneg zero_le_one fun _ _ => norm_nonneg _
    by_contra hc; push Not at hc
    have : Q * Real.exp (-(b * s4)) < 0 := mul_neg_of_neg_of_pos hc (Real.exp_pos _)
    linarith
  set δ : ℝ → ℝ := fun s => Cg * Q * Real.exp (-(b * s))
  have hk : ∀ s, ∃ k : Vec n, s4 ≤ s → TL n (Ψ 1) k = k ∧
      ∀ t, ‖χ (s, t) - TL n (Ψ t) k‖ ≤ δ s := by
    intro s
    by_cases hs : s4 ≤ s
    · have hs0 : 0 < s := lt_of_lt_of_le hs4 hs
      obtain ⟨k, hk1, hk2⟩ := hC (fun t => χ (s, t)) (fun t => pT χ (s, t))
        (fun t => hχ.hasDerivAt_t hs0) (cont_slice hχ.dT.cont hs0) (hpχ.periodic s)
      refine ⟨k, fun _ => ⟨hk1, fun t => (hk2 t).trans ?_⟩⟩
      have e : ∫ τ in (0:ℝ)..1, ‖-(Jop n (pT χ (s, τ))) -
          TL n (Sinf τ + μ • (1 : Mat n)) (χ (s, τ))‖ = ∫ τ in (0:ℝ)..1,
          ‖-(Jop n (pT χ (s, τ))) - TL n (Sinf τ) (χ (s, τ)) - μ • χ (s, τ)‖ := by
        congr 1; funext τ; rw [TL_shift, sub_sub]
      rw [e]
      calc Cg * _ ≤ Cg * (Q * Real.exp (-(b * s))) := mul_le_mul_of_nonneg_left (hG s hs) hCg0
        _ = δ s := by simp only [δ]; ring
    · exact ⟨0, fun h => absurd h hs⟩
  choose k hk using hk
  -- inverse bound
  have hinv : ∀ v : Vec n, ∀ t ∈ Icc (0:ℝ) 1, ‖v‖ ≤ MQ * ‖TL n (Ψ t) v‖ := by
    intro v t ht
    have : v = TL n (Φ t) (TL n (Ψ t) v) := by
      rw [← ContinuousLinearMap.mul_apply, ← TL_mul, hΦΨ, TL_one]; rfl
    calc ‖v‖ = ‖TL n (Φ t) (TL n (Ψ t) v)‖ := by rw [← this]
      _ ≤ ‖TL n (Φ t)‖ * ‖TL n (Ψ t) v‖ := (TL n (Φ t)).le_opNorm _
      _ ≤ MQ * ‖TL n (Ψ t) v‖ := by gcongr; exact hMQ t ht
  -- `L¹` differences
  have hEc : ContinuousOn (fun σ => Real.sqrt (Ip (pS χ) (pS χ) σ)) (Ioi 0) := fun σ hσ =>
    ((Ip_hasDerivAt hχ.dS hχ.dS hσ).continuousAt.sqrt).continuousWithinAt
  set D : ℝ → ℝ := fun s => Real.sqrt P * (Real.exp (-(b / 2 * s)) / (b / 2))
  have hdiff : ∀ s ≥ s4, ∀ s' ≥ s, ∫ t in (0:ℝ)..1, ‖χ (s', t) - χ (s, t)‖ ≤ D s := by
    intro s hs s' hs'
    have hs0 : 0 < s := lt_of_lt_of_le hs4 hs
    refine (diff_bound hχ hs0 hs').trans ?_
    have hi : IntervalIntegrable (fun σ => Real.sqrt (Ip (pS χ) (pS χ) σ)) volume s s' :=
      (hEc.mono fun x hx => by
        rw [uIcc_of_le hs'] at hx; exact lt_of_lt_of_le hs0 hx.1).intervalIntegrable
    have h1 := intervalIntegral.integral_mono_on hs' hi
      (((Real.continuous_exp.comp ((continuous_const.mul continuous_id).neg)).intervalIntegrable
        s s').const_mul (Real.sqrt P))
      (fun σ hσ => by
        have := hE σ (hs.trans hσ.1)
        calc Real.sqrt (Ip (pS χ) (pS χ) σ) ≤ Real.sqrt (P * Real.exp (-(b * σ))) :=
              Real.sqrt_le_sqrt this
          _ = Real.sqrt P * Real.exp (-(b / 2 * σ)) := by
              rw [Real.sqrt_mul hP, exp_half_sq])
    rw [intervalIntegral.integral_const_mul] at h1
    refine h1.trans ?_
    exact mul_le_mul_of_nonneg_left (int_exp_le (by positivity) hs') (Real.sqrt_nonneg _)
  -- `k` differences
  set B0 := MQ * (2 * (Cg * Q) + Real.sqrt P / (b / 2))
  have hB0 : 0 ≤ B0 := by positivity
  have hkd : ∀ s ≥ s4, ∀ s' ≥ s, ‖k s - k s'‖ ≤ B0 * Real.exp (-(b / 2 * s)) := by
    intro s hs s' hs'
    have hs'4 : s4 ≤ s' := hs.trans hs'
    have hs0 : 0 < s := lt_of_lt_of_le hs4 hs
    have hpt : ∀ t ∈ Icc (0:ℝ) 1, ‖k s - k s'‖ ≤
        MQ * (δ s + δ s' + ‖χ (s', t) - χ (s, t)‖) := by
      intro t ht
      refine (hinv _ t ht).trans (mul_le_mul_of_nonneg_left ?_ hMQ0)
      have e : TL n (Ψ t) (k s - k s') = -(χ (s, t) - TL n (Ψ t) (k s)) +
          (χ (s', t) - TL n (Ψ t) (k s')) + -(χ (s', t) - χ (s, t)) := by
        rw [map_sub]; abel
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [norm_neg]
      refine add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) le_rfl
      · rw [norm_neg]; exact ((hk s hs).2 t)
      · exact (hk s' hs'4).2 t
    have hc : Continuous fun t => ‖χ (s', t) - χ (s, t)‖ :=
      ((cont_slice hχ.cont (lt_of_lt_of_le hs0 hs')).sub (cont_slice hχ.cont hs0)).norm
    have hint := intervalIntegral.integral_mono_on zero_le_one
      (intervalIntegrable_const (μ := volume) (c := ‖k s - k s'‖))
      ((continuous_const.add hc).const_mul MQ |>.intervalIntegrable 0 1) hpt
    rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul] at hint
    simp only [Pi.add_apply] at hint
    rw [intervalIntegral.integral_add intervalIntegrable_const (hc.intervalIntegrable _ _),
      intervalIntegral.integral_const] at hint
    simp only [sub_zero, one_smul, smul_eq_mul, one_mul] at hint
    have hδ : δ s' ≤ δ s := by
      simp only [δ]; gcongr
    have hD := hdiff s hs s' hs'
    have hδ2 : δ s ≤ Cg * Q * Real.exp (-(b / 2 * s)) := by
      simp only [δ]; gcongr; nlinarith
    calc ‖k s - k s'‖ ≤ MQ * (δ s + δ s' + ∫ t in (0:ℝ)..1, ‖χ (s', t) - χ (s, t)‖) := hint
      _ ≤ MQ * (2 * (Cg * Q * Real.exp (-(b / 2 * s))) + D s) := by gcongr; linarith
      _ = B0 * Real.exp (-(b / 2 * s)) := by simp only [B0, D]; ring
  have hexp0 : Tendsto (fun s => B0 * Real.exp (-(b / 2 * s))) atTop (𝓝 0) := by
    have : Tendsto (fun s => -(b / 2 * s)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop (by positivity))
    simpa using (Real.tendsto_exp_atBot.comp this).const_mul B0
  have hcauchy : CauchySeq k := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((hexp0.eventually (gt_mem_nhds hε)).and
      (eventually_ge_atTop s4))
    refine ⟨N, fun m hm => ?_⟩
    rw [dist_comm, dist_eq_norm]
    exact lt_of_le_of_lt (hkd N (hN N le_rfl).2 m hm) (hN N le_rfl).1
  obtain ⟨kinf, hlim⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hrate : ∀ s ≥ s4, ‖k s - kinf‖ ≤ B0 * Real.exp (-(b / 2 * s)) := by
    intro s hs
    have := (tendsto_const_nhds (x := k s)).sub hlim
    exact le_of_tendsto this.norm (eventually_atTop.2 ⟨s, fun s' hs' => hkd s hs s' hs'⟩)
  have hfix : TL n (Ψ 1) kinf = kinf := by
    have h1 : Tendsto (fun s => TL n (Ψ 1) (k s)) atTop (𝓝 (TL n (Ψ 1) kinf)) :=
      ((TL n (Ψ 1)).continuous.tendsto _).comp hlim
    have h2 : Tendsto (fun s => TL n (Ψ 1) (k s)) atTop (𝓝 kinf) :=
      hlim.congr' (eventually_atTop.2 ⟨s4, fun s hs => ((hk s hs).1).symm⟩)
    exact tendsto_nhds_unique h1 h2
  set Cc := Cg * Q + MP * B0
  have hfinal : ∀ s ≥ s4, ∀ t, ‖χ (s, t) - TL n (Ψ t) kinf‖ ≤ Cc * Real.exp (-(b / 2 * s)) := by
    intro s hs t
    have hper : Function.Periodic (fun t => χ (s, t) - TL n (Ψ t) kinf) 1 := fun t => by
      simp only [hpχ s t, hfl t, TL_mul, ContinuousLinearMap.mul_apply, hfix]
    obtain ⟨t', ht', htt⟩ := hper.exists_mem_Ico₀ zero_lt_one t
    rw [htt]
    have ht'' : t' ∈ Icc (0:ℝ) 1 := Ico_subset_Icc_self ht'
    have e : χ (s, t') - TL n (Ψ t') kinf = (χ (s, t') - TL n (Ψ t') (k s)) +
        TL n (Ψ t') (k s - kinf) := by rw [map_sub]; abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have h1 := (hk s hs).2 t'
    have h2 : ‖TL n (Ψ t') (k s - kinf)‖ ≤ MP * (B0 * Real.exp (-(b / 2 * s))) :=
      ((TL n (Ψ t')).le_opNorm _).trans (mul_le_mul (hMP t' ht'') (hrate s hs)
        (norm_nonneg _) hMP0)
    have h3 : δ s ≤ Cg * Q * Real.exp (-(b / 2 * s)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith [lt_of_lt_of_le hs4 hs]))
        (mul_nonneg hCg0 hQ)
    calc _ ≤ δ s + MP * (B0 * Real.exp (-(b / 2 * s))) := add_le_add h1 h2
      _ ≤ Cg * Q * Real.exp (-(b / 2 * s)) + MP * (B0 * Real.exp (-(b / 2 * s))) := by linarith
      _ = Cc * Real.exp (-(b / 2 * s)) := by simp only [Cc]; ring
  refine ⟨Ψ, hfund, hfl, kinf, ?_, hfix, Cc, hfinal⟩
  -- nonvanishing
  intro h0
  have hCc : 0 ≤ Cc := by positivity
  have hexp1 : Tendsto (fun s => Cc ^ 2 * Real.exp (-(b / 2 * s)) ^ 2) atTop (𝓝 0) := by
    have : Tendsto (fun s => -(b / 2 * s)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop (by positivity))
    have h := (Real.tendsto_exp_atBot.comp this).pow 2 |>.const_mul (Cc ^ 2)
    simpa using h
  obtain ⟨s, hs⟩ := eventually_atTop.1 ((hexp1.eventually (gt_mem_nhds hHlo)).and
    (eventually_ge_atTop s4))
  have hs1 := hs s le_rfl
  have hb2 : ∀ t, ⟪χ (s, t), χ (s, t)⟫ ≤ Cc ^ 2 * Real.exp (-(b / 2 * s)) ^ 2 := by
    intro t
    have := hfinal s hs1.2 t
    rw [h0, map_zero, sub_zero] at this
    rw [real_inner_self_eq_norm_sq, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  have hI : Ip χ χ s ≤ Cc ^ 2 * Real.exp (-(b / 2 * s)) ^ 2 := by
    have := intervalIntegral.integral_mono_on zero_le_one
      ((cont_inner hχ.cont hχ.cont (lt_of_lt_of_le hs4 hs1.2)).intervalIntegrable _ _)
      (intervalIntegrable_const (μ := volume)) fun t _ => hb2 t
    simpa [Ip] using this
  have := hH s hs1.2
  linarith [hs1.1]

end HDecay

end AF_r

section AF_s

/-! One-dimensional Caccioppoli and Sobolev inequalities. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

lemma abs_int_le_unit {h : ℝ → ℝ} (hc : Continuous h) (h0 : ∀ x, 0 ≤ h x) {τ t : ℝ}
    (hτ : τ ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1) :
    |∫ x in τ..t, h x| ≤ ∫ x in (0:ℝ)..1, h x := by
  have hi : IntervalIntegrable h volume 0 1 := hc.intervalIntegrable _ _
  have hae : 0 ≤ᵐ[volume.restrict (Ioc 0 1)] h := Filter.Eventually.of_forall h0
  rcases le_total τ t with hle | hle
  · rw [abs_of_nonneg (intervalIntegral.integral_nonneg hle fun x _ => h0 x)]
    exact intervalIntegral.integral_mono_interval hτ.1 hle ht.2
      (Filter.Eventually.of_forall h0) hi
  · rw [intervalIntegral.integral_symm, abs_neg,
      abs_of_nonneg (intervalIntegral.integral_nonneg hle fun x _ => h0 x)]
    exact intervalIntegral.integral_mono_interval ht.1 hle hτ.2
      (Filter.Eventually.of_forall h0) hi

/-- `sup |v| ≤ ∫ |v| + ∫ |v'|` for `1`-periodic `C¹` loops -/
lemma sup_le_int {v v' : ℝ → Vec n} (hv : ∀ t, HasDerivAt v (v' t) t) (hv' : Continuous v')
    (hper : Function.Periodic v 1) (t : ℝ) :
    ‖v t‖ ≤ (∫ τ in (0:ℝ)..1, ‖v τ‖) + ∫ τ in (0:ℝ)..1, ‖v' τ‖ := by
  have hvc : Continuous v := continuous_iff_continuousAt.2 fun t => (hv t).continuousAt
  obtain ⟨t', ht', e⟩ := hper.exists_mem_Ico₀ one_pos t
  rw [e]
  have ht'' : t' ∈ Icc (0:ℝ) 1 := Ico_subset_Icc_self ht'
  set C := ∫ τ in (0:ℝ)..1, ‖v' τ‖
  have hb : ∀ τ ∈ Icc (0:ℝ) 1, ‖v t'‖ ≤ ‖v τ‖ + C := by
    intro τ hτ
    have e1 : v t' - v τ = ∫ x in τ..t', v' x :=
      (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hv x)
        (hv'.intervalIntegrable _ _)).symm
    have e2 : ‖∫ x in τ..t', v' x‖ ≤ C :=
      (intervalIntegral.norm_integral_le_abs_integral_norm).trans
        (abs_int_le_unit hv'.norm (fun _ => norm_nonneg _) hτ ht'')
    have : ‖v t'‖ ≤ ‖v τ‖ + ‖v t' - v τ‖ := by
      have := norm_add_le (v τ) (v t' - v τ); simpa using this
    rw [e1] at this; linarith
  have := intervalIntegral.integral_mono_on zero_le_one
    (intervalIntegrable_const (μ := volume) (c := ‖v t'‖))
    ((hvc.norm.add continuous_const).intervalIntegrable 0 1) hb
  simp only [Pi.add_apply] at this
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add (hvc.norm.intervalIntegrable _ _)
    intervalIntegrable_const, intervalIntegral.integral_const] at this
  simpa using this

end HDecay

end AF_s

section AF_t

/-! The third `s`-derivative of the coefficient decays exponentially. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

end HDecay

end AF_t

section AF_u

/-! Second energy level: residual identities and an energy inequality with a scalar weight. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

end HDecay

end AF_u

section AF_v

/-! `‖∂ₛ(∂ₛζ - μζ)‖²_{L²}(s) ≤ C ‖ζ‖²_{L²}(s)`. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

end HDecay

end AF_v

section AF_w

/-! `‖∂ₛ(∂ₛζ - μζ)‖²_{L²}(s) ≤ C ‖ζ‖²_{L²}(s)`. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

end HDecay

end AF_w

section AF_x

/-! Smoothness of the fundamental solution; the limit `Ψ(·) k` is an eigenfunction. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

theorem fund_smooth (S' : ℝ → Mat n) (hS' : ∀ i j, ContDiff ℝ ∞ (fun t => S' t i j))
    (Ψ : ℝ → Mat n) (hΨ : IsFundamentalSolution S' Ψ) :
    ContDiff ℝ ∞ (fun t => TL n (Ψ t)) := by
  set P : ℝ → Op n := fun t => TL n (Ψ t)
  set L : ℝ → Op n := fun t => Jop n * TL n (S' t)
  have hL : ContDiff ℝ ∞ L := contDiff_const.mul (contDiff_TL1 S' hS')
  have hP : ∀ t, HasDerivAt P (L t * P t) t := by
    intro t
    let _ : NormedAddCommGroup (Mat n) := Matrix.normedAddCommGroup
    let _ : NormedSpace ℝ (Mat n) := Matrix.normedSpace
    have := (TL n).hasFDerivAt.comp_hasDerivAt t (hΨ.2 t)
    refine this.congr_deriv ?_
    show TL n (J₀ n * S' t * Ψ t) = Jop n * TL n (S' t) * TL n (Ψ t)
    rw [TL_mul, TL_mul]
  have hPd : deriv P = fun t => L t * P t := funext fun t => (hP t).deriv
  have hPdiff : Differentiable ℝ P := fun t => (hP t).differentiableAt
  have key : ∀ m : ℕ, ContDiff ℝ m P := by
    intro m
    induction m with
    | zero => exact contDiff_zero.2 hPdiff.continuous
    | succ m ih =>
      rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 by norm_cast,
        contDiff_succ_iff_deriv]
      refine ⟨hPdiff, by simp, ?_⟩
      rw [hPd]
      exact (hL.of_le (by exact_mod_cast le_top)).mul ih
  exact contDiff_infty.2 fun m => key m

theorem loopEigen_of_fund (Sinf : ℝ → Mat n) (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (μ : ℝ) (Ψ : ℝ → Mat n) (hΨ : IsFundamentalSolution (fun t => Sinf t + μ • (1 : Mat n)) Ψ)
    (hfl : ∀ t, Ψ (t + 1) = Ψ t * Ψ 1) (k : Vec n) (hk : k ≠ 0) (hfix : TL n (Ψ 1) k = k) :
    FiniteEnergyPlane.IsLoopEigen Sinf μ (fun t => TL n (Ψ t) k) := by
  have hS' : ∀ i j, ContDiff ℝ ∞ (fun t => (Sinf t + μ • (1 : Mat n)) i j) := fun i j => by
    simp only [Matrix.add_apply, Matrix.smul_apply]
    exact (hSinf' i j).add contDiff_const
  have hsm := fund_smooth _ hS' Ψ hΨ
  have hd : ∀ t, HasDerivAt (fun t => TL n (Ψ t) k)
      (TL n (J₀ n * (Sinf t + μ • (1 : Mat n)) * Ψ t) k) t := by
    intro t
    let _ : NormedAddCommGroup (Mat n) := Matrix.normedAddCommGroup
    let _ : NormedSpace ℝ (Mat n) := Matrix.normedSpace
    exact ((TL n).hasFDerivAt.comp_hasDerivAt t (hΨ.2 t)).clm_apply (hasDerivAt_const t k)
      |>.congr_deriv (by simp only [Function.comp, map_zero, add_zero]; rfl)
  refine ⟨hsm.clm_apply contDiff_const, fun t => ?_, ⟨0, ?_⟩, fun t => ?_⟩
  · simp only [hfl t, TL_mul, ContinuousLinearMap.mul_apply, hfix]
  · simp only [hΨ.1, TL_one, ContinuousLinearMap.one_apply]; exact hk
  · rw [(hd t).deriv]
    show -(Jop n (TL n (J₀ n * (Sinf t + μ • (1 : Mat n)) * Ψ t) k)) -
      TL n (Sinf t) (TL n (Ψ t) k) = μ • TL n (Ψ t) k
    rw [TL_mul3]
    erw [Jop_Jop]
    rw [neg_neg, TL_shift]
    abel

end HDecay

end AF_x

section AF_y

/-! Stage E: exponential `C⁰` convergence of `e^{-μs} ζ` to an eigenfunction, with `C¹` bounds. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

lemma norm_Jop (v : Vec n) : ‖Jop n v‖ = ‖v‖ := by
  have h := inner_Jop_Jop v v
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

lemma periodic_op_bound (M : ℝ → Mat n) (hc : Continuous fun t => TL n (M t))
    (hp : Function.Periodic M 1) : ∃ B, 0 ≤ B ∧ ∀ t, ‖TL n (M t)‖ ≤ B := by
  obtain ⟨B, hB0, hB⟩ := TL_cont_bound M hc
  refine ⟨B, hB0, fun t => ?_⟩
  obtain ⟨t', ht', e⟩ := (show Function.Periodic (fun t => TL n (M t)) 1 from
    fun t => by simp only [hp t]).exists_mem_Ico₀ one_pos t
  rw [e]; exact hB t' (Ico_subset_Icc_self ht')

/-- sup bound for `ηm` on a slice -/
lemma sup_ηm {A : ℝ × ℝ → Op n} {ζ : ℝ × ℝ → Vec n} (hA : Sm A) (hζ : Sm ζ) (hpζ : TPer ζ)
    (hres0 : ∀ x ∈ Ω, res A ζ x = 0) (μ : ℝ) {s MA k : ℝ} (hs : 0 < s)
    (hMA : ∀ t, ‖A (s, t)‖ ≤ MA) (hk : ∀ t, ‖pS A (s, t)‖ ≤ k) (t : ℝ) :
    ‖ηm ζ μ (s, t)‖ ≤ Real.sqrt (Ip (ηm ζ μ) (ηm ζ μ) s) +
      (Real.sqrt (Ip (pS (ηm ζ μ)) (pS (ηm ζ μ)) s) + MA * Real.sqrt (Ip (ηm ζ μ) (ηm ζ μ) s) +
        k * Real.sqrt (Fz ζ s)) := by
  set η := ηm ζ μ
  have hη : Sm η := hζ.ηm μ
  have hpη : TPer η := hpζ.ηm μ
  have hsup := sup_le_int (v := fun τ => η (s, τ)) (v' := fun τ => pT η (s, τ))
    (fun τ => hη.hasDerivAt_t hs) (cont_slice hη.dT.cont hs) (hpη.periodic s) t
  refine hsup.trans (add_le_add (int_norm_le_sqrt' hη hs) ?_)
  -- pointwise bound for `pT η`
  have hpt : ∀ τ, ‖pT η (s, τ)‖ ≤ ‖pS η (s, τ)‖ + MA * ‖η (s, τ)‖ + k * ‖ζ (s, τ)‖ := by
    intro τ
    have hr := res_ηm hA hζ hres0 μ (s, τ) (mem_Ω hs)
    simp only [res] at hr
    have e : pT η (s, τ) = Jop n (pS η (s, τ) + A (s, τ) (η (s, τ)) + pS A (s, τ) (ζ (s, τ))) := by
      have : Jop n (pT η (s, τ)) = -(pS η (s, τ) + A (s, τ) (η (s, τ)) +
          pS A (s, τ) (ζ (s, τ))) := by
        rw [eq_neg_iff_add_eq_zero]
        have := congrArg (fun v => v + pS A (s, τ) (ζ (s, τ))) hr
        simp only [neg_add_cancel] at this
        rw [← this]; abel
      have h2 := congrArg (Jop n) this
      rw [Jop_Jop, map_neg] at h2
      rw [← neg_neg (pT η (s, τ)), h2, neg_neg]
    rw [e, norm_Jop]
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add le_rfl ?_)) ?_)
    · exact ((A (s, τ)).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hMA τ) (norm_nonneg _))
    · exact ((pS A (s, τ)).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hk τ) (norm_nonneg _))
  have hc1 := (cont_slice hη.dS.cont hs).norm
  have hc2 := (cont_slice hη.cont hs).norm
  have hc3 := (cont_slice hζ.cont hs).norm
  have hk0 : 0 ≤ k := (norm_nonneg _).trans (hk 0)
  have hMA0 : 0 ≤ MA := (norm_nonneg _).trans (hMA 0)
  have hint := intervalIntegral.integral_mono_on (f := fun τ => ‖pT η (s, τ)‖)
    (g := fun τ => ‖pS η (s, τ)‖ + MA * ‖η (s, τ)‖ + k * ‖ζ (s, τ)‖) zero_le_one
    ((cont_slice hη.dT.cont hs).norm.intervalIntegrable (μ := volume) 0 1)
    (((hc1.add (continuous_const.mul hc2)).add (continuous_const.mul hc3)).intervalIntegrable (μ := volume) 0 1)
    (fun τ _ => hpt τ)
  rw [intervalIntegral.integral_add (f := fun τ => ‖pS η (s, τ)‖ + MA * ‖η (s, τ)‖)
    (g := fun τ => k * ‖ζ (s, τ)‖)
    ((hc1.add (continuous_const.mul hc2)).intervalIntegrable (μ := volume) 0 1)
    ((continuous_const.mul hc3).intervalIntegrable (μ := volume) 0 1),
    intervalIntegral.integral_add (f := fun τ => ‖pS η (s, τ)‖) (g := fun τ => MA * ‖η (s, τ)‖)
    (hc1.intervalIntegrable (μ := volume) 0 1)
    ((continuous_const.mul hc2).intervalIntegrable (μ := volume) 0 1),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hint
  refine hint.trans ?_
  have i1 := int_norm_le_sqrt' hη.dS hs
  have i2 := int_norm_le_sqrt' hη hs
  have i3 := int_norm_le_sqrt' hζ hs
  have : Fz ζ s = Ip ζ ζ s := rfl
  rw [this]
  gcongr

end HDecay

end AF_y

section SP2

/-! Stage E assembled. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}


lemma Ip_self_eq (u : ℝ × ℝ → Vec n) (s : ℝ) : Ip u u s = ∫ t in (0:ℝ)..1, ‖u (s, t)‖ ^ 2 := by
  simp only [Ip, real_inner_self_eq_norm_sq]

theorem bounds_local (S : ℝ × ℝ → Mat n) (hS : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × ℝ => S p i j))
    (hSper : ∀ s t : ℝ, S (s, t + 1) = S (s, t))
    (Sinf : ℝ → Mat n) (hSinf : IsSymLoop Sinf) (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (d : ℝ) (hd : 0 < d) (hSas : FiniteEnergyPlane.IsExpAsymptoticTo S Sinf d)
    (ζ : ℝ × ℝ → Vec n) (hζ : FiniteEnergyPlane.IsHalfCylSolution S ζ)
    (hne : ∃ p : ℝ × ℝ, 0 < p.1 ∧ ζ p ≠ 0)
    (C δ₀ : ℝ) (hgrowth : ∀ s > 0, ∀ t : ℝ, ‖ζ (s, t)‖ ≤ C * Real.exp (δ₀ * s)) :
    ∃ μ, μ ≤ δ₀ ∧ ∃ a > 0, ∃ Cr s1 K : ℝ, 0 < s1 ∧ 0 < K ∧
      (∀ s ≥ s1, ∀ t, ‖TL n (S (s, t)) - TL n (Sinf t)‖ ≤ K * Real.exp (-(d * s)) ∧
        ‖pS (fun p => TL n (S p)) (s, t)‖ ≤ K * Real.exp (-(d * s)) ∧
        ‖pS (pS (fun p => TL n (S p))) (s, t)‖ ≤ K * Real.exp (-(d * s))) ∧
      (∀ s ≥ s1, 0 < Fz ζ s) ∧ (∀ s ≥ s1, HasDerivAt (Fz ζ) (2 * αz ζ s * Fz ζ s) s) ∧
      (∀ s ≥ s1, |αz ζ s - μ| ≤ Cr * Real.exp (-(a * s)) ∧
        ∀ T ≥ s, ∫ x in s..T, qz ζ x ≤ Cr * Real.exp (-(a * s))) ∧
      (∀ s ≥ s1, Ip (ηm ζ μ) (ηm ζ μ) s ≤ Cr * Real.exp (-(a * s)) * Fz ζ s) ∧
      (∀ s ≥ s1, Ip (pS (ηm ζ μ)) (pS (ηm ζ μ)) s ≤ Cr * Fz ζ s) := by
  obtain ⟨μ, hμ, s₀, hs₀, a, ha, Cr, hb⟩ := FiniteEnergyPlane.halfCyl_alpha_eta_bounds S hS hSper
    Sinf hSinf hSinf' d hd hSas ζ hζ hne C δ₀ hgrowth
  obtain ⟨K, hK, s1, hs1, hco⟩ := coeff_exp S hS Sinf hSinf' d hSas
  have hb' : ∀ s ≥ max s₀ s1, 0 < Fz ζ s ∧ |αz ζ s - μ| ≤ Cr * Real.exp (-(a * s)) ∧
      (∀ T ≥ s, ∫ x in s..T, qz ζ x ≤ Cr * Real.exp (-(a * s))) ∧
      Ip (ηm ζ μ) (ηm ζ μ) s ≤ Cr * Real.exp (-(a * s)) * Fz ζ s ∧
      Ip (pS (ηm ζ μ)) (pS (ηm ζ μ)) s ≤ Cr * Fz ζ s := fun s hs => by
    simp only [qz, αz, Dz, Gz, Fz, Ip_self_eq]
    exact hb s ((le_max_left _ _).trans hs)
  refine ⟨μ, hμ, a, ha, Cr, max s₀ s1, K, lt_max_of_lt_left hs₀, hK,
    fun s hs => hco s ((le_max_right _ _).trans hs), fun s hs => (hb' s hs).1, fun s hs => ?_,
    fun s hs => ⟨(hb' s hs).2.1, (hb' s hs).2.2.1⟩, fun s hs => (hb' s hs).2.2.2.1,
    fun s hs => (hb' s hs).2.2.2.2⟩
  exact Fz_hasDerivAt' hζ.1 (hs₀.trans_le ((le_max_left _ _).trans hs)) (hb' s hs).1

set_option maxHeartbeats 1000000 in
theorem stageE2 (S : ℝ × ℝ → Mat n) (hS : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × ℝ => S p i j))
    (hSper : ∀ s t : ℝ, S (s, t + 1) = S (s, t))
    (Sinf : ℝ → Mat n) (hSinf : IsSymLoop Sinf) (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (d : ℝ) (hd : 0 < d) (hSas : FiniteEnergyPlane.IsExpAsymptoticTo S Sinf d)
    (ζ : ℝ × ℝ → Vec n) (hζ : FiniteEnergyPlane.IsHalfCylSolution S ζ)
    (hne : ∃ p : ℝ × ℝ, 0 < p.1 ∧ ζ p ≠ 0)
    (C δ₀ : ℝ) (hgrowth : ∀ s > 0, ∀ t : ℝ, ‖ζ (s, t)‖ ≤ C * Real.exp (δ₀ * s)) :
    ∃ μ, μ ≤ δ₀ ∧ ∃ e : ℝ → Vec n, FiniteEnergyPlane.IsLoopEigen Sinf μ e ∧
      ∃ s6 > 0, ∃ M b Cc : ℝ, 0 < b ∧ ∀ s ≥ s6, ∀ t,
        ‖χr ζ μ (s, t) - e t‖ ≤ Cc * Real.exp (-(b * s)) ∧ ‖χr ζ μ (s, t)‖ ≤ M ∧
        ‖pS (χr ζ μ) (s, t)‖ ≤ M ∧ ‖pT (χr ζ μ) (s, t)‖ ≤ M := by
  obtain ⟨μ, hμ, a, ha, Cr, s1, K, hs10, hK, hco, hFF, hFd, hrate, hE1, hE2⟩ :=
    bounds_local S hS hSper Sinf hSinf hSinf' d hd hSas ζ hζ hne C δ₀ hgrowth
  set s3 := s1
  have hs3 : s1 ≤ s3 := le_rfl
  set A : ℝ × ℝ → Op n := fun p => TL n (S p)
  have hA : Sm A := (contDiff_TL S hS).contDiffOn
  have hpA : TPer A := fun s t => by simp only [A, hSper s t]
  have hζs : Sm ζ := hζ.1
  have hpζ : TPer ζ := hζ.2.1
  have hres0 : ∀ x ∈ Ω, res A ζ x = 0 := by
    rintro ⟨a, b⟩ hx
    exact hζ.2.2 a hx.1 b
  have hCr : 0 ≤ Cr := by
    have := (hrate s3 le_rfl).1
    have h0 := abs_nonneg (αz ζ s3 - μ)
    by_contra hc; push Not at hc
    have : Cr * Real.exp (-(a * s3)) < 0 := mul_neg_of_neg_of_pos hc (Real.exp_pos _)
    linarith
  obtain ⟨Hlo, hHlo, Hhi, hHb⟩ := H_bounds (Fz ζ) (αz ζ) μ a Cr s3 ha hCr
    (fun s hs => hFd s (hs3.trans hs)) (fun s hs => hFF s (hs3.trans hs))
    (fun s hs => (hrate s hs).1)
  obtain ⟨a', ha', C', s4, hC'⟩ : ∃ a' > 0, ∃ C' s4 : ℝ, ∀ s ≥ s4,
      Ip (ηm ζ μ) (ηm ζ μ) s ≤ C' * Real.exp (-(a' * s)) * Fz ζ s := ⟨a, ha, Cr, s1, hE1⟩
  have hC'0 : 0 ≤ C' := by
    set s' := max s4 s3
    have h1 := hC' s' (le_max_left _ _)
    have h2 := Ip_self_nonneg (ηm ζ μ) s'
    have h3 := hFF s' (hs3.trans (le_max_right _ _))
    by_contra hc; push Not at hc
    have : C' * Real.exp (-(a' * s')) * Fz ζ s' < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hc (Real.exp_pos _)) h3
    linarith only [h1, h2, this]
  obtain ⟨C2, s5, hC2⟩ : ∃ C2 s5 : ℝ, ∀ s ≥ s5,
      Ip (pS (ηm ζ μ)) (pS (ηm ζ μ)) s ≤ C2 * Fz ζ s := ⟨Cr, s1, hE2⟩
  have hHhi0 : 0 ≤ Hhi := (hHlo.le.trans (hHb s3 le_rfl).1).trans (hHb s3 le_rfl).2
  have hC20 : 0 ≤ C2 := by
    set s' := max s5 s3
    have h1 := hC2 s' (le_max_left _ _)
    have h2 := Ip_self_nonneg (pS (ηm ζ μ)) s'
    have h3 := hFF s' (hs3.trans (le_max_right _ _))
    by_contra hc; push Not at hc
    have : C2 * Fz ζ s' < 0 := mul_neg_of_neg_of_pos hc h3
    linarith only [h1, h2, this]
  set s6 := max (max s3 s4) (max s5 1)
  have h6a : s3 ≤ s6 := (le_max_left _ _).trans (le_max_left _ _)
  have h6b : s4 ≤ s6 := (le_max_right _ _).trans (le_max_left _ _)
  have h6c : s5 ≤ s6 := (le_max_left _ _).trans (le_max_right _ _)
  have h6d : 1 ≤ s6 := (le_max_right _ _).trans (le_max_right _ _)
  have hs6 : 0 < s6 := by linarith only [h6d]
  set χ := χr ζ μ
  have hχ : Sm χ := hζs.χr μ
  have hpχ : TPer χ := hpζ.χr μ
  set b := min (a' / 2) d
  have hb : 0 < b := lt_min (half_pos ha') hd
  set P := C' * Hhi
  have hP : 0 ≤ P := mul_nonneg hC'0 hHhi0
  have hH : ∀ s ≥ s6, Ip χ χ s = Real.exp (-(2 * μ * s)) * Fz ζ s := fun s _ => Ip_χr ζ μ s
  have hE : ∀ s ≥ s6, Ip (pS χ) (pS χ) s ≤ P * Real.exp (-(a' * s)) := by
    intro s hs
    rw [Ip_pSχr hζs μ (by linarith only [hs, h6d])]
    have h1 := hC' s (h6b.trans hs)
    have h2 := (hHb s (h6a.trans hs)).2
    have h0 := Real.exp_pos (-(2 * μ * s))
    calc Real.exp (-(2 * μ * s)) * Ip (ηm ζ μ) (ηm ζ μ) s
        ≤ Real.exp (-(2 * μ * s)) * (C' * Real.exp (-(a' * s)) * Fz ζ s) :=
          mul_le_mul_of_nonneg_left h1 h0.le
      _ = C' * Real.exp (-(a' * s)) * (Real.exp (-(2 * μ * s)) * Fz ζ s) := by ring
      _ ≤ C' * Real.exp (-(a' * s)) * Hhi :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hC'0 (Real.exp_pos _).le)
      _ = P * Real.exp (-(a' * s)) := by simp only [P]; ring
  have hE' : ∀ s ≥ s6, Ip (pS χ) (pS χ) s ≤ P * Real.exp (-(b * s)) := by
    intro s hs
    refine (hE s hs).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hP)
    have : b ≤ a' := (min_le_left _ _).trans (by linarith only [ha'])
    exact neg_le_neg (mul_le_mul_of_nonneg_right this (by linarith only [hs, h6d]))
  set Q := Real.sqrt P + K * Real.sqrt Hhi
  have hG : ∀ s ≥ s6, ∫ t in (0:ℝ)..1,
      ‖-(Jop n (pT χ (s, t))) - TL n (Sinf t) (χ (s, t)) - μ • χ (s, t)‖ ≤
        Q * Real.exp (-(b * s)) := by
    intro s hs
    have hs0 : 0 < s := by linarith only [hs, h6d]
    have hs1 : s1 ≤ s := hs3.trans (h6a.trans hs)
    have hpt : ∀ t, ‖-(Jop n (pT χ (s, t))) - TL n (Sinf t) (χ (s, t)) - μ • χ (s, t)‖ ≤
        ‖pS χ (s, t)‖ + K * Real.exp (-(d * s)) * ‖χ (s, t)‖ := by
      intro t
      rw [χr_eq hζs hres0 Sinf μ hs0 t]
      refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
      exact ((A (s, t) - TL n (Sinf t)).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (hco s hs1 t).1 (norm_nonneg _))
    have hc1 := (cont_slice hχ.dS.cont hs0).norm
    have hc2 := (cont_slice hχ.cont hs0).norm
    have hint := intervalIntegral.integral_mono_on
      (g := fun t => ‖pS χ (s, t)‖ + K * Real.exp (-(d * s)) * ‖χ (s, t)‖) zero_le_one
      ((((Jop n).continuous.comp (cont_slice hχ.dT.cont hs0)).neg.sub
        (((TL n).continuous.comp hSinf.1).clm_apply (cont_slice hχ.cont hs0))).sub
        ((cont_slice hχ.cont hs0).const_smul μ) |>.norm.intervalIntegrable (μ := volume) 0 1)
      ((hc1.add (continuous_const.mul hc2)).intervalIntegrable (μ := volume) 0 1)
      (fun t _ => hpt t)
    rw [intervalIntegral.integral_add (f := fun t => ‖pS χ (s, t)‖)
      (g := fun t => K * Real.exp (-(d * s)) * ‖χ (s, t)‖) (hc1.intervalIntegrable _ _)
      ((continuous_const.mul hc2).intervalIntegrable _ _), intervalIntegral.integral_const_mul] at hint
    refine hint.trans ?_
    have i1 := int_norm_le_sqrt' hχ.dS hs0
    have i2 := int_norm_le_sqrt' hχ hs0
    have j1 : Real.sqrt (Ip (pS χ) (pS χ) s) ≤ Real.sqrt P * Real.exp (-(b * s)) := by
      have := Real.sqrt_le_sqrt (hE s hs)
      rw [Real.sqrt_mul hP, exp_half_sq] at this
      refine this.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.sqrt_nonneg _))
      have : b ≤ a' / 2 := min_le_left _ _
      exact neg_le_neg (mul_le_mul_of_nonneg_right this hs0.le)
    have j2 : Real.sqrt (Ip χ χ s) ≤ Real.sqrt Hhi := by
      rw [hH s hs]; exact Real.sqrt_le_sqrt (hHb s (h6a.trans hs)).2
    have j3 : Real.exp (-(d * s)) ≤ Real.exp (-(b * s)) := by
      refine Real.exp_le_exp.2 ?_
      have : b ≤ d := min_le_right _ _
      exact neg_le_neg (mul_le_mul_of_nonneg_right this hs0.le)
    have hKe : 0 ≤ K * Real.exp (-(d * s)) := mul_nonneg hK.le (Real.exp_pos _).le
    calc (∫ t in (0:ℝ)..1, ‖pS χ (s, t)‖) + K * Real.exp (-(d * s)) * ∫ t in (0:ℝ)..1, ‖χ (s, t)‖
        ≤ Real.sqrt P * Real.exp (-(b * s)) + K * Real.exp (-(d * s)) * Real.sqrt Hhi :=
          add_le_add (i1.trans j1) (mul_le_mul_of_nonneg_left (i2.trans j2) hKe)
      _ ≤ Real.sqrt P * Real.exp (-(b * s)) + K * Real.exp (-(b * s)) * Real.sqrt Hhi :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left j3 hK.le)
            (Real.sqrt_nonneg _))
      _ = Q * Real.exp (-(b * s)) := by simp only [Q]; ring
  have hHlo' : ∀ s ≥ s6, Hlo ≤ Ip χ χ s := fun s hs => by
    rw [hH s hs]; exact (hHb s (h6a.trans hs)).1
  obtain ⟨Ψ, hfund, hfl, k, hk, hfix, Cc, hconv⟩ :=
    unif_conv Sinf hSinf μ hχ hpχ hs6 hb hP hE' hG hHlo hHlo'
  set e : ℝ → Vec n := fun t => TL n (Ψ t) k
  have heig := loopEigen_of_fund Sinf hSinf' μ Ψ hfund hfl k hk hfix
  -- bounds
  have hΨc : Continuous fun t => TL n (Ψ t) := by
    let _ : NormedAddCommGroup (Mat n) := Matrix.normedAddCommGroup
    let _ : NormedSpace ℝ (Mat n) := Matrix.normedSpace
    exact continuous_iff_continuousAt.2 fun t =>
      ((TL n).hasFDerivAt.comp_hasDerivAt t (hfund.2 t)).continuousAt
  obtain ⟨MP, hMP0, hMP⟩ := TL_cont_bound Ψ hΨc
  have he : ∀ t, ‖e t‖ ≤ MP * ‖k‖ := by
    intro t
    obtain ⟨t', ht', et⟩ := heig.2.1.exists_mem_Ico₀ one_pos t
    show ‖TL n (Ψ t) k‖ ≤ _
    rw [show TL n (Ψ t) k = TL n (Ψ t') k from et]
    exact ((TL n (Ψ t')).le_opNorm k).trans
      (mul_le_mul_of_nonneg_right (hMP t' (Ico_subset_Icc_self ht')) (norm_nonneg _))
  obtain ⟨MS, hMS0, hMS⟩ := periodic_op_bound Sinf ((TL n).continuous.comp hSinf.1) hSinf.2.1
  set MA := MS + K
  have hCc0 : 0 ≤ Cc := by
    have := hconv s6 le_rfl 0
    have := norm_nonneg (χ (s6, 0) - TL n (Ψ 0) k)
    by_contra hc; push Not at hc
    have : Cc * Real.exp (-(b / 2 * s6)) < 0 := mul_neg_of_neg_of_pos hc (Real.exp_pos _)
    linarith
  set M0 := MP * ‖k‖ + Cc
  set M1 := Real.sqrt C' * Real.sqrt Hhi + (Real.sqrt C2 * Real.sqrt Hhi +
    MA * (Real.sqrt C' * Real.sqrt Hhi) + K * Real.sqrt Hhi)
  have hMA0 : 0 ≤ MA := add_nonneg hMS0 hK.le
  have hM0 : 0 ≤ M0 := add_nonneg (mul_nonneg hMP0 (norm_nonneg _)) hCc0
  have hM1 : 0 ≤ M1 :=
    add_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (add_nonneg (add_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
        (mul_nonneg hMA0 (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))))
        (mul_nonneg hK.le (Real.sqrt_nonneg _)))
  refine ⟨μ, hμ, e, heig, s6, hs6, M1 + (|μ| + MA) * M0 + M0, b / 2, Cc, half_pos hb,
    fun s hs t => ?_⟩
  have hs0 : 0 < s := by linarith only [hs, h6d]
  have hs1 : s1 ≤ s := hs3.trans (h6a.trans hs)
  have hexp1 : Real.exp (-(b / 2 * s)) ≤ 1 :=
    Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg (half_pos hb).le hs0.le))
  have hconv' := hconv s hs t
  have hχb : ‖χ (s, t)‖ ≤ M0 := by
    have : χ (s, t) = (χ (s, t) - e t) + e t := by abel
    rw [this]
    refine (norm_add_le _ _).trans ?_
    have h1 := he t
    have h2 : Cc * Real.exp (-(b / 2 * s)) ≤ Cc := mul_le_of_le_one_right hCc0 hexp1
    show _ ≤ MP * ‖k‖ + Cc
    linarith only [hconv', h1, h2]
  have hMA : ∀ t, ‖A (s, t)‖ ≤ MA := fun t => by
    have : A (s, t) = (A (s, t) - TL n (Sinf t)) + TL n (Sinf t) := by abel
    rw [this]
    refine (norm_add_le _ _).trans ?_
    have h1 := (hco s hs1 t).1
    have h2 : K * Real.exp (-(d * s)) ≤ K :=
      mul_le_of_le_one_right hK.le
        (Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hd.le hs0.le)))
    have h3 := hMS t
    show _ ≤ MS + K
    linarith only [h1, h2, h3]
  have hkA : ∀ t, ‖pS A (s, t)‖ ≤ K := fun t => by
    have h1 := (hco s hs1 t).2.1
    have : Real.exp (-(d * s)) ≤ 1 :=
      Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hd.le hs0.le))
    exact h1.trans (mul_le_of_le_one_right hK.le this)
  -- `pS χ`
  have hpSχ : ‖pS χ (s, t)‖ ≤ M1 := by
    rw [pS_χr hζs μ hs0, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hsup := sup_ηm hA hζs hpζ hres0 μ hs0 hMA hkA t
    have hF0 := Ip_self_nonneg ζ s
    have hw : Real.exp (-(μ * s)) = Real.sqrt (Real.exp (-(2 * μ * s))) := by
      rw [← Real.exp_half]; ring_nf
    have hHs : Real.exp (-(2 * μ * s)) * Fz ζ s ≤ Hhi := (hHb s (h6a.trans hs)).2
    have r1 : Real.exp (-(μ * s)) * Real.sqrt (Fz ζ s) ≤ Real.sqrt Hhi := by
      rw [hw, ← Real.sqrt_mul (Real.exp_pos _).le]; exact Real.sqrt_le_sqrt hHs
    have hη1 : Ip (ηm ζ μ) (ηm ζ μ) s ≤ C' * Fz ζ s := by
      have := hC' s (h6b.trans hs)
      have h2 : Real.exp (-(a' * s)) ≤ 1 :=
        Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg ha'.le hs0.le))
      calc _ ≤ C' * Real.exp (-(a' * s)) * Fz ζ s := this
        _ ≤ C' * 1 * Fz ζ s := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hC'0) hF0
        _ = C' * Fz ζ s := by ring
    have hη2 := hC2 s (h6c.trans hs)
    have r2 : Real.sqrt (Ip (ηm ζ μ) (ηm ζ μ) s) ≤ Real.sqrt C' * Real.sqrt (Fz ζ s) := by
      rw [← Real.sqrt_mul hC'0]; exact Real.sqrt_le_sqrt hη1
    have r3 : Real.sqrt (Ip (pS (ηm ζ μ)) (pS (ηm ζ μ)) s) ≤ Real.sqrt C2 * Real.sqrt (Fz ζ s) := by
      rw [← Real.sqrt_mul hC20]; exact Real.sqrt_le_sqrt hη2
    have hw0 := Real.exp_pos (-(μ * s))
    calc Real.exp (-(μ * s)) * ‖ηm ζ μ (s, t)‖
        ≤ Real.exp (-(μ * s)) * (Real.sqrt C' * Real.sqrt (Fz ζ s) +
          (Real.sqrt C2 * Real.sqrt (Fz ζ s) + MA * (Real.sqrt C' * Real.sqrt (Fz ζ s)) +
            K * Real.sqrt (Fz ζ s))) :=
          mul_le_mul_of_nonneg_left (hsup.trans (add_le_add r2 (add_le_add
            (add_le_add r3 (mul_le_mul_of_nonneg_left r2 hMA0)) le_rfl))) hw0.le
      _ = Real.sqrt C' * (Real.exp (-(μ * s)) * Real.sqrt (Fz ζ s)) +
          (Real.sqrt C2 * (Real.exp (-(μ * s)) * Real.sqrt (Fz ζ s)) +
            MA * (Real.sqrt C' * (Real.exp (-(μ * s)) * Real.sqrt (Fz ζ s))) +
            K * (Real.exp (-(μ * s)) * Real.sqrt (Fz ζ s))) := by ring
      _ ≤ M1 :=
          add_le_add (mul_le_mul_of_nonneg_left r1 (Real.sqrt_nonneg _))
            (add_le_add (add_le_add (mul_le_mul_of_nonneg_left r1 (Real.sqrt_nonneg _))
              (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left r1 (Real.sqrt_nonneg _))
                hMA0)) (mul_le_mul_of_nonneg_left r1 hK.le))
  have hμMA : 0 ≤ (|μ| + MA) * M0 := mul_nonneg (add_nonneg (abs_nonneg μ) hMA0) hM0
  refine ⟨?_, hχb.trans (le_add_of_nonneg_left (add_nonneg hM1 hμMA)),
    hpSχ.trans (le_add_of_le_of_nonneg (le_add_of_nonneg_right hμMA) hM0), ?_⟩
  · exact hconv'
  · -- `pT χ`
    rw [pT_χr hζs μ hs0, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hr := hres0 (s, t) (mem_Ω hs0)
    simp only [res] at hr
    have e1 : pT ζ (s, t) = Jop n (pS ζ (s, t) + A (s, t) (ζ (s, t))) := by
      have : Jop n (pT ζ (s, t)) = -(pS ζ (s, t) + A (s, t) (ζ (s, t))) := by
        rw [eq_neg_iff_add_eq_zero, ← hr]; abel
      have h2 := congrArg (Jop n) this
      rw [Jop_Jop, map_neg] at h2
      rw [← neg_neg (pT ζ (s, t)), h2, neg_neg]
    rw [e1, norm_Jop]
    have e2 : pS ζ (s, t) = ηm ζ μ (s, t) + μ • ζ (s, t) := by simp [ηm]
    have hpSχ' := hpSχ
    rw [pS_χr hζs μ hs0, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hpSχ'
    have hχb' := hχb
    simp only [χ, χr, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hχb'
    have b1 : ‖pS ζ (s, t) + A (s, t) (ζ (s, t))‖ ≤
        ‖ηm ζ μ (s, t)‖ + (|μ| + MA) * ‖ζ (s, t)‖ := by
      rw [e2]
      refine (norm_add_le _ _).trans ?_
      have := ((A (s, t)).le_opNorm (ζ (s, t))).trans
        (mul_le_mul_of_nonneg_right (hMA t) (norm_nonneg _))
      have := norm_add_le (ηm ζ μ (s, t)) (μ • ζ (s, t))
      rw [norm_smul, Real.norm_eq_abs] at this
      linarith only [this, ‹‖A (s, t) (ζ (s, t))‖ ≤ MA * ‖ζ (s, t)‖›]
    have hw0 := Real.exp_pos (-(μ * s))
    calc Real.exp (-(μ * s)) * ‖pS ζ (s, t) + A (s, t) (ζ (s, t))‖
        ≤ Real.exp (-(μ * s)) * (‖ηm ζ μ (s, t)‖ + (|μ| + MA) * ‖ζ (s, t)‖) :=
          mul_le_mul_of_nonneg_left b1 hw0.le
      _ = Real.exp (-(μ * s)) * ‖ηm ζ μ (s, t)‖ +
          (|μ| + MA) * (Real.exp (-(μ * s)) * ‖ζ (s, t)‖) := by ring
      _ ≤ M1 + (|μ| + MA) * M0 :=
          add_le_add hpSχ' (mul_le_mul_of_nonneg_left hχb' (add_nonneg (abs_nonneg μ) hMA0))
      _ ≤ M1 + (|μ| + MA) * M0 + M0 := le_add_of_nonneg_right hM0

end HDecay

open HDecay in
theorem solution {n : ℕ} (S : ℝ × ℝ → CauchyRiemannIndex.Mat n)
    (hS : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × ℝ => S p i j)) (hSper : ∀ s t : ℝ, S (s, t + 1) = S (s, t))
    (Sinf : ℝ → CauchyRiemannIndex.Mat n) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (d : ℝ) (hd : 0 < d) (hSas : FiniteEnergyPlane.IsExpAsymptoticTo S Sinf d)
    (ζ : ℝ × ℝ → CauchyRiemannIndex.Vec n) (hζ : FiniteEnergyPlane.IsHalfCylSolution S ζ)
    (hne : ∃ p : ℝ × ℝ, 0 < p.1 ∧ ζ p ≠ 0)
    (C δ₀ : ℝ) (hgrowth : ∀ s > 0, ∀ t : ℝ, ‖ζ (s, t)‖ ≤ C * Real.exp (δ₀ * s)) :
    ∃ μ : ℝ, μ ≤ δ₀ ∧ ∃ e : ℝ → CauchyRiemannIndex.Vec n, FiniteEnergyPlane.IsLoopEigen Sinf μ e ∧
      ∃ s₀ > 0, ∃ M b K : ℝ, 0 < b ∧ ∀ s ≥ s₀, ∀ t : ℝ,
        ‖Real.exp (-(μ * s)) • ζ (s, t) - e t‖ ≤ K * Real.exp (-(b * s)) ∧
        ‖Real.exp (-(μ * s)) • ζ (s, t)‖ ≤ M ∧
        ‖fderiv ℝ (fun p : ℝ × ℝ => Real.exp (-(μ * p.1)) • ζ p) (s, t) (1, 0)‖ ≤ M ∧
        ‖fderiv ℝ (fun p : ℝ × ℝ => Real.exp (-(μ * p.1)) • ζ p) (s, t) (0, 1)‖ ≤ M :=
  stageE2 S hS hSper Sinf hSinf hSinf' d hd hSas ζ hζ hne C δ₀ hgrowth

end SP2
