-- Prove2me | solution 1 for FiniteEnergyPlane.halfCyl_exp_decay
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T02:27:15.65504+00:00
-- url     : https://prove2.me/submissions/1d5b013b-791e-40be-8eec-7f35fb18080b

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
    simpa [hX0, hY0] using this
  let _ : NormedAddCommGroup (Mat n) := Matrix.normedAddCommGroup
  let _ : NormedSpace ℝ (Mat n) := Matrix.normedSpace
  refine ⟨fun t => (TL n).symm (X t), fun t => (TL n).symm (Y t), ⟨?_, fun t => ?_⟩, ?_,
    fun t => ?_, fun t => ?_, fun t => ?_⟩
  · simp [hX0, ← TL_one]
  · have := (TL n).symm.hasFDerivAt.comp_hasDerivAt t (hX t)
    have hv : (TL n).symm (A t * X t) = J₀ n * Sinf t * (TL n).symm (X t) := by
      apply (TL n).injective
      simp [A, TL_mul]
    exact this.congr_deriv hv
  · simp [hY0, ← TL_one]
  · have := (TL n).symm.hasFDerivAt.comp_hasDerivAt t (hY t)
    have hv : (TL n).symm (Y t * -A t) = -((TL n).symm (Y t) * (J₀ n * Sinf t)) := by
      apply (TL n).injective
      simp [A, TL_mul]
    exact this.congr_deriv hv
  · apply (TL n).injective
    simp [TL_mul, hYX t, TL_one]
  · have h1 : (TL n).symm (Y t) * (TL n).symm (X t) = 1 := by
      apply (TL n).injective
      simp [TL_mul, hYX t, TL_one]
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

/-- Gap estimate: `sup |η| ≤ C ∫₀¹ |-J₀ η' - S∞ η|` for `1`-periodic `C¹` loops `η`. -/
theorem gap_sup (Sinf : ℝ → Mat n) (hS : IsSymLoop Sinf) (hnd : IsNondegenerate Sinf) :
    ∃ C, 0 ≤ C ∧ ∀ η η' : ℝ → Vec n, (∀ t, HasDerivAt η (η' t) t) → Continuous η' →
      Function.Periodic η 1 → ∀ t, ‖η t‖ ≤
        C * ∫ τ in (0:ℝ)..1, ‖-(Jop n (η' τ)) - TL n (Sinf τ) (η τ)‖ := by
  obtain ⟨Ψ, Φ, ⟨hΨ0, hΨ⟩, hΦ0, hΦ, hΦΨ, hΨΦ⟩ := fund_exists Sinf hS
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
  have hdet : IsUnit (1 - Ψ 1).det := isUnit_iff_ne_zero.2 (hnd Ψ ⟨hΨ0, hΨ⟩)
  set N : Mat n := (1 - Ψ 1)⁻¹
  have hN : N * (1 - Ψ 1) = 1 := Matrix.nonsing_inv_mul _ hdet
  set cJ : ℝ := ‖Jop n‖
  set C0 : ℝ := ‖TL n N‖ * (MP * (MQ * cJ))
  refine ⟨MP * (C0 + MQ * cJ), by positivity, ?_⟩
  intro η η' hη hη' hper
  have hηc : Continuous η := continuous_iff_continuousAt.2 fun t => (hη t).continuousAt
  set g : ℝ → Vec n := fun τ => -(Jop n (η' τ)) - TL n (Sinf τ) (η τ) with hg
  have hgc : Continuous g := by
    refine ((Jop n).continuous.comp hη').neg.sub ?_
    exact (((TL n).continuous.comp hS.1).clm_apply hηc)
  -- `Φ η` has derivative `Φ J g`
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
  have hw0 : w 0 = η 0 := by simp [w, hΦ0, TL_one]
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
      _ ≤ MQ * cJ * I1 := by
          gcongr
          exact intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
            (Eventually.of_forall fun _ => norm_nonneg _) (hgc.norm.intervalIntegrable _ _)
  have hI1 : 0 ≤ I1 := intervalIntegral.integral_nonneg zero_le_one fun _ _ => norm_nonneg _
  -- bound on `η 0`
  have h0 : ‖η 0‖ ≤ C0 * I1 := by
    have key : TL n (1 - Ψ 1) (η 0) = TL n (Ψ 1) (w 1 - w 0) := by
      have : w 1 = TL n (Φ 1) (η 0) := by simp [w, ← hper 0]
      have h1 : TL n (Ψ 1) (TL n (Φ 1) (η 0)) = η 0 := by
        rw [← ContinuousLinearMap.mul_apply, ← TL_mul, hΨΦ, TL_one]; rfl
      rw [this, hw0, map_sub, TL_one, map_sub, h1]
      simp
    have hv : η 0 = TL n N (TL n (1 - Ψ 1) (η 0)) := by
      rw [← ContinuousLinearMap.mul_apply, ← TL_mul, hN, TL_one]; rfl
    rw [hv, key, hint 1]
    calc ‖TL n N (TL n (Ψ 1) (∫ τ in (0:ℝ)..1, TL n (Φ τ) (Jop n (g τ))))‖
        ≤ ‖TL n N‖ * (‖TL n (Ψ 1)‖ * ‖∫ τ in (0:ℝ)..1, TL n (Φ τ) (Jop n (g τ))‖) :=
          ((TL n N).le_opNorm _).trans (mul_le_mul_of_nonneg_left
            ((TL n (Ψ 1)).le_opNorm _) (norm_nonneg _))
      _ ≤ ‖TL n N‖ * (MP * (MQ * cJ * I1)) := by
          gcongr
          · exact hMP 1 ⟨zero_le_one, le_rfl⟩
          · exact hI 1 ⟨zero_le_one, le_rfl⟩
      _ = C0 * I1 := by simp only [C0]; ring
  -- bound on `[0, 1]`
  have hIcc : ∀ t ∈ Ico (0:ℝ) 1, ‖η t‖ ≤ MP * (C0 + MQ * cJ) * I1 := by
    intro t ht
    have ht' : t ∈ Icc (0:ℝ) 1 := Ico_subset_Icc_self ht
    have hv : η t = TL n (Ψ t) (w t) := by
      simp only [w, ← ContinuousLinearMap.mul_apply, ← TL_mul, hΨΦ, TL_one]; rfl
    have hwt : w t = η 0 + ∫ τ in (0:ℝ)..t, TL n (Φ τ) (Jop n (g τ)) := by
      rw [← hint t, hw0]; abel
    rw [hv, hwt]
    calc ‖TL n (Ψ t) (η 0 + ∫ τ in (0:ℝ)..t, TL n (Φ τ) (Jop n (g τ)))‖
        ≤ ‖TL n (Ψ t)‖ * ‖η 0 + ∫ τ in (0:ℝ)..t, TL n (Φ τ) (Jop n (g τ))‖ :=
          (TL n (Ψ t)).le_opNorm _
      _ ≤ MP * (C0 * I1 + MQ * cJ * I1) :=
          mul_le_mul (hMP t ht') ((norm_add_le _ _).trans (add_le_add h0 (hI t ht')))
            (norm_nonneg _) hMP0
      _ = _ := by ring
  intro t
  obtain ⟨y, hy, hyt⟩ := hper.exists_mem_Ico₀ zero_lt_one t
  rw [hyt]
  exact hIcc y hy

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

lemma TPer.pT {u : ℝ × ℝ → F} (hu : TPer u) : TPer (pT u) := fun s t => by
  simp [HDecay.pT, hu.fderiv s t]

lemma TPer.periodic {u : ℝ × ℝ → F} (hu : TPer u) (s : ℝ) :
    Function.Periodic (fun t => u (s, t)) 1 := fun t => hu s t

/-! ### Operator-valued coefficients -/

variable {n : ℕ}

lemma pS_apply {A : ℝ × ℝ → Op n} {v : ℝ × ℝ → Vec n} (hA : Sm A) (hv : Sm v) {x} (hx : x ∈ Ω) :
    pS (fun y => A y (v y)) x = pS A x (v x) + A x (pS v x) := by
  simp only [pS]
  rw [fderiv_clm_apply (hA.diffAt hx) (hv.diffAt hx)]
  simp [add_comm]

lemma pT_apply {A : ℝ × ℝ → Op n} {v : ℝ × ℝ → Vec n} (hA : Sm A) (hv : Sm v) {x} (hx : x ∈ Ω) :
    pT (fun y => A y (v y)) x = pT A x (v x) + A x (pT v x) := by
  simp only [pT]
  rw [fderiv_clm_apply (hA.diffAt hx) (hv.diffAt hx)]
  simp [add_comm]

lemma Sm.apply {A : ℝ × ℝ → Op n} {v : ℝ × ℝ → Vec n} (hA : Sm A) (hv : Sm v) :
    Sm (fun y => A y (v y)) := hA.clm_apply hv

lemma pS_constOp (T : Op n) {v : ℝ × ℝ → Vec n} (hv : Sm v) {x} (hx : x ∈ Ω) :
    pS (fun y => T (v y)) x = T (pS v x) := by
  simp only [pS]
  rw [fderiv_clm_apply (differentiableAt_const _) (hv.diffAt hx)]
  simp

lemma pT_constOp (T : Op n) {v : ℝ × ℝ → Vec n} (hv : Sm v) {x} (hx : x ∈ Ω) :
    pT (fun y => T (v y)) x = T (pT v x) := by
  simp only [pT]
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

lemma Ip_ibp {u v : ℝ × ℝ → Vec n} (hu : Sm u) (hv : Sm v) (hpu : TPer u) (hpv : TPer v)
    {s : ℝ} (hs : 0 < s) : Ip (pT u) v s = -Ip u (pT v) s := by
  have h1 := cont_inner hu.dT.cont hv.cont hs
  have h2 := cont_inner hu.cont hv.dT.cont hs
  have key : ∫ t in (0:ℝ)..1, (⟪pT u (s, t), v (s, t)⟫ + ⟪u (s, t), pT v (s, t)⟫) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => ⟪u (s, t), v (s, t)⟫)
      (fun t _ => ((hu.hasDerivAt_t hs).inner ℝ (hv.hasDerivAt_t hs)).congr_deriv (add_comm _ _))
      ((h1.add h2).intervalIntegrable _ _)]
    rw [show (1:ℝ) = 0 + 1 by norm_num, hpu, hpv, sub_self]
  rw [intervalIntegral.integral_add (h1.intervalIntegrable _ _) (h2.intervalIntegrable _ _)] at key
  simp only [Ip]
  linarith

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
  simpa [pS] using this

lemma pS_pS_le (g : ℝ × ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (x : ℝ × ℝ) :
    |pS (pS g) x| ≤ ‖iteratedFDeriv ℝ 2 g x‖ := by
  have hd2 : DifferentiableAt ℝ (fderiv ℝ g) x :=
    ((hg.fderiv_right (m := 1) (WithTop.coe_le_coe.2 le_top)).differentiable one_ne_zero) x
  have h : pS (pS g) x = fderiv ℝ (fderiv ℝ g) x (1, 0) (1, 0) := by
    show fderiv ℝ (fun y => fderiv ℝ g y (1, 0)) x (1, 0) = _
    rw [show (fun y => fderiv ℝ g y (1, 0)) = fun y => (fderiv ℝ g y) ((fun _ => ((1:ℝ), (0:ℝ))) y)
      from rfl, fderiv_clm_apply hd2 (differentiableAt_const _)]
    simp
  rw [h, show fderiv ℝ (fderiv ℝ g) x (1, 0) (1, 0) = iteratedFDeriv ℝ 2 g x ![(1, 0), (1, 0)] by
    rw [iteratedFDeriv_two_apply]; rfl]
  have := (iteratedFDeriv ℝ 2 g x).le_opNorm ![(1, 0), (1, 0)]
  simpa [Fin.prod_univ_two] using this

/-- `∂ₛ` of an operator field built from a matrix field. -/
lemma hasFDerivAt_TL (S : ℝ × ℝ → Mat n) (hS : ∀ i j, Differentiable ℝ (fun p => S p i j))
    (x : ℝ × ℝ) : pS (fun p => TL n (S p)) x =
      TL n (Matrix.of fun i j => pS (fun p => S p i j) x) := by
  have hsum : (fun p => TL n (S p)) = fun p => ∑ i, ∑ j, S p i j • TL n (Matrix.single i j 1) := by
    funext p; exact TL_eq_sum _
  have hd : HasFDerivAt (fun p => ∑ i, ∑ j, S p i j • TL n (Matrix.single i j 1))
      (∑ i, ∑ j, (fderiv ℝ (fun p => S p i j) x).smulRight (TL n (Matrix.single i j 1))) x := by
    refine HasFDerivAt.fun_sum fun i _ => HasFDerivAt.fun_sum fun j _ => ?_
    exact ((hS i j) x).hasFDerivAt.smul_const (TL n (Matrix.single i j (1:ℝ)))
  rw [pS, hsum, hd.fderiv, TL_eq_sum (Matrix.of _)]
  simp [pS]

lemma contDiff_of_pS (S : ℝ × ℝ → Mat n) (hS : ∀ i j, ContDiff ℝ ∞ (fun p => S p i j)) :
    ∀ i j, ContDiff ℝ ∞ (fun p => (Matrix.of fun i j => pS (fun p => S p i j) p) i j) := by
  intro i j
  simp only [Matrix.of_apply, pS]
  exact (hS i j).fderiv_right (m := ∞) (by simp) |>.clm_apply contDiff_const

/-- entrywise smallness gives operator smallness -/
lemma op_small : ∃ c, 0 < c ∧ ∀ (M : Mat n) (δ : ℝ), 0 ≤ δ → (∀ i j, |M i j| ≤ δ) →
    ‖TL n M‖ ≤ c * δ := by
  set c0 := ∑ i, ∑ j, ‖TL n (Matrix.single i j (1:ℝ))‖
  have hc0 : 0 ≤ c0 := by positivity
  refine ⟨1 + c0, by positivity, fun M δ hδ hM => (norm_TL_le M).trans ?_⟩
  calc ∑ i, ∑ j, |M i j| * ‖TL n (Matrix.single i j 1)‖
      ≤ ∑ i, ∑ j, δ * ‖TL n (Matrix.single i j (1:ℝ))‖ :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_right (hM i j) (norm_nonneg _)
    _ = δ * c0 := by simp only [c0, Finset.mul_sum]
    _ ≤ (1 + c0) * δ := by nlinarith

lemma pS_snd (f : ℝ → ℝ) (hf : Differentiable ℝ f) (x : ℝ × ℝ) : pS (fun p => f p.2) x = 0 := by
  have : HasFDerivAt (fun p : ℝ × ℝ => f p.2) ((fderiv ℝ f x.2).comp (ContinuousLinearMap.snd ℝ ℝ ℝ)) x :=
    (hf x.2).hasFDerivAt.comp x hasFDerivAt_snd
  simp [pS, this.fderiv]

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
  simp [this]

theorem coeff_small (S : ℝ × ℝ → Mat n) (hS : ∀ i j, ContDiff ℝ ∞ (fun p => S p i j))
    (Sinf : ℝ → Mat n) (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (hSas : FiniteEnergyPlane.IsCInftyAsymptoticTo S Sinf) :
    ∀ ε > 0, ∃ s1 > 0, ∀ s ≥ s1, ∀ t, ‖TL n (S (s, t)) - TL n (Sinf t)‖ ≤ ε ∧
      ‖pS (fun p => TL n (S p)) (s, t)‖ ≤ ε ∧ ‖pS (pS (fun p => TL n (S p))) (s, t)‖ ≤ ε := by
  intro ε hε
  obtain ⟨c, hc, hcM⟩ := op_small (n := n)
  set δ := ε / c
  have hδ : 0 < δ := div_pos hε hc
  have hcδ : c * δ = ε := by simp only [δ]; field_simp
  have h := fun i j (m : ℕ) => (hSas i j).2 m δ hδ
  choose s1f hs1f using h
  set s1 := ∑ i, ∑ j, (|s1f i j 0| + |s1f i j 1| + |s1f i j 2|) + 1
  have hs1 : ∀ i j, s1f i j 0 ≤ s1 ∧ s1f i j 1 ≤ s1 ∧ s1f i j 2 ≤ s1 := by
    intro i j
    have hle : |s1f i j 0| + |s1f i j 1| + |s1f i j 2| ≤
        ∑ i, ∑ j, (|s1f i j 0| + |s1f i j 1| + |s1f i j 2|) := by
      refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, (|s1f i j 0| + |s1f i j 1| +
        |s1f i j 2|)) (fun i _ => by positivity) (Finset.mem_univ i))
      exact Finset.single_le_sum (f := fun j => |s1f i j 0| + |s1f i j 1| + |s1f i j 2|)
        (fun j _ => by positivity) (Finset.mem_univ j)
    have := le_abs_self (s1f i j 0); have := le_abs_self (s1f i j 1)
    have := le_abs_self (s1f i j 2); have := abs_nonneg (s1f i j 0)
    have := abs_nonneg (s1f i j 1); have := abs_nonneg (s1f i j 2)
    refine ⟨by linarith, by linarith, by linarith⟩
  have hs1pos : 0 < s1 := by
    have : 0 ≤ ∑ i, ∑ j, (|s1f i j 0| + |s1f i j 1| + |s1f i j 2|) := by positivity
    linarith
  refine ⟨s1, hs1pos, fun s hs t => ⟨?_, ?_, ?_⟩⟩
  · rw [← map_sub, ← hcδ]
    refine hcM _ δ hδ.le fun i j => ?_
    have := hs1f i j 0 s ((hs1 i j).1.trans hs) t
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    simpa using this
  · rw [hasFDerivAt_TL S (fun i j => (hS i j).differentiable (by simp)), ← hcδ]
    refine hcM _ δ hδ.le fun i j => ?_
    have := hs1f i j 1 s ((hs1 i j).2.1.trans hs) t
    simp only [Matrix.of_apply, pS_entry S hS Sinf hSinf']
    exact (pS_le0 _ _).trans this
  · have hfun : pS (fun p => TL n (S p)) = fun p => TL n (Matrix.of fun i j => pS (fun p => S p i j) p) :=
      funext (hasFDerivAt_TL S (fun i j => (hS i j).differentiable (by simp)))
    rw [hfun, hasFDerivAt_TL _ (fun i j => (contDiff_of_pS S hS i j).differentiable (by simp)), ← hcδ]
    refine hcM _ δ hδ.le fun i j => ?_
    have := hs1f i j 2 s ((hs1 i j).2.2.trans hs) t
    simp only [Matrix.of_apply, pS_entry S hS Sinf hSinf']
    have hg : ContDiff ℝ ∞ (fun p : ℝ × ℝ => S p i j - Sinf p.2 i j) :=
      (hS i j).sub ((hSinf' i j).comp contDiff_snd)
    exact (pS_pS_le _ hg _).trans this

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

lemma pS_sub {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {u v : ℝ × ℝ → F}
    (hu : Sm u) (hv : Sm v) {x} (hx : x ∈ Ω) : pS (u - v) x = pS u x - pS v x := by
  rw [sub_eq_add_neg, pS_add hu hv.neg hx, pS_neg, ← sub_eq_add_neg]

lemma ii {F : ℝ × ℝ → ℝ} (hF : ContinuousOn F Ω) {s : ℝ} (hs : 0 < s) :
    IntervalIntegrable (fun t => F (s, t)) volume 0 1 :=
  (cont_slice hF hs).intervalIntegrable _ _

section energy

variable (A : ℝ × ℝ → Op n) (η : ℝ × ℝ → Vec n)

/-- residual `∂ₛη + J₀ ∂ₜη + A η` -/
noncomputable def res (x : ℝ × ℝ) : Vec n := pS η x + Jop n (pT η x) + A x (η x)

/-- integrand of the second derivative -/
noncomputable def Qd (x : ℝ × ℝ) : ℝ :=
  2 * ⟪pS η x, pS η x⟫ + ⟪A x (η x), pS η x⟫ - ⟪η x, A x (pS η x)⟫ - ⟪res A η x, pS η x⟫ +
    ⟪η x, pS (res A η) x⟫ - ⟪η x, pS A x (η x)⟫

variable {A η}

lemma Sm.jop {v : ℝ × ℝ → Vec n} (hv : Sm v) : Sm (fun x => Jop n (v x)) :=
  (contDiffOn_const (c := Jop n)).clm_apply hv

lemma Sm.rs (hA : Sm A) (hη : Sm η) : Sm (res A η) :=
  ((hη.dS.add hη.dT.jop).add (hA.apply hη))

lemma TPer.rs (hpA : TPer A) (hpη : TPer η) : TPer (res A η) := fun s t => by
  simp [HDecay.res, hpA s t, hpη s t, hpη.pS s t, hpη.pT s t]

theorem energy_d2 (hA : Sm A) (hη : Sm η) (hpA : TPer A) (hpη : TPer η) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (Ip η (pS η)) (∫ t in (0:ℝ)..1, Qd A η (s, t)) s := by
  have hξ := hη.dS
  have h := Ip_hasDerivAt hη hξ hs
  refine h.congr_deriv ?_
  set ξ := pS η
  set r := res A η
  have hr : Sm r := Sm.rs hA hη
  -- `pS ξ` in terms of the equation
  have hξeq : ξ = fun x => r x - Jop n (pT η x) - A x (η x) := by
    funext x; simp only [r, res]; abel
  have hpSξ : ∀ x ∈ Ω, pS ξ x = pS r x - Jop n (pT ξ x) - (pS A x (η x) + A x (ξ x)) := by
    intro x hx
    conv_lhs => rw [hξeq]
    have e1 : (fun x => r x - Jop n (pT η x) - A x (η x)) =
        (r - fun x => Jop n (pT η x)) - fun x => A x (η x) := rfl
    rw [e1, pS_sub (hr.sub hη.dT.jop) (hA.apply hη) hx, pS_sub hr hη.dT.jop hx,
      pS_constOp _ hη.dT hx, pS_pT hη hx, pS_apply hA hη hx]
  -- integration by parts for the `J₀ ∂ₜ` term
  have hJ : Sm (fun x => Jop n (η x)) := hη.jop
  have hpJ : TPer (fun x => Jop n (η x)) := fun a b => by simp [hpη a b]
  have hibp := Ip_ibp hJ hξ hpJ hpη.pS hs
  have hpTJ : ∀ x ∈ Ω, pT (fun x => Jop n (η x)) x = r x - ξ x - A x (η x) := by
    intro x hx
    rw [pT_constOp _ hη hx]; simp only [r, res, ξ]; abel
  have hI1 : Ip η (fun x => Jop n (pT ξ x)) s = Ip (fun x => r x - ξ x - A x (η x)) ξ s := by
    have e1 : Ip η (fun x => Jop n (pT ξ x)) s = -Ip (fun x => Jop n (η x)) (pT ξ) s := by
      simp only [Ip, inner_Jop]
      exact intervalIntegral.integral_neg
    rw [e1, ← hibp]
    simp only [Ip]
    exact intervalIntegral.integral_congr fun t _ => by rw [hpTJ (s, t) (mem_Ω hs)]
  -- continuity facts
  have cη := hη.cont
  have cξ := hξ.cont
  have cr := hr.cont
  have cAη := (hA.apply hη).cont
  have cAξ := (hA.apply hξ).cont
  have cpr := hr.dS.cont
  have cpAη := (hA.dS.apply hη).cont
  have cJξ := hξ.dT.jop.cont
  -- rewrite `Ip η (pS ξ)`
  have hI2 : Ip η (pS ξ) s = ∫ t in (0:ℝ)..1, (⟪η (s, t), pS r (s, t)⟫ - ⟪η (s, t), Jop n (pT ξ (s, t))⟫ -
      ⟪η (s, t), pS A (s, t) (η (s, t))⟫ - ⟪η (s, t), A (s, t) (ξ (s, t))⟫) := by
    simp only [Ip]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [hpSξ (s, t) (mem_Ω hs), inner_sub_right, inner_sub_right, inner_add_right]
    ring
  rw [hI2]
  simp only [Ip] at hI1 ⊢
  have iA := ii (cη.inner cpr) hs
  have iB := ii (cη.inner cJξ) hs
  have iC := ii (cη.inner cpAη) hs
  have iD := ii (cη.inner cAξ) hs
  have iE := ii (cξ.inner cξ) hs
  have iF := ii (cAη.inner cξ) hs
  have iG := ii (cr.inner cξ) hs
  rw [intervalIntegral.integral_sub ((iA.sub iB).sub iC) iD, intervalIntegral.integral_sub (iA.sub iB) iC,
    intervalIntegral.integral_sub iA iB, hI1]
  have e3 : ∫ t in (0:ℝ)..1, ⟪r (s, t) - ξ (s, t) - A (s, t) (η (s, t)), ξ (s, t)⟫ =
      (∫ t in (0:ℝ)..1, ⟪r (s, t), ξ (s, t)⟫) - (∫ t in (0:ℝ)..1, ⟪ξ (s, t), ξ (s, t)⟫) -
        ∫ t in (0:ℝ)..1, ⟪A (s, t) (η (s, t)), ξ (s, t)⟫ := by
    simp only [inner_sub_left]
    rw [intervalIntegral.integral_sub (iG.sub iE) iF, intervalIntegral.integral_sub iG iE]
  have e4 : ∫ t in (0:ℝ)..1, Qd A η (s, t) = 2 * (∫ t in (0:ℝ)..1, ⟪ξ (s, t), ξ (s, t)⟫) +
      (∫ t in (0:ℝ)..1, ⟪A (s, t) (η (s, t)), ξ (s, t)⟫) - (∫ t in (0:ℝ)..1, ⟪η (s, t), A (s, t) (ξ (s, t))⟫) -
      (∫ t in (0:ℝ)..1, ⟪r (s, t), ξ (s, t)⟫) + (∫ t in (0:ℝ)..1, ⟪η (s, t), pS r (s, t)⟫) -
      ∫ t in (0:ℝ)..1, ⟪η (s, t), pS A (s, t) (η (s, t))⟫ := by
    simp only [Qd]
    rw [intervalIntegral.integral_sub (((((iE.const_mul 2).add iF).sub iD).sub iG).add iA) iC,
      intervalIntegral.integral_add ((((iE.const_mul 2).add iF).sub iD).sub iG) iA,
      intervalIntegral.integral_sub (((iE.const_mul 2).add iF).sub iD) iG,
      intervalIntegral.integral_sub ((iE.const_mul 2).add iF) iD,
      intervalIntegral.integral_add (iE.const_mul 2) iF, intervalIntegral.integral_const_mul]
  rw [e3, e4]
  ring

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

theorem gap_L2 (Sinf : ℝ → Mat n) (hS : IsSymLoop Sinf) (hnd : IsNondegenerate Sinf) :
    ∃ C2, 0 ≤ C2 ∧ ∀ η : ℝ × ℝ → Vec n, Sm η → TPer η → ∀ s > 0, Ip η η s ≤
      C2 * ∫ t in (0:ℝ)..1, ‖-(Jop n (pT η (s, t))) - TL n (Sinf t) (η (s, t))‖ ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := gap_sup Sinf hS hnd
  refine ⟨C ^ 2, by positivity, fun η hη hpη s hs => ?_⟩
  set g : ℝ → Vec n := fun t => -(Jop n (pT η (s, t))) - TL n (Sinf t) (η (s, t))
  have hgc : Continuous g :=
    ((Jop n).continuous.comp (cont_slice hη.dT.cont hs)).neg.sub
      (((TL n).continuous.comp hS.1).clm_apply (cont_slice hη.cont hs))
  have hpt := hC (fun t => η (s, t)) (fun t => pT η (s, t)) (fun t => hη.hasDerivAt_t hs)
    (cont_slice hη.dT.cont hs) (hpη.periodic s)
  have hI : ∫ t in (0:ℝ)..1, ‖g t‖ ≥ 0 :=
    intervalIntegral.integral_nonneg zero_le_one fun _ _ => norm_nonneg _
  have hpt2 : ∀ t, ⟪η (s, t), η (s, t)⟫ ≤ C ^ 2 * ∫ t in (0:ℝ)..1, ‖g t‖ ^ 2 := by
    intro t
    rw [real_inner_self_eq_norm_sq]
    calc ‖η (s, t)‖ ^ 2 ≤ (C * ∫ t in (0:ℝ)..1, ‖g t‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hpt t) 2
      _ = C ^ 2 * (∫ t in (0:ℝ)..1, ‖g t‖) ^ 2 := by ring
      _ ≤ C ^ 2 * ∫ t in (0:ℝ)..1, ‖g t‖ ^ 2 := by
          gcongr; exact sq_integral_le _ hgc.norm
  calc Ip η η s ≤ ∫ t in (0:ℝ)..1, C ^ 2 * ∫ t in (0:ℝ)..1, ‖g t‖ ^ 2 :=
        intervalIntegral.integral_mono_on zero_le_one
          ((cont_inner hη.cont hη.cont hs).intervalIntegrable _ _) intervalIntegrable_const
          fun t _ => hpt2 t
    _ = _ := by simp [g]

lemma mono_Ici (g g' : ℝ → ℝ) (a : ℝ) (hd : ∀ s ≥ a, HasDerivAt g (g' s) s)
    (hnn : ∀ s ≥ a, 0 ≤ g' s) : MonotoneOn g (Ici a) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici a)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt)
    (fun x hx => hnn x (interior_subset hx))

lemma anti_Ici (g g' : ℝ → ℝ) (a : ℝ) (hd : ∀ s ≥ a, HasDerivAt g (g' s) s)
    (hnp : ∀ s ≥ a, g' s ≤ 0) : AntitoneOn g (Ici a) := by
  have := mono_Ici (fun x => -g x) (fun x => -g' x) a (fun s hs => (hd s hs).neg)
    (fun s hs => by linarith [hnp s hs])
  intro x hx y hy hxy
  have := this hx hy hxy
  simp only at this
  linarith

/-- `f'' ≥ c² f`, `f ≥ 0`, `f → 0` ⇒ `f' ≤ 0` and `f(s) ≤ f(s₀) e^{-c(s - s₀)}`. -/
theorem ode_decay (f f1 f2 : ℝ → ℝ) (s0 c : ℝ) (hc : 0 < c)
    (hf : ∀ s ≥ s0, HasDerivAt f (f1 s) s) (hf1 : ∀ s ≥ s0, HasDerivAt f1 (f2 s) s)
    (hpos : ∀ s ≥ s0, 0 ≤ f s) (hlim : Tendsto f atTop (𝓝 0))
    (h2 : ∀ s ≥ s0, c ^ 2 * f s ≤ f2 s) :
    (∀ s ≥ s0, f1 s ≤ 0) ∧ ∀ s ≥ s0, f s ≤ f s0 * Real.exp (-(c * (s - s0))) := by
  have hf2 : ∀ s ≥ s0, 0 ≤ f2 s := fun s hs =>
    le_trans (mul_nonneg (sq_nonneg c) (hpos s hs)) (h2 s hs)
  have hm1 := mono_Ici f1 f2 s0 hf1 hf2
  have hneg : ∀ s ≥ s0, f1 s ≤ 0 := by
    intro a ha
    by_contra hpa
    push Not at hpa
    -- `f x ≥ f a + f1 a (x - a)`
    have hm := mono_Ici (fun x => f x - f1 a * x) (fun x => f1 x - f1 a) a
      (fun x hx => (hf x (ha.trans hx)).sub ((hasDerivAt_id x).const_mul (f1 a)) |>.congr_deriv
        (by simp))
      (fun x hx => by linarith [hm1 ha (show s0 ≤ x from ha.trans hx) hx])
    obtain ⟨N, hN⟩ := (eventually_atTop.1 (hlim.eventually (gt_mem_nhds zero_lt_one)))
    set x := max N (a + 2 / f1 a)
    have hpos2 : 0 < 2 / f1 a := by positivity
    have hxa : a ≤ x := le_trans (by linarith) (le_max_right N (a + 2 / f1 a))
    have h1 := hm (le_refl a) hxa hxa
    simp only at h1
    have h3 := hN x (le_max_left _ _)
    have h4 := hpos a ha
    have h5 : f1 a * (x - a) ≥ 2 := by
      have : x - a ≥ 2 / f1 a := by have := le_max_right N (a + 2 / f1 a); linarith
      calc f1 a * (x - a) ≥ f1 a * (2 / f1 a) := by gcongr
        _ = 2 := by field_simp
    nlinarith
  refine ⟨hneg, ?_⟩
  -- `w = f' + c f ≤ 0`
  have hw : ∀ s ≥ s0, f1 s + c * f s ≤ 0 := by
    intro a ha
    by_contra hpa
    push Not at hpa
    have hm := mono_Ici (fun x => Real.exp (-(c * x)) * (f1 x + c * f x))
      (fun x => Real.exp (-(c * x)) * (f2 x - c ^ 2 * f x)) a
      (fun x hx => by
        have hx0 : s0 ≤ x := ha.trans hx
        have e := ((hasDerivAt_id x).const_mul c).neg.exp.mul ((hf1 x hx0).add ((hf x hx0).const_mul c))
        refine e.congr_deriv ?_
        simp only [id, mul_one, Pi.neg_apply, Pi.add_apply, Pi.mul_apply]
        ring)
      (fun x hx => mul_nonneg (Real.exp_pos _).le (by linarith [h2 x (ha.trans hx)]))
    obtain ⟨N, hN⟩ := (eventually_atTop.1 (hlim.eventually
      (gt_mem_nhds (show 0 < (f1 a + c * f a) / c by positivity))))
    set x := max N a
    have hxa : a ≤ x := le_max_right _ _
    have h1 := hm (le_refl a) hxa hxa
    simp only at h1
    have hfx := hN x (le_max_left _ _)
    have hneg' := hneg x (ha.trans hxa)
    -- `exp(-cx) w(x) ≥ exp(-ca) w(a)` gives `w(x) ≥ w(a)`
    have hexp : Real.exp (-(c * a)) ≥ Real.exp (-(c * x)) := by
      apply Real.exp_le_exp.2; nlinarith
    have hwx : f1 x + c * f x ≥ f1 a + c * f a := by
      by_contra hlt
      push Not at hlt
      have : Real.exp (-(c * x)) * (f1 x + c * f x) < Real.exp (-(c * a)) * (f1 a + c * f a) := by
        calc Real.exp (-(c * x)) * (f1 x + c * f x) < Real.exp (-(c * x)) * (f1 a + c * f a) :=
              mul_lt_mul_of_pos_left hlt (Real.exp_pos _)
          _ ≤ Real.exp (-(c * a)) * (f1 a + c * f a) :=
              mul_le_mul_of_nonneg_right hexp hpa.le
      linarith
    have : c * f x < f1 a + c * f a := by
      have := (lt_div_iff₀ hc).1 hfx; linarith
    linarith
  -- `exp(c s) f s` is antitone
  have ha := anti_Ici (fun x => Real.exp (c * x) * f x)
    (fun x => Real.exp (c * x) * (f1 x + c * f x)) s0
    (fun x hx => by
      have e := ((hasDerivAt_id x).const_mul c).exp.mul (hf x hx)
      refine e.congr_deriv ?_
      simp only [id, mul_one, Pi.neg_apply, Pi.add_apply, Pi.mul_apply]
      ring)
    (fun x hx => mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (hw x hx))
  intro s hs
  have h := ha (le_refl s0) hs hs
  simp only at h
  have e : Real.exp (-(c * (s - s0))) = Real.exp (c * s0) / Real.exp (c * s) := by
    rw [← Real.exp_sub]; ring_nf
  rw [e, mul_div_assoc', le_div_iff₀ (Real.exp_pos _)]
  linarith

/-- a convex nonnegative function with bounded integrals on `[a, ∞)` is nonincreasing -/
theorem convex_bdd_anti (h h1 h2 : ℝ → ℝ) (a B : ℝ) (hd : ∀ s ≥ a, HasDerivAt h (h1 s) s)
    (hd1 : ∀ s ≥ a, HasDerivAt h1 (h2 s) s) (h2nn : ∀ s ≥ a, 0 ≤ h2 s)
    (hnn : ∀ s ≥ a, 0 ≤ h s) (hB : ∀ b ≥ a, ∫ x in a..b, h x ≤ B) : AntitoneOn h (Ici a) := by
  have hm1 := mono_Ici h1 h2 a hd1 h2nn
  have hcont : ContinuousOn h (Ici a) := fun x hx => (hd x hx).continuousAt.continuousWithinAt
  refine anti_Ici h h1 a hd fun c0 hc0 => ?_
  by_contra hpc
  push Not at hpc
  have hm := mono_Ici (fun x => h x - h1 c0 * x) (fun x => h1 x - h1 c0) c0
    (fun x hx => (hd x (hc0.trans hx)).sub ((hasDerivAt_id x).const_mul (h1 c0)) |>.congr_deriv
      (by simp))
    (fun x hx => by linarith [hm1 hc0 (show a ≤ x from hc0.trans hx) hx])
  -- on `[c0 + 1, b]`, `h ≥ h1 c0`
  have hlow : ∀ x ≥ c0 + 1, h1 c0 ≤ h x := by
    intro x hx
    have := hm (le_refl c0) (show c0 ≤ x by linarith) (show c0 ≤ x by linarith)
    simp only at this
    nlinarith [hnn c0 hc0]
  set b := c0 + 2 + (|B| + 1) / h1 c0
  have hb1 : c0 + 1 ≤ b := by have : 0 < (|B| + 1) / h1 c0 := by positivity
                              simp only [b]; linarith
  have hint : ∀ u v, a ≤ u → u ≤ v → IntervalIntegrable h volume u v := fun u v hu huv =>
    (hcont.mono (by rw [uIcc_of_le huv]; exact Icc_subset_Ici_iff huv |>.2 hu)).intervalIntegrable
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hint a (c0 + 1) le_rfl (by linarith))
    (hint (c0 + 1) b (by linarith) hb1)
  have hI1 : 0 ≤ ∫ x in a..(c0 + 1), h x :=
    intervalIntegral.integral_nonneg (by linarith) fun x hx => hnn x hx.1
  have hI2 : ∫ x in (c0 + 1)..b, h1 c0 ≤ ∫ x in (c0 + 1)..b, h x :=
    intervalIntegral.integral_mono_on hb1 intervalIntegrable_const (hint _ _ (by linarith) hb1)
      fun x hx => hlow x hx.1
  rw [intervalIntegral.integral_const, smul_eq_mul] at hI2
  have hbB := hB b (by linarith)
  have : (b - (c0 + 1)) * h1 c0 ≥ |B| + 1 := by
    have e : b - (c0 + 1) = 1 + (|B| + 1) / h1 c0 := by simp only [b]; ring
    rw [e, add_mul, div_mul_cancel₀ _ hpc.ne']
    linarith
  linarith [le_abs_self B]

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

lemma Qd_cont {A : ℝ × ℝ → Op n} {η : ℝ × ℝ → Vec n} (hA : Sm A) (hη : Sm η) :
    ContinuousOn (Qd A η) Ω := by
  have hr := Sm.rs hA hη
  have c1 := hη.dS.cont
  unfold Qd
  refine (((((continuousOn_const.mul (c1.inner c1)).add ((hA.apply hη).cont.inner c1)).sub
    (hη.cont.inner (hA.apply hη.dS).cont)).sub (hr.cont.inner c1)).add
    (hη.cont.inner hr.dS.cont)).sub (hη.cont.inner (hA.dS.apply hη).cont)

lemma abs_inner_op (T : Op n) (v w : Vec n) : |⟪T v, w⟫| ≤ ‖T‖ * ‖v‖ * ‖w‖ :=
  (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (T.le_opNorm v) (norm_nonneg _))

theorem energy_lower (Sinf : ℝ → Mat n) (hS : IsSymLoop Sinf) (C2 : ℝ) (hC2 : 0 ≤ C2)
    (hgap : ∀ η : ℝ × ℝ → Vec n, Sm η → TPer η → ∀ s > 0, Ip η η s ≤
      C2 * ∫ t in (0:ℝ)..1, ‖-(Jop n (pT η (s, t))) - TL n (Sinf t) (η (s, t))‖ ^ 2)
    {A : ℝ × ℝ → Op n} (hA : Sm A) {η w : ℝ × ℝ → Vec n} (hη : Sm η) (hpη : TPer η)
    (hw : Sm w) {s : ℝ} (hs : 0 < s) {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (hA1 : ∀ t, ‖A (s, t) - TL n (Sinf t)‖ ≤ ε) (hA2 : ∀ t, ‖pS A (s, t)‖ ≤ ε)
    (hr : ∀ t, ‖res A η (s, t)‖ ≤ ε * ‖w (s, t)‖)
    (hr' : ∀ t, ‖pS (res A η) (s, t)‖ ≤ ε * (‖w (s, t)‖ + ‖η (s, t)‖)) :
    Ip η η s ≤ 3 * C2 * (Ip (pS η) (pS η) s + ε ^ 2 * Ip η η s + ε ^ 2 * Ip w w s) ∧
    Ip (pS η) (pS η) s - 4 * ε * Ip η η s - ε * Ip w w s ≤ ∫ t in (0:ℝ)..1, Qd A η (s, t) := by
  have hξ := hη.dS
  have iξ := ii (hξ.cont.inner hξ.cont) hs
  have iη := ii (hη.cont.inner hη.cont) hs
  have iw := ii (hw.cont.inner hw.cont) hs
  constructor
  · set g : ℝ → Vec n := fun t => -(Jop n (pT η (s, t))) - TL n (Sinf t) (η (s, t))
    have hgc : Continuous g :=
      ((Jop n).continuous.comp (cont_slice hη.dT.cont hs)).neg.sub
        (((TL n).continuous.comp hS.1).clm_apply (cont_slice hη.cont hs))
    have hpt : ∀ t, ‖g t‖ ^ 2 ≤ 3 * (⟪pS η (s, t), pS η (s, t)⟫ + ε ^ 2 * ⟪η (s, t), η (s, t)⟫ +
        ε ^ 2 * ⟪w (s, t), w (s, t)⟫) := by
      intro t
      have e : g t = pS η (s, t) + (A (s, t) - TL n (Sinf t)) (η (s, t)) - res A η (s, t) := by
        simp only [g, res, ContinuousLinearMap.sub_apply]; abel
      have h1 : ‖g t‖ ≤ ‖pS η (s, t)‖ + ε * ‖η (s, t)‖ + ε * ‖w (s, t)‖ := by
        rw [e]
        refine (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add le_rfl ?_))
          (hr t))
        exact ((A (s, t) - TL n (Sinf t)).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hA1 t) (norm_nonneg _))
      simp only [real_inner_self_eq_norm_sq]
      have h0 := norm_nonneg (g t)
      nlinarith [sq_nonneg (‖pS η (s, t)‖ - ε * ‖η (s, t)‖), sq_nonneg (‖pS η (s, t)‖ - ε * ‖w (s, t)‖),
        sq_nonneg (ε * ‖η (s, t)‖ - ε * ‖w (s, t)‖), norm_nonneg (pS η (s, t)),
        mul_nonneg hε0 (norm_nonneg (η (s, t))), mul_nonneg hε0 (norm_nonneg (w (s, t)))]
    refine (hgap η hη hpη s hs).trans ?_
    have hint : ∫ t in (0:ℝ)..1, ‖g t‖ ^ 2 ≤ ∫ t in (0:ℝ)..1, 3 * (⟪pS η (s, t), pS η (s, t)⟫ +
        ε ^ 2 * ⟪η (s, t), η (s, t)⟫ + ε ^ 2 * ⟪w (s, t), w (s, t)⟫) :=
      intervalIntegral.integral_mono_on zero_le_one ((hgc.norm.pow 2).intervalIntegrable _ _)
        (((iξ.add (iη.const_mul _)).add (iw.const_mul _)).const_mul _) fun t _ => hpt t
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add (iξ.add (iη.const_mul _))
      (iw.const_mul _), intervalIntegral.integral_add iξ (iη.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hint
    simp only [Ip]
    have := mul_le_mul_of_nonneg_left hint hC2
    linarith
  · have hpt : ∀ t, ⟪pS η (s, t), pS η (s, t)⟫ - 4 * ε * ⟪η (s, t), η (s, t)⟫ -
        ε * ⟪w (s, t), w (s, t)⟫ ≤ Qd A η (s, t) := by
      intro t
      set ξv := pS η (s, t)
      set ηv := η (s, t)
      set wv := w (s, t)
      set D := A (s, t) - TL n (Sinf t)
      have hsym : ⟪A (s, t) ηv, ξv⟫ - ⟪ηv, A (s, t) ξv⟫ = ⟪D ηv, ξv⟫ - ⟪ηv, D ξv⟫ := by
        have := inner_symm (hS.2.2 t) ηv ξv
        simp only [D, ContinuousLinearMap.sub_apply, inner_sub_left, inner_sub_right]
        linarith
      have b1 := abs_inner_op D ηv ξv
      have b2 : |⟪ηv, D ξv⟫| ≤ ‖D‖ * ‖ξv‖ * ‖ηv‖ := by rw [real_inner_comm]; exact abs_inner_op _ _ _
      have b3 : |⟪res A η (s, t), ξv⟫| ≤ ε * ‖wv‖ * ‖ξv‖ :=
        (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hr t) (norm_nonneg _))
      have b4 : |⟪ηv, pS (res A η) (s, t)⟫| ≤ ‖ηv‖ * (ε * (‖wv‖ + ‖ηv‖)) :=
        (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hr' t) (norm_nonneg _))
      have b5 : |⟪ηv, pS A (s, t) ηv⟫| ≤ ‖pS A (s, t)‖ * ‖ηv‖ * ‖ηv‖ := by
        rw [real_inner_comm]; exact abs_inner_op _ _ _
      have hD := hA1 t
      have hAs := hA2 t
      have q : Qd A η (s, t) = 2 * ⟪ξv, ξv⟫ + (⟪D ηv, ξv⟫ - ⟪ηv, D ξv⟫) - ⟪res A η (s, t), ξv⟫ +
          ⟪ηv, pS (res A η) (s, t)⟫ - ⟪ηv, pS A (s, t) ηv⟫ := by
        rw [← hsym]; simp only [Qd]; ring
      rw [q]
      simp only [real_inner_self_eq_norm_sq]
      have na := norm_nonneg ξv
      have nb := norm_nonneg ηv
      have nc := norm_nonneg wv
      have e1 : ‖D‖ * ‖ηv‖ * ‖ξv‖ ≤ ε * ‖ηv‖ * ‖ξv‖ := by gcongr
      have e2 : ‖D‖ * ‖ξv‖ * ‖ηv‖ ≤ ε * ‖ξv‖ * ‖ηv‖ := by gcongr
      have e5 : ‖pS A (s, t)‖ * ‖ηv‖ * ‖ηv‖ ≤ ε * ‖ηv‖ * ‖ηv‖ := by gcongr
      have a1 := neg_abs_le ⟪D ηv, ξv⟫
      have a2 := le_abs_self ⟪ηv, D ξv⟫
      have a3 := le_abs_self ⟪res A η (s, t), ξv⟫
      have a4 := neg_abs_le ⟪ηv, pS (res A η) (s, t)⟫
      have a5 := le_abs_self ⟪ηv, pS A (s, t) ηv⟫
      nlinarith [mul_nonneg hε0 (sq_nonneg (‖ξv‖ - ‖ηv‖)), mul_nonneg hε0 (sq_nonneg (‖ξv‖ - ‖wv‖)),
        mul_nonneg hε0 (sq_nonneg (‖ηv‖ - ‖wv‖)), mul_nonneg (by linarith : 0 ≤ 1 / 2 - ε) (sq_nonneg ‖ξv‖)]
    have hQ := ii (Qd_cont hA hη) hs
    have hint := intervalIntegral.integral_mono_on zero_le_one
      ((iξ.sub (iη.const_mul _)).sub (iw.const_mul _)) hQ fun t _ => hpt t
    rw [intervalIntegral.integral_sub (iξ.sub (iη.const_mul _)) (iw.const_mul _),
      intervalIntegral.integral_sub iξ (iη.const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul] at hint
    exact hint

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

lemma int_bound (G f f1 f2 : ℝ → ℝ) (a β : ℝ) (ha : 0 < a) (hG : ContinuousOn G (Ioi 0))
    (hf : ContinuousOn f (Ioi 0)) (hf1 : ∀ s ≥ a, HasDerivAt f1 (f2 s) s)
    (hle : ∀ s ≥ a, G s ≤ f2 s / 2 + β * f s) :
    ∀ b ≥ a, ∫ x in a..b, G x ≤ (f1 b - f1 a) / 2 + β * ∫ x in a..b, f x := by
  have hii : ∀ {g : ℝ → ℝ}, ContinuousOn g (Ioi 0) → ∀ x ≥ a, IntervalIntegrable g volume a x :=
    fun {g} hg x hx => (hg.mono (by
      rw [uIcc_of_le hx]; intro y hy; exact lt_of_lt_of_le ha hy.1)).intervalIntegrable
  have hpd : ∀ {g : ℝ → ℝ}, ContinuousOn g (Ioi 0) → ∀ x ≥ a,
      HasDerivAt (fun x => ∫ y in a..x, g y) (g x) x := by
    intro g hg x hx
    have hx0 : x ∈ Ioi (0:ℝ) := lt_of_lt_of_le ha hx
    exact intervalIntegral.integral_hasDerivAt_right (hii hg x hx)
      (hg.stronglyMeasurableAtFilter isOpen_Ioi x hx0)
      (hg.continuousAt (isOpen_Ioi.mem_nhds hx0))
  have hanti := anti_Ici (fun x => (∫ y in a..x, G y) - f1 x / 2 - β * ∫ y in a..x, f y)
    (fun x => G x - f2 x / 2 - β * f x) a
    (fun x hx => (((hpd hG x hx).sub ((hf1 x hx).div_const 2)).sub
      ((hpd hf x hx).const_mul β)))
    (fun x hx => by linarith [hle x hx])
  intro b hb
  have := hanti (le_refl a) hb hb
  simp only [intervalIntegral.integral_same] at this
  linarith

/-- from monotonicity of `f'`: `-f'(a) ≤ f(a - 1)` when `f ≥ 0` -/
lemma secant (f f1 : ℝ → ℝ) (a : ℝ) (hf : ∀ x ∈ Icc (a - 1) a, HasDerivAt f (f1 x) x)
    (hm : ∀ x ∈ Icc (a - 1) a, f1 x ≤ f1 a) (hpos : 0 ≤ f a) : -f1 a ≤ f (a - 1) := by
  obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope f f1 (show a - 1 < a by linarith)
    (fun x hx => (hf x hx).continuousAt.continuousWithinAt)
    (fun x hx => hf x (Ioo_subset_Icc_self hx))
  have h := hm ξ (Ioo_subset_Icc_self hξ)
  rw [hξe, show a - (a - 1) = 1 by ring, div_one] at h
  linarith

end HDecay

end HD_j

section HD_k

/-! `L²` exponential decay of `ζ` and `∂ₛζ`. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

lemma exp_shift (c a b : ℝ) : Real.exp (-(c * (a - b))) = Real.exp (c * b) * Real.exp (-(c * a)) := by
  rw [← Real.exp_add]; ring_nf

set_option maxHeartbeats 1000000 in
theorem L2_decay (S : ℝ × ℝ → Mat n) (hS : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × ℝ => S p i j))
    (hSper : ∀ s t : ℝ, S (s, t + 1) = S (s, t))
    (Sinf : ℝ → Mat n) (hSinf : IsSymLoop Sinf) (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (hSas : FiniteEnergyPlane.IsCInftyAsymptoticTo S Sinf) (hnd : IsNondegenerate Sinf)
    (ζ : ℝ × ℝ → Vec n) (hζ : FiniteEnergyPlane.IsHalfCylSolution S ζ)
    (hζ0 : FiniteEnergyPlane.TendstoZeroUnif ζ) :
    ∃ s2 > 0, ∃ c > 0, ∃ M, ∀ s ≥ s2, Ip ζ ζ s ≤ M * Real.exp (-(c * s)) ∧
      Ip (pS ζ) (pS ζ) s ≤ M * Real.exp (-(c * s)) := by
  set A : ℝ × ℝ → Op n := fun p => TL n (S p)
  have hA : Sm A := (contDiff_TL S hS).contDiffOn
  have hpA : TPer A := fun s t => by simp only [A, hSper s t]
  have hζs : Sm ζ := hζ.1
  have hpζ : TPer ζ := hζ.2.1
  have hres0 : ∀ x ∈ Ω, res A ζ x = 0 := by
    rintro ⟨a, b⟩ hx
    exact hζ.2.2 a hx.1 b
  have hpres0 : ∀ x ∈ Ω, pS (res A ζ) x = 0 := by
    intro x hx
    rw [pS_congr (v := fun _ => (0 : Vec n)) hres0 hx]
    simp [pS]
  obtain ⟨C2, hC2, hgap⟩ := gap_L2 Sinf hSinf hnd
  set K := C2 + 1 with hKd
  have hCK : 3 * C2 ≤ 3 * K := by rw [hKd]; linarith
  have hK1 : 1 ≤ K := by simp only [K]; linarith
  set u := 1 / K
  have hu0 : 0 < u := by positivity
  have hu1 : u ≤ 1 := by rw [div_le_one (by linarith)]; exact hK1
  have hKu : K * u = 1 := by simp only [u]; field_simp
  set ε := u / 100 with hεd
  have hε0 : 0 < ε := by positivity
  have hε : ε ≤ 1 / 2 := by simp only [ε]; linarith
  obtain ⟨s1, hs1, hco⟩ := coeff_small S hS Sinf hSinf' hSas ε hε0
  set ξ := pS ζ
  have hξ : Sm ξ := hζs.dS
  set f := Ip ζ ζ
  set G := Ip ξ ξ
  set f1 : ℝ → ℝ := fun s => 2 * Ip ζ ξ s
  set f2 : ℝ → ℝ := fun s => 2 * ∫ t in (0:ℝ)..1, Qd A ζ (s, t)
  have hfd : ∀ s > 0, HasDerivAt f (f1 s) s := fun s hs =>
    (Ip_hasDerivAt hζs hζs hs).congr_deriv (by simp only [f1]; rw [Ip_comm ξ ζ]; ring)
  have hf1d : ∀ s > 0, HasDerivAt f1 (f2 s) s := fun s hs =>
    (energy_d2 hA hζs hpA hpζ hs).const_mul 2
  have hfnn : ∀ s, 0 ≤ f s := fun s => Ip_self_nonneg _ _
  have hGnn : ∀ s, 0 ≤ G s := fun s => Ip_self_nonneg _ _
  -- first application: `η = ζ`
  have app1 : ∀ s ≥ s1, u * f s ≤ 4 * G s ∧ G s - 5 * ε * f s ≤ f2 s / 2 := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le hs1 hs
    obtain ⟨L1, L2⟩ := energy_lower Sinf hSinf C2 hC2 hgap hA hζs hpζ hζs hs0 hε0.le hε
      (fun t => (hco s hs t).1) (fun t => (hco s hs t).2.1)
      (fun t => by rw [hres0 _ (mem_Ω hs0), norm_zero]; positivity)
      (fun t => by rw [hpres0 _ (mem_Ω hs0), norm_zero]; positivity)
    constructor
    · have h1 : 3 * C2 * (G s + ε ^ 2 * f s + ε ^ 2 * f s) ≤ 3 * K * (G s + ε ^ 2 * f s + ε ^ 2 * f s) :=
        mul_le_mul_of_nonneg_right hCK (by have := hfnn s; have := hGnn s; positivity)
      have h2 : u * f s ≤ u * (3 * K * (G s + ε ^ 2 * f s + ε ^ 2 * f s)) :=
        mul_le_mul_of_nonneg_left (L1.trans h1) hu0.le
      have h3 : u * (3 * K * (G s + ε ^ 2 * f s + ε ^ 2 * f s)) = 3 * (G s + 2 * ε ^ 2 * f s) := by
        rw [show u * (3 * K * (G s + ε ^ 2 * f s + ε ^ 2 * f s)) =
          (K * u) * (3 * (G s + 2 * ε ^ 2 * f s)) by ring, hKu, one_mul]
      have h4 : ε ^ 2 ≤ u / 10000 := by rw [hεd]; nlinarith
      nlinarith [hfnn s, hGnn s]
    · have : (∫ t in (0:ℝ)..1, Qd A ζ (s, t)) = f2 s / 2 := by simp only [f2]; ring
      rw [← this]; linarith
  set c := u / 6
  have hc : 0 < c := by positivity
  have hf2 : ∀ s ≥ s1, c ^ 2 * f s ≤ f2 s := by
    intro s hs
    obtain ⟨h1, h2⟩ := app1 s hs
    have : c ^ 2 ≤ u / 36 := by simp only [c]; nlinarith
    have hf := hfnn s
    have e1 : c ^ 2 * f s ≤ u / 36 * f s := mul_le_mul_of_nonneg_right this hf
    have e2 : ε * f s = u * f s / 100 := by rw [hεd]; ring
    have e3 : 0 ≤ u * f s := mul_nonneg hu0.le hf
    linarith
  have hflim : Tendsto f atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨s₀, hs₀⟩ := hζ0 (min 1 (δ / 2)) (by positivity)
    refine ⟨max s₀ 1, fun s hs => ?_⟩
    have hs0 : 0 < s := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hs)
    have hb : f s ≤ min 1 (δ / 2) ^ 2 := by
      have := intervalIntegral.integral_mono_on zero_le_one
        (ii (hζs.cont.inner hζs.cont) hs0) intervalIntegrable_const
        (fun t _ => show ⟪ζ (s, t), ζ (s, t)⟫ ≤ min 1 (δ / 2) ^ 2 by
          rw [real_inner_self_eq_norm_sq]
          exact pow_le_pow_left₀ (norm_nonneg _) (hs₀ s (le_trans (le_max_left _ _) hs) t) 2)
      simp only [intervalIntegral.integral_const, sub_zero, one_smul] at this
      exact this
    have hm1 : min 1 (δ / 2) ≤ 1 := min_le_left _ _
    have hm2 : min 1 (δ / 2) ≤ δ / 2 := min_le_right _ _
    have hm0 : 0 < min 1 (δ / 2) := by positivity
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hfnn s)]
    nlinarith
  obtain ⟨hf1neg, hfdec⟩ := ode_decay f f1 f2 s1 c hc (fun s hs => hfd s (lt_of_lt_of_le hs1 hs))
    (fun s hs => hf1d s (lt_of_lt_of_le hs1 hs)) (fun s _ => hfnn s) hflim hf2
  set M0 := f s1 * Real.exp (c * s1)
  have hM0 : 0 ≤ M0 := mul_nonneg (hfnn s1) (Real.exp_pos _).le
  have hfM : ∀ s ≥ s1, f s ≤ M0 * Real.exp (-(c * s)) := by
    intro s hs
    have := hfdec s hs
    rw [exp_shift] at this
    simpa only [M0, mul_assoc] using this
  -- continuity in `s`
  have hfc : ContinuousOn f (Ioi 0) := fun s hs => (hfd s hs).continuousAt.continuousWithinAt
  have hGd : ∀ s > 0, HasDerivAt G (2 * Ip ξ (pS ξ) s) s := fun s hs =>
    (Ip_hasDerivAt hξ hξ hs).congr_deriv (by rw [Ip_comm (pS ξ) ξ]; ring)
  have hGc : ContinuousOn G (Ioi 0) := fun s hs => (hGd s hs).continuousAt.continuousWithinAt
  -- `∫ₐᵇ f ≤ M0 e^{-ca} / c`
  have hIf : ∀ a ≥ s1, ∀ b ≥ a, ∫ x in a..b, f x ≤ M0 * (Real.exp (-(c * a)) / c) := by
    intro a ha b hb
    have hint := intervalIntegral.integral_mono_on hb
      (hfc.mono (by rw [uIcc_of_le hb]; intro y hy; exact lt_of_lt_of_le hs1 (ha.trans hy.1)) |>.intervalIntegrable (μ := volume))
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).intervalIntegrable a b |>.const_mul M0)
      (fun x hx => hfM x (ha.trans hx.1))
    rw [intervalIntegral.integral_const_mul] at hint
    exact hint.trans (mul_le_mul_of_nonneg_left (int_exp_le hc hb) hM0)
  -- `∫ₐᵇ G ≤ M1 e^{-ca}`
  set M1 := M0 * Real.exp c / 2 + 5 * ε * M0 / c
  have hM1 : 0 ≤ M1 := by positivity
  have hIG : ∀ a ≥ s1 + 1, ∀ b ≥ a, ∫ x in a..b, G x ≤ M1 * Real.exp (-(c * a)) := by
    intro a ha b hb
    have ha1 : s1 ≤ a := by linarith
    have hib := int_bound G f f1 f2 a (5 * ε) (lt_of_lt_of_le hs1 ha1) hGc hfc
      (fun s hs => hf1d s (lt_of_lt_of_le hs1 (ha1.trans hs)))
      (fun s hs => by have := (app1 s (ha1.trans hs)).2; linarith) b hb
    have hsec := secant f f1 a (fun x hx => hfd x (lt_of_lt_of_le hs1 (by linarith [hx.1])))
      (fun x hx => mono_Ici f1 f2 s1 (fun s hs => hf1d s (lt_of_lt_of_le hs1 hs))
        (fun s hs => le_trans (mul_nonneg (sq_nonneg c) (hfnn s)) (hf2 s hs))
        (show s1 ≤ x by linarith [hx.1]) ha1 hx.2) (hfnn a)
    have hfa := hfM (a - 1) (by linarith)
    rw [show -(c * (a - 1)) = c + -(c * a) by ring, Real.exp_add] at hfa
    have hb1 := hf1neg b (ha1.trans hb)
    have hIfa := hIf a ha1 b hb
    have e1 : 5 * ε * (M0 * (Real.exp (-(c * a)) / c)) = 5 * ε * M0 / c * Real.exp (-(c * a)) := by ring
    have : (f1 b - f1 a) / 2 + 5 * ε * ∫ x in a..b, f x ≤ M1 * Real.exp (-(c * a)) := by
      have h5 : 5 * ε * ∫ x in a..b, f x ≤ 5 * ε * (M0 * (Real.exp (-(c * a)) / c)) :=
        mul_le_mul_of_nonneg_left hIfa (by positivity)
      simp only [M1]
      nlinarith
    linarith
  -- second application: `η = ξ = ∂ₛζ`
  have hresξ : ∀ x ∈ Ω, res A ξ x = -(pS A x (ζ x)) := by
    intro x hx
    have h0 := hpres0 x hx
    have e : res A ζ = (pS ζ + fun y => Jop n (pT ζ y)) + fun y => A y (ζ y) := rfl
    rw [e, pS_add (hζs.dS.add hζs.dT.jop) (hA.apply hζs) hx, pS_add hζs.dS hζs.dT.jop hx,
      pS_constOp _ hζs.dT hx, pS_pT hζs hx, pS_apply hA hζs hx] at h0
    calc res A ξ x = (pS (pS ζ) x + Jop n (pT (pS ζ) x) + (pS A x (ζ x) + A x (pS ζ x))) -
          pS A x (ζ x) := by simp only [res, ξ]; abel
      _ = -(pS A x (ζ x)) := by rw [h0, zero_sub]
  have hpresξ : ∀ x ∈ Ω, pS (res A ξ) x = -(pS (pS A) x (ζ x) + pS A x (ξ x)) := by
    intro x hx
    rw [pS_congr (v := fun y => -(pS A y (ζ y))) hresξ hx,
      show (fun y => -(pS A y (ζ y))) = -(fun y => pS A y (ζ y)) from rfl, pS_neg,
      pS_apply hA.dS hζs hx]
  set g1 : ℝ → ℝ := fun s => 2 * Ip ξ (pS ξ) s
  set g2 : ℝ → ℝ := fun s => 2 * ∫ t in (0:ℝ)..1, Qd A ξ (s, t)
  have hg1d : ∀ s > 0, HasDerivAt g1 (g2 s) s := fun s hs =>
    (energy_d2 hA hξ hpA hpζ.pS hs).const_mul 2
  have app2 : ∀ s ≥ s1, -(2 * f s) ≤ g2 s := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le hs1 hs
    obtain ⟨L1, L2⟩ := energy_lower Sinf hSinf C2 hC2 hgap hA hξ hpζ.pS hζs hs0 hε0.le hε
      (fun t => (hco s hs t).1) (fun t => (hco s hs t).2.1)
      (fun t => by
        rw [hresξ _ (mem_Ω hs0), norm_neg]
        exact ((pS A (s, t)).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hco s hs t).2.1 (norm_nonneg _)))
      (fun t => by
        rw [hpresξ _ (mem_Ω hs0), norm_neg, mul_add]
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · exact ((pS (pS A) (s, t)).le_opNorm _).trans
            (mul_le_mul_of_nonneg_right (hco s hs t).2.2 (norm_nonneg _))
        · exact ((pS A (s, t)).le_opNorm _).trans
            (mul_le_mul_of_nonneg_right (hco s hs t).2.1 (norm_nonneg _)))
    set H := Ip (pS ξ) (pS ξ) s
    have hH : 0 ≤ H := Ip_self_nonneg _ _
    have h1 : 3 * C2 * (H + ε ^ 2 * G s + ε ^ 2 * f s) ≤ 3 * K * (H + ε ^ 2 * G s + ε ^ 2 * f s) :=
      mul_le_mul_of_nonneg_right hCK (by have := hGnn s; have := hfnn s; positivity)
    have h2 : u * G s ≤ u * (3 * K * (H + ε ^ 2 * G s + ε ^ 2 * f s)) :=
      mul_le_mul_of_nonneg_left (L1.trans h1) hu0.le
    have h3 : u * (3 * K * (H + ε ^ 2 * G s + ε ^ 2 * f s)) = 3 * (H + ε ^ 2 * G s + ε ^ 2 * f s) := by
      rw [show u * (3 * K * (H + ε ^ 2 * G s + ε ^ 2 * f s)) =
        (K * u) * (3 * (H + ε ^ 2 * G s + ε ^ 2 * f s)) by ring, hKu, one_mul]
    have h4 : ε ^ 2 ≤ u / 10000 := by rw [hεd]; nlinarith
    have h5 : ε ^ 2 ≤ 1 := by nlinarith
    have hg : (∫ t in (0:ℝ)..1, Qd A ξ (s, t)) = g2 s / 2 := by simp only [g2]; ring
    have hG0 := hGnn s
    have hf0 := hfnn s
    have k1 : ε ^ 2 * G s ≤ u / 10000 * G s := mul_le_mul_of_nonneg_right h4 hG0
    have k2 : ε ^ 2 * f s ≤ f s := by nlinarith
    have k3 : ε * f s ≤ f s / 2 := by nlinarith
    have k4 : ε * G s = u * G s / 100 := by rw [hεd]; ring
    have k5 : 0 ≤ u * G s := mul_nonneg hu0.le hG0
    linarith
  -- convexity of `G + κ e^{-cs}`
  set κ := 2 * M0 / c ^ 2
  have hκ : 0 ≤ κ := by positivity
  set h : ℝ → ℝ := fun x => G x + κ * Real.exp (-(c * x))
  set h1 : ℝ → ℝ := fun x => g1 x + κ * (Real.exp (-(c * x)) * (-c))
  set h2 : ℝ → ℝ := fun x => g2 x + κ * (Real.exp (-(c * x)) * (-c) * (-c))
  have hexpd : ∀ x, HasDerivAt (fun x => Real.exp (-(c * x))) (Real.exp (-(c * x)) * (-c)) x := by
    intro x
    have := ((hasDerivAt_id x).const_mul c).neg.exp
    refine this.congr_deriv ?_
    simp only [id, mul_one, Pi.neg_apply]
  have hhd : ∀ s ≥ s1 + 1, HasDerivAt h (h1 s) s := fun s hs =>
    (hGd s (by linarith)).add ((hexpd s).const_mul κ)
  have hh1d : ∀ s ≥ s1 + 1, HasDerivAt h1 (h2 s) s := by
    intro s hs
    have := (hexpd s).mul_const (-c) |>.const_mul κ
    exact (hg1d s (by linarith)).add this
  have hh2 : ∀ s ≥ s1 + 1, 0 ≤ h2 s := by
    intro s hs
    have h1' := app2 s (by linarith)
    have h2' := hfM s (by linarith)
    have : κ * (Real.exp (-(c * s)) * (-c) * (-c)) = 2 * M0 * Real.exp (-(c * s)) := by
      simp only [κ]; field_simp
    simp only [h2]
    linarith
  have hhnn : ∀ s, 0 ≤ h s := fun s => add_nonneg (hGnn s) (mul_nonneg hκ (Real.exp_pos _).le)
  have hexpc : Continuous fun x => Real.exp (-(c * x)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id).neg
  have hIh : ∀ a ≥ s1 + 1, ∀ b ≥ a, ∫ x in a..b, h x ≤ (M1 + κ / c) * Real.exp (-(c * a)) := by
    intro a ha b hb
    have hGi : IntervalIntegrable G volume a b :=
      (hGc.mono (by rw [uIcc_of_le hb]; intro y hy; exact lt_of_lt_of_le hs1 (by linarith [hy.1])))
        |>.intervalIntegrable
    simp only [h]
    rw [intervalIntegral.integral_add hGi ((hexpc.intervalIntegrable a b).const_mul κ),
      intervalIntegral.integral_const_mul]
    have := hIG a ha b hb
    have := mul_le_mul_of_nonneg_left (int_exp_le hc hb) hκ
    have e : κ * (Real.exp (-(c * a)) / c) = κ / c * Real.exp (-(c * a)) := by ring
    have e' : (M1 + κ / c) * Real.exp (-(c * a)) = M1 * Real.exp (-(c * a)) + κ / c * Real.exp (-(c * a)) := by
      ring
    linarith
  have hanti := convex_bdd_anti h h1 h2 (s1 + 1) ((M1 + κ / c) * Real.exp (-(c * (s1 + 1))))
    hhd hh1d hh2 (fun s _ => hhnn s) (hIh (s1 + 1) le_rfl)
  -- pointwise bound on `G`
  set M2 := (M1 + κ / c) * Real.exp c
  refine ⟨s1 + 2, by linarith, c, hc, M0 + M2, fun s hs => ⟨?_, ?_⟩⟩
  · have := hfM s (by linarith)
    have : 0 ≤ M2 * Real.exp (-(c * s)) := by positivity
    have e : (M0 + M2) * Real.exp (-(c * s)) = M0 * Real.exp (-(c * s)) + M2 * Real.exp (-(c * s)) := by ring
    linarith
  · have hhs : h s ≤ ∫ x in (s - 1)..s, h x := by
      have hi : IntervalIntegrable h volume (s - 1) s := by
        refine ContinuousOn.intervalIntegrable ?_
        intro x hx
        rw [uIcc_of_le (by linarith)] at hx
        exact ((hhd x (by linarith [hx.1])).continuousAt).continuousWithinAt
      have := intervalIntegral.integral_mono_on (by linarith : s - 1 ≤ s) intervalIntegrable_const hi
        (fun x hx => hanti (show s1 + 1 ≤ x by linarith [hx.1]) (show s1 + 1 ≤ s by linarith) hx.2)
      simpa using this
    have hb := hIh (s - 1) (by linarith) s (by linarith)
    rw [exp_shift] at hb
    have hGh : G s ≤ h s := le_add_of_nonneg_right (mul_nonneg hκ (Real.exp_pos _).le)
    have : M2 * Real.exp (-(c * s)) = (M1 + κ / c) * (Real.exp (c * 1) * Real.exp (-(c * s))) := by
      simp only [M2, mul_one]; ring
    have : 0 ≤ M0 * Real.exp (-(c * s)) := by positivity
    have e : (M0 + M2) * Real.exp (-(c * s)) = M0 * Real.exp (-(c * s)) + M2 * Real.exp (-(c * s)) := by ring
    simp only [mul_one] at hb
    linarith

end HDecay

end HD_k

section HD_l

/-! Pointwise exponential decay: the gap estimate turns `L²` decay of `ζ`, `∂ₛζ` into sup decay. -/

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

namespace HDecay

variable {n : ℕ}

lemma int_norm_le_sqrt {v : ℝ × ℝ → Vec n} (hv : Sm v) {s : ℝ} (hs : 0 < s) :
    ∫ t in (0:ℝ)..1, ‖v (s, t)‖ ≤ Real.sqrt (Ip v v s) := by
  apply Real.le_sqrt_of_sq_le
  have := sq_integral_le (fun t => ‖v (s, t)‖) (cont_slice hv.cont hs).norm
  simp only [Ip, real_inner_self_eq_norm_sq]
  exact this

theorem sup_decay (S : ℝ × ℝ → Mat n) (hS : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × ℝ => S p i j))
    (hSper : ∀ s t : ℝ, S (s, t + 1) = S (s, t))
    (Sinf : ℝ → Mat n) (hSinf : IsSymLoop Sinf) (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (hSas : FiniteEnergyPlane.IsCInftyAsymptoticTo S Sinf) (hnd : IsNondegenerate Sinf)
    (ζ : ℝ × ℝ → Vec n) (hζ : FiniteEnergyPlane.IsHalfCylSolution S ζ)
    (hζ0 : FiniteEnergyPlane.TendstoZeroUnif ζ) :
    ∃ δ > 0, ∃ C : ℝ, ∀ s ≥ 1, ∀ t : ℝ, ‖ζ (s, t)‖ ≤ C * Real.exp (-(δ * s)) := by
  obtain ⟨s2, hs2, c, hc, M, hM⟩ := L2_decay S hS hSper Sinf hSinf hSinf' hSas hnd ζ hζ hζ0
  obtain ⟨C, hC0, hC⟩ := gap_sup Sinf hSinf hnd
  obtain ⟨s1, hs1, hco⟩ := coeff_small S hS Sinf hSinf' hSas 1 one_pos
  set A : ℝ × ℝ → Op n := fun p => TL n (S p)
  have hζs : Sm ζ := hζ.1
  have hpζ : TPer ζ := hζ.2.1
  set s3 := max s2 s1
  set δ := c / 2
  have hδ : 0 < δ := by positivity
  have hM0 : 0 ≤ M := by
    have h := (hM s2 le_rfl).1
    have := Ip_self_nonneg ζ s2
    by_contra hneg
    push Not at hneg
    have : M * Real.exp (-(c * s2)) < 0 := mul_neg_of_neg_of_pos hneg (Real.exp_pos _)
    linarith
  -- large `s`
  have hlarge : ∀ s ≥ s3, ∀ t, ‖ζ (s, t)‖ ≤ 2 * C * Real.sqrt M * Real.exp (-(δ * s)) := by
    intro s hs t
    have hs0 : 0 < s := lt_of_lt_of_le hs2 (le_trans (le_max_left _ _) hs)
    have hsq : ∀ v : ℝ × ℝ → Vec n, Sm v → Ip v v s ≤ M * Real.exp (-(c * s)) →
        ∫ t in (0:ℝ)..1, ‖v (s, t)‖ ≤ Real.sqrt M * Real.exp (-(δ * s)) := by
      intro v hv hb
      refine (int_norm_le_sqrt hv hs0).trans ?_
      have e : Real.exp (-(c * s)) = Real.exp (-(δ * s)) ^ 2 := by
        rw [← Real.exp_nat_mul]; congr 1; simp only [δ]; push_cast; ring
      rw [← Real.sqrt_sq (Real.exp_pos (-(δ * s))).le, ← Real.sqrt_mul hM0, ← e]
      exact Real.sqrt_le_sqrt hb
    have h1 := hsq ζ hζs (hM s (le_trans (le_max_left _ _) hs)).1
    have h2 := hsq (pS ζ) hζs.dS (hM s (le_trans (le_max_left _ _) hs)).2
    have hg := hC (fun τ => ζ (s, τ)) (fun τ => pT ζ (s, τ)) (fun τ => hζs.hasDerivAt_t hs0)
      (cont_slice hζs.dT.cont hs0) (hpζ.periodic s) t
    have hpt : ∀ τ, ‖-(Jop n (pT ζ (s, τ))) - TL n (Sinf τ) (ζ (s, τ))‖ ≤
        ‖pS ζ (s, τ)‖ + ‖ζ (s, τ)‖ := by
      intro τ
      have hres : res A ζ (s, τ) = 0 := hζ.2.2 s hs0 τ
      have e : -(Jop n (pT ζ (s, τ))) - TL n (Sinf τ) (ζ (s, τ)) =
          pS ζ (s, τ) + (A (s, τ) - TL n (Sinf τ)) (ζ (s, τ)) - res A ζ (s, τ) := by
        simp only [res, ContinuousLinearMap.sub_apply]; abel
      rw [e, hres, sub_zero]
      refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
      refine ((A (s, τ) - TL n (Sinf τ)).le_opNorm _).trans ?_
      have := (hco s (le_trans (le_max_right _ _) hs) τ).1
      nlinarith [norm_nonneg (ζ (s, τ))]
    have hint : ∫ τ in (0:ℝ)..1, ‖-(Jop n (pT ζ (s, τ))) - TL n (Sinf τ) (ζ (s, τ))‖ ≤
        (∫ τ in (0:ℝ)..1, ‖pS ζ (s, τ)‖) + ∫ τ in (0:ℝ)..1, ‖ζ (s, τ)‖ := by
      have c1 := (cont_slice hζs.dS.cont hs0).norm
      have c2 := (cont_slice hζs.cont hs0).norm
      rw [← intervalIntegral.integral_add (c1.intervalIntegrable _ _) (c2.intervalIntegrable _ _)]
      refine intervalIntegral.integral_mono_on zero_le_one ?_ ((c1.add c2).intervalIntegrable _ _)
        fun τ _ => hpt τ
      exact ((((Jop n).continuous.comp (cont_slice hζs.dT.cont hs0)).neg.sub
        (((TL n).continuous.comp hSinf.1).clm_apply (cont_slice hζs.cont hs0))).norm).intervalIntegrable _ _
    calc ‖ζ (s, t)‖ ≤ C * ((∫ τ in (0:ℝ)..1, ‖pS ζ (s, τ)‖) + ∫ τ in (0:ℝ)..1, ‖ζ (s, τ)‖) :=
          hg.trans (mul_le_mul_of_nonneg_left hint hC0)
      _ ≤ C * (Real.sqrt M * Real.exp (-(δ * s)) + Real.sqrt M * Real.exp (-(δ * s))) := by
          gcongr
      _ = 2 * C * Real.sqrt M * Real.exp (-(δ * s)) := by ring
  -- bounded part `[1, s3]`
  have hK : IsCompact (Icc (1:ℝ) s3 ×ˢ Icc (0:ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  have hKΩ : Icc (1:ℝ) s3 ×ˢ Icc (0:ℝ) 1 ⊆ Ω := fun x hx =>
    ⟨lt_of_lt_of_le one_pos hx.1.1, trivial⟩
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (hζs.cont.mono hKΩ)
  have hsmall : ∀ s ∈ Icc (1:ℝ) s3, ∀ t, ‖ζ (s, t)‖ ≤ B := by
    intro s hs t
    obtain ⟨y, hy, hyt⟩ := (hpζ.periodic s).exists_mem_Ico₀ zero_lt_one t
    rw [hyt]
    exact hB (s, y) ⟨hs, Ico_subset_Icc_self hy⟩
  refine ⟨δ, hδ, 2 * C * Real.sqrt M + |B| * Real.exp (δ * s3), fun s hs t => ?_⟩
  have hE : 0 ≤ Real.exp (-(δ * s)) := (Real.exp_pos _).le
  have hP1 : 0 ≤ 2 * C * Real.sqrt M * Real.exp (-(δ * s)) := by positivity
  have hP2 : 0 ≤ |B| * Real.exp (δ * s3) * Real.exp (-(δ * s)) := by positivity
  rw [add_mul]
  rcases le_total s s3 with h | h
  · have h1 := hsmall s ⟨hs, h⟩ t
    have h2 : B ≤ |B| * Real.exp (δ * s3) * Real.exp (-(δ * s)) := by
      rw [mul_assoc, ← Real.exp_add]
      have : 1 ≤ Real.exp (δ * s3 + -(δ * s)) := Real.one_le_exp (by nlinarith)
      nlinarith [le_abs_self B, abs_nonneg B]
    linarith
  · have := hlarge s h t
    linarith

end HDecay


end HD_l

open scoped ContDiff in
theorem solution {n : ℕ} (S : ℝ × ℝ → CauchyRiemannIndex.Mat n)
    (hS : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × ℝ => S p i j)) (hSper : ∀ s t : ℝ, S (s, t + 1) = S (s, t))
    (Sinf : ℝ → CauchyRiemannIndex.Mat n) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (hSas : FiniteEnergyPlane.IsCInftyAsymptoticTo S Sinf)
    (hnd : CauchyRiemannIndex.IsNondegenerate Sinf)
    (ζ : ℝ × ℝ → CauchyRiemannIndex.Vec n) (hζ : FiniteEnergyPlane.IsHalfCylSolution S ζ)
    (hζ0 : FiniteEnergyPlane.TendstoZeroUnif ζ) :
    ∃ δ > 0, ∃ C : ℝ, ∀ s ≥ 1, ∀ t : ℝ, ‖ζ (s, t)‖ ≤ C * Real.exp (-(δ * s)) :=
  HDecay.sup_decay S hS hSper Sinf hSinf hSinf' hSas hnd ζ hζ hζ0
