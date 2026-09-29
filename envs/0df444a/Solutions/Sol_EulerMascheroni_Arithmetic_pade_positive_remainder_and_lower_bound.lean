-- Prove2me | solution 1 for EulerMascheroni.Arithmetic.pade_positive_remainder_and_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T21:17:42.08686+00:00
-- url     : https://prove2.me/submissions/c26505ea-9a10-4d99-9f3f-2074e9a0d9a8

import Definitions.Def_eulerMascheroni_padeTransform
set_option autoImplicit false
set_option maxHeartbeats 1800000
open MeasureTheory Set Filter EulerMascheroni.Arithmetic
open scoped Topology
namespace PadeRemainder
noncomputable def kernel (n : ℕ) (s : ℝ) : ℝ := (s/(1+s))^n * Real.exp (-s)/(1+s)

lemma kernel_nonneg (n : ℕ) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ kernel n s := by
  unfold kernel
  positivity
lemma kernel_bound (n : ℕ) {s : ℝ} (hs : 0 ≤ s) : kernel n s ≤ Real.exp (-s) := by
  have ha : 0 ≤ s/(1+s) := by positivity
  have hb : s/(1+s) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  have hp : (s/(1+s))^n ≤ 1 := pow_le_one₀ ha hb
  unfold kernel
  calc
    _ ≤ (s/(1+s))^n * Real.exp (-s) := div_le_self (by positivity) (by linarith)
    _ ≤ 1 * Real.exp (-s) := mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = _ := one_mul _
lemma kernel_integrable (n : ℕ) : IntegrableOn (kernel n) (Ioi 0) := by
  have hexp : IntegrableOn (fun s : ℝ => Real.exp (-s)) (Ioi 0) := by
    simpa using exp_neg_integrableOn_Ioi (0:ℝ) (by norm_num : (0:ℝ) < 1)
  refine Integrable.mono' hexp ?_ ?_
  · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    intro s hs
    have hn : 1+s ≠ 0 := by have := hs; simp only [mem_Ioi] at this; linarith
    exact (show ContinuousAt (kernel n) s by unfold kernel; fun_prop).continuousWithinAt
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (kernel_nonneg n (le_of_lt hs))]
    exact kernel_bound n (le_of_lt hs)
lemma kernel_tendsto (n : ℕ) : Tendsto (kernel n) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ Real.tendsto_exp_neg_atTop_nhds_zero
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with s hs
    exact kernel_nonneg n hs
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with s hs
    exact kernel_bound n hs

lemma kernel_derivative_succ (n : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    HasDerivAt (kernel (n+1))
      (((n:ℝ)+2)*kernel (n+2) s - 2*((n:ℝ)+2)*kernel (n+1) s + ((n:ℝ)+1)*kernel n s) s := by
  have hn : 1+s ≠ 0 := by linarith
  have hd := ((((hasDerivAt_id s).div ((hasDerivAt_id s).const_add 1) hn).pow (n+1)).mul
    ((hasDerivAt_id s).neg.exp)).div ((hasDerivAt_id s).const_add 1) hn
  convert! hd using 1
  dsimp only [kernel, Pi.div_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, id_eq]
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, one_mul, mul_one, pow_succ]
  field_simp
  ring
lemma kernel_derivative_zero (s : ℝ) (hs : 0 ≤ s) :
    HasDerivAt (kernel 0) (kernel 1 s - 2*kernel 0 s) s := by
  have hn : 1+s ≠ 0 := by linarith
  have hd := ((hasDerivAt_id s).neg.exp).div ((hasDerivAt_id s).const_add 1) hn
  convert! hd using 1
  · ext x; simp [kernel]
  · dsimp only [Pi.div_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, id_eq]
    simp only [kernel, pow_zero, pow_one, one_mul, mul_one]
    field_simp
    ring

lemma integral_recurrence (n : ℕ) :
    ((n:ℝ)+2)*(∫ s in Ioi 0, kernel (n+2) s) =
      2*((n:ℝ)+2)*(∫ s in Ioi 0, kernel (n+1) s) -
        ((n:ℝ)+1)*(∫ s in Ioi 0, kernel n s) := by
  have hi := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun s hs => kernel_derivative_succ n s hs)
    ((((kernel_integrable (n+2)).const_mul ((n:ℝ)+2)).sub
      ((kernel_integrable (n+1)).const_mul (2*((n:ℝ)+2)))).add
      ((kernel_integrable n).const_mul ((n:ℝ)+1))) (kernel_tendsto (n+1))
  rw [integral_add, integral_sub, integral_const_mul, integral_const_mul, integral_const_mul] at hi
  · have hk : kernel (n+1) 0 = 0 := by simp [kernel]
    rw [hk, sub_zero] at hi
    linear_combination hi
  · exact (kernel_integrable (n+2)).const_mul _
  · exact (kernel_integrable (n+1)).const_mul _
  · exact ((kernel_integrable (n+2)).const_mul _).sub ((kernel_integrable (n+1)).const_mul _)
  · exact (kernel_integrable n).const_mul _

lemma integral_initial :
    (∫ s in Ioi 0, kernel 0 s) = EulerMascheroni.gompertzConstant ∧
    (∫ s in Ioi 0, kernel 1 s) = 2*EulerMascheroni.gompertzConstant-1 := by
  have h0 : (∫ s in Ioi 0, kernel 0 s) = EulerMascheroni.gompertzConstant := by
    simp [kernel, EulerMascheroni.gompertzConstant]
  refine ⟨h0, ?_⟩
  have hi := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun s hs => kernel_derivative_zero s hs)
    ((kernel_integrable 1).sub ((kernel_integrable 0).const_mul 2)) (kernel_tendsto 0)
  rw [integral_sub (kernel_integrable 1) ((kernel_integrable 0).const_mul 2),
    integral_const_mul, h0] at hi
  have hk : kernel 0 0 = 1 := by simp [kernel]
  rw [hk] at hi
  linear_combination hi

lemma remainder_identity (n : ℕ) :
    (padeQ n:ℝ)*EulerMascheroni.gompertzConstant-(padeP n:ℝ) =
      (n.factorial:ℝ)*(∫ s in Ioi 0, kernel n s) := by
  induction n using Nat.twoStepInduction with
  | zero => simpa [padeQ,padeP,padeSeq] using integral_initial.1.symm
  | one => simpa [padeQ,padeP,padeSeq] using integral_initial.2.symm
  | more n ih ih' =>
    have hh := integral_recurrence n
    have hP : padeP (n+2) = (2*(n:ℤ)+4)*padeP (n+1)-((n:ℤ)+1)^2*padeP n := rfl
    have hQ : padeQ (n+2) = (2*(n:ℤ)+4)*padeQ (n+1)-((n:ℤ)+1)^2*padeQ n := rfl
    rw [hP,hQ]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Int.cast_sub, Int.cast_mul, Int.cast_add, Int.cast_pow, Int.cast_ofNat, Int.cast_natCast] at ih' ⊢
    linear_combination (2*(n:ℝ)+4)*ih' - ((n:ℝ)+1)^2*ih -
      ((n:ℝ)+1)*(n.factorial:ℝ)*hh
lemma remainder_positive (n : ℕ) :
    0 < (padeQ n:ℝ)*EulerMascheroni.gompertzConstant-(padeP n:ℝ) := by
  rw [remainder_identity]
  apply mul_pos (by positivity)
  rw [setIntegral_pos_iff_support_of_nonneg_ae]
  · have hh : (Function.support (kernel n)) ∩ Ioi 0 = Ioi 0 := by
      ext s
      simp only [mem_inter_iff, Function.mem_support, mem_Ioi, and_iff_right_iff_imp]
      intro hs
      unfold kernel
      positivity
    rw [hh]
    simp
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    exact kernel_nonneg n (le_of_lt hs)
  · exact kernel_integrable n

lemma integral_window_lower (n : ℕ) (K : ℝ) (hK : 0 < K) :
    (K/(K+1))^n * Real.exp (-(K+1))/(K+2) ≤ ∫ s in Ioi 0, kernel n s := by
  let c : ℝ := (K/(K+1))^n * Real.exp (-(K+1))/(K+2)
  have hsub : Icc K (K+1) ⊆ Ioi 0 := fun s hs => lt_of_lt_of_le hK hs.1
  have hmono : ∀ s ∈ Icc K (K+1), c ≤ kernel n s := by
    intro s hs
    have hs0 : 0 ≤ s := le_trans hK.le hs.1
    have ha : K/(K+1) ≤ s/(1+s) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith [hs.1]
    have hp := pow_le_pow_left₀ (show 0 ≤ K/(K+1) by positivity) ha n
    have he : Real.exp (-(K+1)) ≤ Real.exp (-s) := Real.exp_le_exp.mpr (by linarith [hs.2])
    dsimp [c]
    unfold kernel
    calc
      _ ≤ (s/(1+s))^n * Real.exp (-s)/(K+2) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul hp he (Real.exp_pos _).le (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith [hs.2])
  have hconst : IntegrableOn (fun _ : ℝ => c) (Icc K (K+1)) := integrableOn_const (hs := by simp)
  have hwin := setIntegral_mono_on hconst ((kernel_integrable n).mono_set hsub) measurableSet_Icc hmono
  have hc : (∫ s in Icc K (K+1), c) = c := by simp [setIntegral_const]
  rw [hc] at hwin
  refine hwin.trans (setIntegral_mono_set (kernel_integrable n) ?_ (ae_of_all _ hsub))
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
  exact kernel_nonneg n (le_of_lt hs)

lemma remainder_rational_lower (n K : ℕ) (hK : 0 < K) :
    (n.factorial:ℝ)*(K:ℝ)^n / (((K:ℝ)+1)^n * 3^(K+1) * ((K:ℝ)+2)) ≤
      (padeQ n:ℝ)*EulerMascheroni.gompertzConstant-(padeP n:ℝ) := by
  have hKr : 0 < (K:ℝ) := by exact_mod_cast hK
  have he : (1:ℝ)/3^(K+1) ≤ Real.exp (-((K:ℝ)+1)) := by
    rw [Real.exp_neg, one_div]
    apply inv_anti₀ (Real.exp_pos _)
    have hp := pow_le_pow_left₀ (Real.exp_pos (1:ℝ)).le Real.exp_one_lt_three.le (K+1)
    simpa only [← Real.exp_nat_mul, mul_one, Nat.cast_add, Nat.cast_one] using hp
  rw [remainder_identity]
  apply le_trans _ (mul_le_mul_of_nonneg_left (integral_window_lower n K hKr) (by positivity))
  have hp : (K:ℝ)+1 ≠ 0 := by positivity
  have hmul := mul_le_mul_of_nonneg_left he (show 0 ≤ (n.factorial:ℝ)*((K:ℝ)/((K:ℝ)+1))^n/((K:ℝ)+2) by positivity)
  convert hmul using 1 <;> push_cast <;> simp only [div_pow] <;> field_simp <;> ring
end PadeRemainder


theorem solution (n : ℕ) :
    ((padeQ n:ℝ)*EulerMascheroni.gompertzConstant-(padeP n:ℝ) =
      (n.factorial:ℝ)*(∫ s in Ioi (0:ℝ), (s/(1+s))^n * Real.exp (-s)/(1+s))) ∧
    0 < (padeQ n:ℝ)*EulerMascheroni.gompertzConstant-(padeP n:ℝ) ∧
    ∀ K : ℕ, 0 < K →
      (n.factorial:ℝ)*(K:ℝ)^n / (((K:ℝ)+1)^n * 3^(K+1) * ((K:ℝ)+2)) ≤
        (padeQ n:ℝ)*EulerMascheroni.gompertzConstant-(padeP n:ℝ) := by
  exact ⟨PadeRemainder.remainder_identity n, PadeRemainder.remainder_positive n,
    fun K hK => PadeRemainder.remainder_rational_lower n K hK⟩
#print axioms solution
