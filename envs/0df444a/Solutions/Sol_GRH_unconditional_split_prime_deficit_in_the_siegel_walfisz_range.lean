-- Prove2me | solution 1 for GRH.unconditional_split_prime_deficit_in_the_siegel_walfisz_range
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T02:23:42.139634+00:00
-- url     : https://prove2.me/submissions/6e7759a6-0c3d-4853-8530-2b67ec276839

import Theorems.Thm_GRH_prime_power_excess_in_a_progression_is_uniformly_square_root
import Theorems.Thm_SWPort_Davenport_siegel_walfisz_ap
import Mathlib.Tactic.Linarith

open Finset Filter ArithmeticFunction GRH.SplitPrimeLower GRH.PrimeDeficitMean

private theorem before_le (q n : ℕ) : SWPort.Davenport.psiAP n q 1 ≤ mangoldtWeight q n := by
  classical
  have h (i : ℕ) : (if (i:ZMod q)=((1:ℕ):ZMod q) then (vonMangoldt i:ℝ) else 0) =
      vonMangoldt.residueClass (1:ZMod q) i := by
    simp [vonMangoldt.residueClass,Set.indicator_apply]
  unfold SWPort.Davenport.psiAP mangoldtWeight
  simp_rw [h]
  calc
    _ ≤ ∑ i ∈ range (n+1), vonMangoldt.residueClass (1:ZMod q) i := by
      rw [sum_range_succ]; linarith [vonMangoldt.residueClass_nonneg (1:ZMod q) n]
    _ = _ := by
      rw [show range (n+1) = Icc 0 n from by ext i;simp,
        show Icc 1 n = Ioc 0 n from Icc_succ_left_eq_Ioc 0 n,← add_sum_Ioc_eq_sum_Icc (Nat.zero_le n)]
      simp

private theorem sw (A : ℝ) (hA : 0<A) :
    ∃ c C K : ℝ, 0<c ∧ 0<C ∧ 0≤K ∧ ∀ (q n : ℕ), 0<q → 2≤n →
      (q:ℝ) ≤ (Real.log n)^A →
      (n:ℝ) - (q.totient:ℝ)*primeWeight q n ≤
        (q.totient:ℝ)*(C*(n:ℝ)*Real.exp (-c*Real.sqrt (Real.log n)) + K*Real.sqrt n) := by
  obtain ⟨c,C,hc,hC,hw⟩ := SWPort.Davenport.siegel_walfisz_ap A hA
  obtain ⟨K,hK,hcomp⟩ := GRH.prime_power_excess_in_a_progression_is_uniformly_square_root
  refine ⟨c,C,K,hc,hC,hK,?_⟩
  intro q n hq hn hr
  have h := (abs_le.mp (hw n q 1 hn hq hr (by simp))).1
  have ht : 0 < (q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have he : (n:ℝ)/(q.totient:ℝ) - primeWeight q n ≤
      C*(n:ℝ)*Real.exp (-c*Real.sqrt (Real.log n)) + K*Real.sqrt n := by
    linarith only [h,(hcomp q n).2,before_le q n]
  have := mul_le_mul_of_nonneg_left he ht.le
  rwa [mul_sub,mul_div_cancel₀ _ ht.ne'] at this

private noncomputable def logKernel (n : ℕ) : ℝ := 1 / ((n:ℝ)*(1+Real.log n)^2)

private theorem logKernel_summable : Summable logKernel := by
  apply (summable_condensed_iff_of_nonneg (fun n => by unfold logKernel;positivity) ?_).mp
  · have hs : Summable (fun n : ℕ => (((n+1:ℕ):ℝ)^2)⁻¹) :=
      (summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr (by norm_num))
    let L := Real.log 2
    have hL : 0<L := Real.log_pos (by norm_num)
    have hL1 : L≤1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
      dsimp [L];linarith
    refine Summable.of_nonneg_of_le (f:=fun n : ℕ => (L^2)⁻¹ * (((n+1:ℕ):ℝ)^2)⁻¹)
      (fun n => by unfold logKernel;positivity) ?_ (hs.mul_left _)
    intro n
    unfold logKernel
    simp only [Nat.cast_pow,Nat.cast_ofNat,Real.log_pow,Nat.cast_succ]
    change (2:ℝ)^n * (1 / (2^n*(1+n*L)^2)) ≤ _
    have e : (2:ℝ)^n * (1 / (2^n*(1+n*L)^2)) = ((1+n*L)^2)⁻¹ := by field_simp
    rw [e,← mul_inv,← mul_pow]
    apply inv_anti₀ (by positivity)
    apply pow_le_pow_left₀ (by positivity)
    nlinarith only [hL1]
  · intro m n hm hmn
    have hm1 : 1≤(m:ℝ) := by exact_mod_cast hm
    have hab : (m:ℝ)≤(n:ℝ) := by exact_mod_cast hmn
    have hp : 0<(m:ℝ) := by linarith
    have hlog := Real.log_nonneg hm1
    unfold logKernel
    apply one_div_le_one_div_of_le (by positivity)
    exact mul_le_mul hab (pow_le_pow_left₀ (by linarith) (by linarith [Real.log_le_log hp hab]) 2)
      (sq_nonneg _) (hp.le.trans hab)

private theorem exp_decay {c t : ℝ} (hc : 0<c) (ht : 1≤t) :
    Real.exp (-c*Real.sqrt (2*t)) ≤ (24/c^4)/(1+t)^2 := by
  let y := Real.sqrt (2*t)
  have hy := Real.sq_sqrt (by linarith : 0 ≤ 2*t)
  change y^2 = 2*t at hy
  have hp : 0≤y := Real.sqrt_nonneg _
  have hl := Real.pow_div_factorial_le_exp (c*y) (mul_nonneg hc.le hp) 4
  norm_num at hl
  have hscale : (1+t)^2 ≤ y^4 := by
    calc
      _ ≤ (2*t)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
      _ = y^4 := by rw [← hy];ring
  have he : 0 < Real.exp (c*y) := Real.exp_pos _
  change Real.exp (-c*y) ≤ _
  rw [neg_mul,Real.exp_neg]
  apply (le_div_iff₀ (sq_pos_of_pos (by linarith : 0<1+t))).mpr
  apply (le_div_iff₀ (pow_pos hc 4)).mpr
  rw [show (Real.exp (c*y))⁻¹ * (1+t)^2 * c^4 =
    (c^4*(1+t)^2)/Real.exp (c*y) by ring]
  apply (div_le_iff₀ he).mpr
  calc
    _ ≤ c^4*y^4 := mul_le_mul_of_nonneg_left hscale (by positivity)
    _ ≤ _ := by rw [← mul_pow];linarith

private theorem exponent_one (q : ℕ) [NeZero q] : squareMean q 1 := by
  obtain ⟨c,C,K,hc,hC,hK,hw⟩ := sw 1 (by norm_num)
  let u := fun n : ℕ => ((n+1:ℕ):ℝ)
  have hp (n : ℕ) : 0<u n := by dsimp [u];positivity
  have hlim : Tendsto u atTop atTop := tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hlog : Tendsto (fun n : ℕ => Real.log (u n)) atTop atTop := Real.tendsto_log_atTop.comp hlim
  have hs1 : Summable (fun n : ℕ => logKernel (n+1)) := (summable_nat_add_iff 1).mpr logKernel_summable
  have hs2 : Summable (fun n : ℕ => ((u n)^2)⁻¹) :=
    (summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr (by norm_num))
  let B := C*(24/c^4)
  have hs := ((hs1.mul_left B).add (hs2.mul_left K)).mul_left (q.totient:ℝ)
  refine hs.of_norm_bounded_eventually_nat ?_
  filter_upwards [hlog.eventually_ge_atTop (max (q:ℝ) 1),eventually_ge_atTop 1] with n hn hn1
  have hu := hp n
  have ht : 1 ≤ Real.log (u n) := (le_max_right ..).trans hn
  have hq : (q:ℝ) ≤ Real.log (u n) := (le_max_left ..).trans hn
  let m := (n+1)^2
  have hm : (m:ℝ) = (u n)^2 := by dsimp only [m,u];norm_cast
  have hm2 : 2 ≤ m := by dsimp [m];nlinarith
  have hz := hw q m (NeZero.pos q) hm2 (by rw [Real.rpow_one,hm,Real.log_pow];norm_num;linarith)
  rw [hm,Real.log_pow,Real.sqrt_sq hu.le] at hz
  norm_num only [Nat.cast_ofNat] at hz
  have hδ : deficit q ((u n)^2) ≤ (q.totient:ℝ)*(C*(u n)^2*((24/c^4)/(1+Real.log (u n))^2)+K*u n) := by
    unfold deficit
    rw [← hm,Nat.floor_natCast,hm]
    refine max_le (hz.trans ?_) (by positivity)
    have hh := mul_le_mul_of_nonneg_left (exp_decay hc ht) (mul_nonneg hC.le (sq_nonneg (u n)))
    exact mul_le_mul_of_nonneg_left (add_le_add hh (le_refl (K*u n))) (Nat.cast_nonneg (α:=ℝ) q.totient)
  have hpow : (u n)^(-2*(1:ℝ)-1) = ((u n)^3)⁻¹ := by
    rw [show -2*(1:ℝ)-1 = -(3:ℝ) by norm_num,Real.rpow_neg hu.le,Real.rpow_ofNat]
  change ‖deficit q ((u n)^2) * (u n)^(-2*(1:ℝ)-1)‖ ≤
    (q.totient:ℝ)*(B*logKernel (n+1)+K*((u n)^2)⁻¹)
  rw [hpow,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (le_max_right ..) (by positivity))]
  apply (mul_le_mul_of_nonneg_right hδ (inv_nonneg.mpr (pow_nonneg hu.le 3))).trans_eq
  change _ = (q.totient:ℝ)*(B*(1/(u n*(1+Real.log (u n))^2))+K*((u n)^2)⁻¹)
  dsimp only [B]
  have hlog0 : 1+Real.log (u n) ≠ 0 := by linarith
  field_simp

theorem solution :
    (∀ A : ℝ, 0<A → ∃ c C K : ℝ, 0<c ∧ 0<C ∧ 0≤K ∧ ∀ (q n : ℕ), 0<q → 2≤n →
      (q:ℝ) ≤ (Real.log n)^A →
      (n:ℝ) - (q.totient:ℝ)*primeWeight q n ≤
        (q.totient:ℝ)*(C*(n:ℝ)*Real.exp (-c*Real.sqrt (Real.log n)) + K*Real.sqrt n)) ∧
    ∀ q : ℕ, [NeZero q] → squareMean q 1 := by
  exact ⟨sw,fun q _ => exponent_one q⟩
