-- Prove2me | solution 1 for Formalism.ZF.localZeroExpansionOfFactorization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:41:57.795175+00:00
-- url     : https://prove2.me/submissions/ed1c9598-eaa2-4c95-8b76-db07516bee3c

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_LandauLocalOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex Filter Topology Metric
noncomputable section
namespace Formalism.ZF
private theorem hasDerivAt_sub_pow_of_sub_ne_zero (a z : ℂ) (n : ℕ) (h : z - a ≠ 0) :
    HasDerivAt (fun w => (w - a) ^ n) ((z - a) ^ n * ((n : ℂ) / (z - a))) z := by
  have h1 : HasDerivAt (fun w : ℂ => w - a) 1 z := by
    simpa using (hasDerivAt_id z).sub_const a
  have h2 : HasDerivAt (fun w : ℂ => (w - a) ^ n) ((n : ℂ) * (z - a) ^ (n - 1) * 1) z :=
    (hasDerivAt_pow n (z - a)).comp z h1
  refine h2.congr_deriv ?_
  rcases n with _ | k
  · simp
  · rw [pow_succ, Nat.add_sub_cancel]
    have hinv : (z - a) * (z - a)⁻¹ = 1 := mul_inv_cancel₀ h
    linear_combination (-((z - a) ^ k * ((k + 1 : ℕ) : ℂ))) * hinv
private theorem hasDerivAt_prod_sub_pow (Z : Finset ℂ) (m : ℂ → ℕ) (z : ℂ)
    (hz : ∀ ρ ∈ Z, z - ρ ≠ 0) :
    HasDerivAt (fun w => ∏ ρ ∈ Z, (w - ρ) ^ m ρ)
      ((∏ ρ ∈ Z, (z - ρ) ^ m ρ) * ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ)) z := by
  classical
  revert hz
  induction Z using Finset.induction_on with
  | empty =>
    intro _
    simp only [Finset.prod_empty, Finset.sum_empty, mul_zero]
    exact hasDerivAt_const z (1 : ℂ)
  | insert =>
    rename_i a s ha ih
    intro hz
    have hs : ∀ ρ ∈ s, z - ρ ≠ 0 := fun ρ hρ => hz ρ (Finset.mem_insert_of_mem hρ)
    have hza : z - a ≠ 0 := hz a (Finset.mem_insert_self a s)
    have hd := (hasDerivAt_sub_pow_of_sub_ne_zero a z (m a) hza).mul (ih hs)
    beta_reduce at hd
    simp only [Finset.prod_insert ha, Finset.sum_insert ha]
    refine hd.congr_deriv ?_
    ring
private theorem pow_le_pow_left_of_nonneg_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (n : ℕ) : a ^ n ≤ b ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact mul_le_mul ih hab ha (le_trans (pow_nonneg ha k) ih)
private theorem norm_prod_sub_pow (Z : Finset ℂ) (m : ℂ → ℕ) (w : ℂ) :
    ‖∏ ρ ∈ Z, (w - ρ) ^ m ρ‖ = ∏ ρ ∈ Z, ‖w - ρ‖ ^ m ρ := by
  simp only [norm_prod, norm_pow]
private theorem div_add_div_sub_eq_div (P S H D : ℂ) (hP : P ≠ 0) (hH : H ≠ 0) :
    (P * S * H + P * D) / (P * H) - S = D / H := by
  rw [sub_eq_iff_eq_add, div_eq_iff (mul_ne_zero hP hH)]
  have hHH : H⁻¹ * H = 1 := inv_mul_cancel₀ hH
  linear_combination (-(P * D)) * hHH
end Formalism.ZF
end
end

set_option autoImplicit false
open Complex Filter Topology Metric
noncomputable section
open Formalism Formalism.ZF
namespace Formalism.ZF
theorem _root_.solution : LandauLocalOf := by
  unfold LandauLocalOf LandauLocal
  intro hfac hlog f z₀ r M hr hM hf hf0 hbound
  classical
  have hr3 : 0 < r / 3 := by positivity
  obtain ⟨Z, m, h, hZ, hm, hh, hh0, hfeq⟩ := hfac f z₀ r (r / 3) hr3 (by linarith) hf hf0
  have hZball : ∀ ρ ∈ Z, ‖ρ - z₀‖ ≤ r / 3 := fun ρ hρ => by
    have := ((hZ ρ).1 hρ).1
    rwa [Metric.mem_closedBall, dist_eq_norm] at this
  have hZzero : ∀ ρ ∈ Z, f ρ = 0 := fun ρ hρ => ((hZ ρ).1 hρ).2
  have hz₀mem : z₀ ∈ Metric.closedBall z₀ r := Metric.mem_closedBall_self hr.le
  have hfz₀ := hfeq z₀ hz₀mem
  have hhz₀ : h z₀ ≠ 0 := by
    intro h0; apply hf0; rw [hfz₀, h0, mul_zero]
  have hPz₀le : ‖∏ ρ ∈ Z, (z₀ - ρ) ^ m ρ‖ ≤ (r / 3) ^ (∑ ρ ∈ Z, m ρ) := by
    rw [norm_prod_sub_pow, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod (fun ρ _ => pow_nonneg (norm_nonneg _) _) ?_
    intro ρ hρ
    have h1 : ‖z₀ - ρ‖ ≤ r / 3 := by rw [norm_sub_rev]; exact hZball ρ hρ
    exact pow_le_pow_left_of_nonneg_le (norm_nonneg _) h1 _
  have hPw : ∀ w : ℂ, ‖w - z₀‖ = r →
      (2 * r / 3) ^ (∑ ρ ∈ Z, m ρ) ≤ ‖∏ ρ ∈ Z, (w - ρ) ^ m ρ‖ := by
    intro w hw
    rw [norm_prod_sub_pow, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod (fun ρ _ => pow_nonneg (by linarith) _) ?_
    intro ρ hρ
    have h2 := hZball ρ hρ
    have h3 : ‖w - z₀‖ ≤ ‖w - ρ‖ + ‖ρ - z₀‖ := by
      have := norm_add_le (w - ρ) (ρ - z₀)
      rwa [sub_add_sub_cancel] at this
    have h1 : 2 * r / 3 ≤ ‖w - ρ‖ := by linarith
    exact pow_le_pow_left_of_nonneg_le (by linarith) h1 _
  have key_sphere : ∀ w : ℂ, ‖w - z₀‖ = r →
      (2 : ℝ) ^ (∑ ρ ∈ Z, m ρ) * ‖h w‖ ≤ M * ‖h z₀‖ := by
    intro w hw
    have hwmem : w ∈ Metric.closedBall z₀ r :=
      Metric.mem_closedBall.mpr (by rw [dist_eq_norm]; exact hw.le)
    have e1 := hbound w hwmem
    rw [hfeq w hwmem, hfz₀, norm_mul, norm_mul] at e1
    have e2 := hPw w hw
    have hq : 0 < (r / 3) ^ (∑ ρ ∈ Z, m ρ) := by positivity
    have e3 : (2 * r / 3) ^ (∑ ρ ∈ Z, m ρ) = (2 : ℝ) ^ (∑ ρ ∈ Z, m ρ) * (r / 3) ^ (∑ ρ ∈ Z, m ρ) := by
      rw [mul_div_assoc, mul_pow]
    have e4 : (r / 3) ^ (∑ ρ ∈ Z, m ρ) * ((2 : ℝ) ^ (∑ ρ ∈ Z, m ρ) * ‖h w‖)
        ≤ (r / 3) ^ (∑ ρ ∈ Z, m ρ) * (M * ‖h z₀‖) := by
      calc (r / 3) ^ (∑ ρ ∈ Z, m ρ) * ((2 : ℝ) ^ (∑ ρ ∈ Z, m ρ) * ‖h w‖)
          = (2 * r / 3) ^ (∑ ρ ∈ Z, m ρ) * ‖h w‖ := by rw [e3]; ring
        _ ≤ ‖∏ ρ ∈ Z, (w - ρ) ^ m ρ‖ * ‖h w‖ := mul_le_mul_of_nonneg_right e2 (norm_nonneg _)
        _ ≤ M * (‖∏ ρ ∈ Z, (z₀ - ρ) ^ m ρ‖ * ‖h z₀‖) := e1
        _ ≤ M * ((r / 3) ^ (∑ ρ ∈ Z, m ρ) * ‖h z₀‖) := by
            refine mul_le_mul_of_nonneg_left ?_ (by linarith)
            exact mul_le_mul_of_nonneg_right hPz₀le (norm_nonneg _)
        _ = (r / 3) ^ (∑ ρ ∈ Z, m ρ) * (M * ‖h z₀‖) := by ring
    exact le_of_mul_le_mul_left e4 hq
  have hdc : DiffContOnCl ℂ h (Metric.ball z₀ r) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball z₀ hr.ne']
    exact hh
  have hmax : ∀ z ∈ Metric.closedBall z₀ r,
      ‖h z‖ ≤ M * ‖h z₀‖ / (2 : ℝ) ^ (∑ ρ ∈ Z, m ρ) := by
    intro z hz
    have hz' : z ∈ closure (Metric.ball z₀ r) := by rwa [closure_ball z₀ hr.ne']
    refine Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hdc ?_ hz'
    intro w hw
    rw [frontier_ball z₀ hr.ne', mem_sphere_iff_norm] at hw
    rw [le_div_iff₀ (by positivity), mul_comm (‖h w‖)]
    exact key_sphere w hw
  have h2N : (2 : ℝ) ^ (∑ ρ ∈ Z, m ρ) ≤ M := by
    have := hmax z₀ hz₀mem
    have hpos : 0 < ‖h z₀‖ := norm_pos_iff.mpr hhz₀
    rw [le_div_iff₀ (by positivity), mul_comm M] at this
    exact le_of_mul_le_mul_left this hpos
  have hsum : ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) ≤ Real.log M / Real.log 2 := by
    rw [le_div_iff₀ (Real.log_pos one_lt_two), ← Real.log_pow]
    exact Real.log_le_log (by positivity) h2N
  have h2N1 : (1 : ℝ) ≤ (2 : ℝ) ^ (∑ ρ ∈ Z, m ρ) := by
    simpa using pow_le_pow_left_of_nonneg_le (a := 1) (b := 2) zero_le_one one_le_two (∑ ρ ∈ Z, m ρ)
  have hhb : ∀ z ∈ Metric.closedBall z₀ (r / 3), ‖h z‖ ≤ M * ‖h z₀‖ := by
    intro z hz
    have hz' : z ∈ Metric.closedBall z₀ r := Metric.closedBall_subset_closedBall (by linarith) hz
    have h1 := hmax z hz'
    have h2 : M * ‖h z₀‖ / (2 : ℝ) ^ (∑ ρ ∈ Z, m ρ) ≤ M * ‖h z₀‖ :=
      div_le_self (mul_nonneg (by linarith) (norm_nonneg _)) h2N1
    linarith
  have hlogb := hlog h z₀ (r / 3) M hr3 hM
    (hh.mono (Metric.closedBall_subset_closedBall (by linarith))) hh0 hhb
  refine ⟨Z, m, hZ, hm, hsum, ?_⟩
  intro z hz hfz
  have hzr : z ∈ Metric.ball z₀ r := by
    rw [Metric.mem_closedBall] at hz; rw [Metric.mem_ball]; linarith
  have hnhds : Metric.closedBall z₀ r ∈ 𝓝 z :=
    Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hzr) Metric.ball_subset_closedBall
  have hev : f =ᶠ[𝓝 z] fun w => (∏ ρ ∈ Z, (w - ρ) ^ m ρ) * h w :=
    Filter.mem_of_superset hnhds (fun w hw => hfeq w hw)
  have hfeqz := hfeq z (Metric.ball_subset_closedBall hzr)
  have hPz : (∏ ρ ∈ Z, (z - ρ) ^ m ρ) ≠ 0 := by
    intro h0; apply hfz; rw [hfeqz, h0, zero_mul]
  have hhz : h z ≠ 0 := by
    intro h0; apply hfz; rw [hfeqz, h0, mul_zero]
  have hzρ : ∀ ρ ∈ Z, z - ρ ≠ 0 := by
    intro ρ hρ h0; apply hfz; rw [sub_eq_zero.mp h0]; exact hZzero ρ hρ
  have hPd := hasDerivAt_prod_sub_pow Z m z hzρ
  have hhd : HasDerivAt h (deriv h z) z := (hh.differentiableAt hnhds).hasDerivAt
  have hd := (hPd.mul hhd).congr_of_eventuallyEq hev
  have hsplit : deriv f z / f z - ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ) = deriv h z / h z := by
    rw [hd.deriv, hfeqz]
    exact div_add_div_sub_eq_div _ _ _ _ hPz hhz
  rw [hsplit]
  have hz6 : z ∈ Metric.closedBall z₀ (r / 3 / 2) := by
    rw [Metric.mem_closedBall] at hz ⊢; linarith
  calc ‖deriv h z / h z‖ ≤ 24 * Real.log M / (r / 3) := hlogb z hz6
    _ = 72 * Real.log M / r := by rw [div_div_eq_mul_div]; ring
end Formalism.ZF
