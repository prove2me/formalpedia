-- Prove2me | solution 1 for FiniteEnergyPlane.lintegral_rpow_lt_top_of_norm_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T21:51:30.357451+00:00
-- url     : https://prove2.me/submissions/c506477b-4d44-44fc-ba2f-39ecb66d5830

import Definitions.Def_FiniteEnergyPlane_Setting

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

namespace A3S48HI

lemma cover {r : ℝ} (hr : 0 < r) (z : ℂ) (hz : z ≠ 0) (hzr : ‖z‖ < r) :
    ∃ k : ℕ, r / 2 ^ (k + 1) ≤ ‖z‖ ∧ ‖z‖ < r / 2 ^ k := by
  have hz0 : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hex : ∃ k : ℕ, r / 2 ^ (k + 1) ≤ ‖z‖ := by
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (r / ‖z‖) (by norm_num : (1:ℝ) < 2)
    refine ⟨k, ?_⟩
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hz0] at hk
    have : (2:ℝ) ^ k ≤ 2 ^ (k+1) := pow_le_pow_right₀ (by norm_num) (by omega)
    nlinarith
  classical
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases h : Nat.find hex with _ | j
  · simpa using hzr
  · have := Nat.find_min hex (show j < Nat.find hex by omega)
    push Not at this
    exact this

end A3S48HI

open A3S48HI in
theorem solution (g : ℂ → ℝ) {r C K μ : ℝ} (hr : 0 < r)
    (hμ : 0 < μ) (hg0 : ∀ z, 0 ≤ g z) (hg : AEMeasurable g (volume.restrict (ball 0 r)))
    (hbd : ∀ z : ℂ, z ≠ 0 → ‖z‖ < r → ‖z‖ * g z ≤ C)
    (hdec : ∀ s : ℝ, 0 < s → s ≤ r →
      ∫⁻ z in ball 0 s, ENNReal.ofReal (g z ^ 2) ≤ ENNReal.ofReal (K * s ^ (2 * μ)))
    (p : ℝ) (hp2 : 2 ≤ p) (hp : p < 2 + 2 * μ) :
    ∫⁻ z in ball 0 r, ENNReal.ofReal (g z ^ p) < ⊤ := by
  -- C ≥ 0
  have hC : 0 ≤ C := by
    have h1 : ((r/2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (r/2:ℝ) ≠ 0)
    have h2 : ‖((r/2 : ℝ) : ℂ)‖ < r := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]; linarith
    have := hbd _ h1 h2
    have := hg0 ((r/2 : ℝ) : ℂ)
    have : 0 ≤ ‖((r/2 : ℝ) : ℂ)‖ := norm_nonneg _
    nlinarith
  set K' := max K 0 with hK'
  have hdec' : ∀ s : ℝ, 0 < s → s ≤ r →
      ∫⁻ z in ball 0 s, ENNReal.ofReal (g z ^ 2) ≤ ENNReal.ofReal (K' * s ^ (2 * μ)) := by
    intro s hs hsr
    refine (hdec s hs hsr).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  set a := p - 2 with ha
  have ha0 : 0 ≤ a := by linarith
  set A : ℕ → Set ℂ := fun k => ball 0 (r / 2 ^ k) \ ball 0 (r / 2 ^ (k+1)) with hA
  set M : ℕ → ℝ := fun k => C * 2 ^ (k+1) / r with hM
  set q : ℝ := (2:ℝ) ^ a / (2:ℝ) ^ (2 * μ) with hq
  set D : ℝ := (2 * C / r) ^ a * K' * r ^ (2 * μ) with hD
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by
    rw [hq, div_lt_one (by positivity)]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  have hD0 : 0 ≤ D := by positivity
  -- term bound
  have hterm : ∀ k : ℕ, ∫⁻ z in A k, ENNReal.ofReal (g z ^ p) ≤ ENNReal.ofReal (D * q ^ k) := by
    intro k
    have hsk : 0 < r / 2 ^ k := by positivity
    have hskr : r / 2 ^ k ≤ r := div_le_self hr.le (one_le_pow₀ (by norm_num))
    calc ∫⁻ z in A k, ENNReal.ofReal (g z ^ p)
        ≤ ∫⁻ z in A k, ENNReal.ofReal (M k ^ a) * ENNReal.ofReal (g z ^ 2) := by
          apply lintegral_mono_ae
          refine (ae_restrict_iff' ?_).2 (Eventually.of_forall ?_)
          · exact measurableSet_ball.diff measurableSet_ball
          intro z hz
          simp only [hA, Set.mem_sdiff, mem_ball, dist_zero_right, not_lt] at hz
          have hzpos : 0 < ‖z‖ := lt_of_lt_of_le (by positivity) hz.2
          have hz0 : z ≠ 0 := norm_pos_iff.1 hzpos
          have hzr : ‖z‖ < r := lt_of_lt_of_le hz.1 hskr
          have hgz : g z ≤ M k := by
            have h1 := hbd z hz0 hzr
            have h2 : g z ≤ C / ‖z‖ := by rw [le_div_iff₀ hzpos]; linarith
            refine h2.trans ?_
            rw [hM]
            calc C / ‖z‖ ≤ C / (r / 2 ^ (k+1)) :=
                  div_le_div_of_nonneg_left hC (by positivity) hz.2
              _ = C * 2 ^ (k+1) / r := by field_simp
          rw [← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          have : g z ^ p = g z ^ (2:ℝ) * g z ^ a := by
            rw [← Real.rpow_add' (hg0 z) (by linarith)]; congr 1; linarith
          rw [this, Real.rpow_two, mul_comm]
          exact mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow (hg0 z) hgz ha0) (by positivity)
      _ = ENNReal.ofReal (M k ^ a) * ∫⁻ z in A k, ENNReal.ofReal (g z ^ 2) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (M k ^ a) * ∫⁻ z in ball 0 (r / 2 ^ k), ENNReal.ofReal (g z ^ 2) := by
          gcongr
          exact Set.sdiff_subset
      _ ≤ ENNReal.ofReal (M k ^ a) * ENNReal.ofReal (K' * (r / 2 ^ k) ^ (2 * μ)) := by
          gcongr; exact hdec' _ hsk hskr
      _ = ENNReal.ofReal (D * q ^ k) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          have e1 : M k = (2 * C / r) * (2:ℝ) ^ k := by rw [hM]; ring
          have e2 : ((2:ℝ) ^ k) ^ a = ((2:ℝ) ^ a) ^ k := by
            rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
              ← Real.rpow_mul (by norm_num), mul_comm]
          have e3 : ((2:ℝ) ^ k) ^ (2 * μ) = ((2:ℝ) ^ (2 * μ)) ^ k := by
            rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
              ← Real.rpow_mul (by norm_num), mul_comm]
          rw [e1, Real.mul_rpow (by positivity) (by positivity), e2,
            Real.div_rpow hr.le (by positivity), e3, hD, hq, div_pow]
          have : (0:ℝ) < ((2:ℝ) ^ (2 * μ)) ^ k := by positivity
          field_simp
  -- covering
  have hsub : ball (0:ℂ) r ⊆ {0} ∪ ⋃ k, A k := by
    intro z hz
    by_cases hz0 : z = 0
    · left; exact hz0
    · right
      rw [mem_ball, dist_zero_right] at hz
      obtain ⟨k, hk1, hk2⟩ := cover hr z hz0 hz
      refine Set.mem_iUnion.2 ⟨k, ?_⟩
      simp only [hA, Set.mem_sdiff, mem_ball, dist_zero_right, not_lt]
      exact ⟨hk2, hk1⟩
  have hsum : Summable (fun k : ℕ => D * q ^ k) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left D
  calc ∫⁻ z in ball 0 r, ENNReal.ofReal (g z ^ p)
      ≤ ∫⁻ z in {0} ∪ ⋃ k, A k, ENNReal.ofReal (g z ^ p) := lintegral_mono_set hsub
    _ ≤ (∫⁻ z in ({0} : Set ℂ), ENNReal.ofReal (g z ^ p))
          + ∫⁻ z in ⋃ k, A k, ENNReal.ofReal (g z ^ p) := lintegral_union_le _ _ _
    _ = ∫⁻ z in ⋃ k, A k, ENNReal.ofReal (g z ^ p) := by
          rw [setLIntegral_measure_zero ({0} : Set ℂ) _ (measure_singleton (0:ℂ)), zero_add]
    _ ≤ ∑' k, ∫⁻ z in A k, ENNReal.ofReal (g z ^ p) := lintegral_iUnion_le _ _
    _ ≤ ∑' k, ENNReal.ofReal (D * q ^ k) := ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (∑' k, D * q ^ k) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsum).symm
    _ < ⊤ := ENNReal.ofReal_lt_top
