-- Prove2me | solution 1 for AvramDividend.Classical.continuousOn_positive_causal_convolution_of_locally_bounded_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:59:47.103785+00:00
-- url     : https://prove2.me/submissions/f1ac48c9-05c3-4bb7-89c4-7a62abaf6b36

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_positive_ramp_cutoff_continuous_and_support
import Theorems.Thm_AvramDividend_Classical_continuous_causal_convolution_of_bounded_continuous_left
import Theorems.Thm_AvramDividend_Classical_real_causal_convolution_comm
import Theorems.Thm_AvramDividend_Classical_causal_convolution_zero_above_support_sum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology

/-- Split a causal L1 kernel into a bounded continuous tail and a
remainder supported close to zero. -/
theorem AvramDividend.Classical.causal_cutoff_decomposition
    (f : ℝ → ℝ) (hfint : Integrable f volume)
    (hfcont : ContinuousOn f (Ioi (0 : ℝ)))
    (hfbound : ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ x : ℝ, ε ≤ x → |f x| ≤ M)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ F U : ℝ → ℝ, (∀ t, f t = F t + U t) ∧ Continuous F ∧
      BddAbove (range fun t : ℝ => ‖F t‖) ∧ Integrable U volume ∧
      (∀ t, 2 * ε < t → U t = 0) := by
  let χ : ℝ → ℝ := fun t => max 0 (min 1 ((t - ε) / ε))
  obtain ⟨hχc, hχzero, hχone⟩ :=
    positive_ramp_cutoff_continuous_and_support ε hε
  have hχ0 (t : ℝ) : 0 ≤ χ t := le_max_left _ _
  have hχ1 (t : ℝ) : χ t ≤ 1 := by
    dsimp [χ]; exact max_le (by norm_num) (min_le_left _ _)
  have hχabs (t : ℝ) : |χ t| ≤ 1 := by
    rw [abs_of_nonneg (hχ0 t)]; exact hχ1 t
  have hηabs (t : ℝ) : |1 - χ t| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr (hχ1 t))]; linarith [hχ0 t]
  let F : ℝ → ℝ := fun t => χ t * f t
  let U : ℝ → ℝ := fun t => (1 - χ t) * f t
  have hFc : Continuous F := by
    rw [continuous_iff_continuousAt]; intro t
    by_cases ht : t < ε
    · have heq : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 t] F := by
        filter_upwards [isOpen_Iio.mem_nhds ht] with y hy
        have hcut : χ y = 0 := hχzero y (le_of_lt hy)
        simp only [F, hcut, zero_mul]
      exact continuousAt_const.congr_of_eventuallyEq heq.symm
    · have htpos : 0 < t := by linarith
      exact hχc.continuousAt.mul (hfcont.continuousAt (isOpen_Ioi.mem_nhds htpos))
  obtain ⟨M, hM⟩ := hfbound ε hε
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (f ε)) (hM ε le_rfl)
  have hFb : BddAbove (range fun t : ℝ => ‖F t‖) := by
    refine ⟨M, ?_⟩; rintro z ⟨t, rfl⟩
    by_cases ht : t ≤ ε
    · change ‖χ t * f t‖ ≤ M
      rw [show χ t = 0 from hχzero t ht]
      simpa using hM0
    · have hp : |χ t * f t| ≤ |f t| := by
        calc
          |χ t * f t| = |χ t| * |f t| := abs_mul _ _
          _ ≤ 1 * |f t| :=
            mul_le_mul_of_nonneg_right (hχabs t) (abs_nonneg _)
          _ = |f t| := one_mul _
      exact (by simpa [F, Real.norm_eq_abs] using
        le_trans hp (hM t (le_of_lt (lt_of_not_ge ht))))
  have hUi : Integrable U volume := by
    have hc : Continuous (fun t : ℝ => 1 - χ t) := continuous_const.sub hχc
    have hb : ∀ᵐ t : ℝ ∂volume, ‖1 - χ t‖ ≤ (1 : ℝ) :=
      Filter.Eventually.of_forall (fun t => by simpa [Real.norm_eq_abs] using hηabs t)
    simpa [U] using (hfint.bdd_mul hc.aestronglyMeasurable hb)
  refine ⟨F, U, ?_, hFc, hFb, hUi, ?_⟩
  · intro t; dsimp [F, U]; ring
  · intro t ht; dsimp [U]
    have hunit : χ t = 1 := hχone t (le_of_lt ht)
    rw [hunit]; ring
/-- Causal integrable kernels with continuous, locally bounded positive tails
have a continuous real convolution on strictly positive reserves. -/
theorem solution (f g : ℝ → ℝ)
    (hfint : Integrable f volume) (hgint : Integrable g volume)
    (hfcont : ContinuousOn f (Ioi (0 : ℝ)))
    (hgcont : ContinuousOn g (Ioi (0 : ℝ)))
    (hfzero : ∀ x : ℝ, x ≤ 0 → f x = 0)
    (hgzero : ∀ x : ℝ, x ≤ 0 → g x = 0)
    (hfbound : ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ x : ℝ, ε ≤ x → |f x| ≤ M)
    (hgbound : ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ x : ℝ, ε ≤ x → |g x| ≤ M) :
    ContinuousOn (fun x : ℝ => ∫ y : ℝ, f y * g (x - y) ∂volume) (Ioi 0) := by
  intro x hx
  let ε : ℝ := x / 8
  have hε : 0 < ε := by exact div_pos hx (by norm_num)
  obtain ⟨F, U, hfsum, hFc, hFb, hUi, hUzero⟩ :=
    causal_cutoff_decomposition f hfint hfcont hfbound ε hε
  obtain ⟨G, V, hgsum, hGc, hGb, hVi, hVzero⟩ :=
    causal_cutoff_decomposition g hgint hgcont hgbound ε hε
  have hcontFG : Continuous (fun z : ℝ =>
      ∫ y : ℝ, F y * g (z - y) ∂volume) :=
    continuous_causal_convolution_of_bounded_continuous_left F g hFc hFb hgint
  have hcontGU : Continuous (fun z : ℝ =>
      ∫ y : ℝ, G y * U (z - y) ∂volume) :=
    continuous_causal_convolution_of_bounded_continuous_left G U hGc hGb hUi
  have hident (z : ℝ) (hz : 4 * ε < z) (y : ℝ) :
      f y * g (z - y) = F y * g (z - y) + U y * G (z - y) := by
    rw [hfsum y, hgsum (z - y)]
    by_cases hy : 2 * ε < y
    · rw [hUzero y hy]; ring
    · have hzother : 2 * ε < z - y := by linarith
      rw [hVzero (z - y) hzother]; ring
  have hconv (z : ℝ) (hz : 4 * ε < z) :
      (∫ y : ℝ, f y * g (z - y) ∂volume) =
      (∫ y : ℝ, F y * g (z - y) ∂volume) +
      (∫ y : ℝ, G y * U (z - y) ∂volume) := by
    have hIG : Integrable (fun y : ℝ => F y * g (z - y)) volume := by
      have hgshift : Integrable (fun y : ℝ => g (z - y)) volume := hgint.comp_sub_left z
      rcases hFb with ⟨M, hM⟩
      have hb : ∀ᵐ y : ℝ ∂volume, ‖F y‖ ≤ M :=
        Filter.Eventually.of_forall (fun y => hM (mem_range_self y))
      exact hgshift.bdd_mul hFc.aestronglyMeasurable hb
    have hIUG : Integrable (fun y : ℝ => U y * G (z - y)) volume := by
      have hGcshift : AEStronglyMeasurable (fun y : ℝ => G (z - y)) volume :=
        (hGc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      rcases hGb with ⟨M, hM⟩
      have hb : ∀ᵐ y : ℝ ∂volume, ‖G (z - y)‖ ≤ M :=
        Filter.Eventually.of_forall (fun y => hM (mem_range_self (z - y)))
      have hi := hUi.bdd_mul hGcshift hb
      simpa only [mul_comm] using hi
    calc
      (∫ y : ℝ, f y * g (z - y) ∂volume) =
          ∫ y : ℝ, (F y * g (z - y) + U y * G (z - y)) ∂volume := by
            congr 1; ext y; exact hident z hz y
      _ = (∫ y : ℝ, F y * g (z - y) ∂volume) +
          (∫ y : ℝ, U y * G (z - y) ∂volume) := integral_add hIG hIUG
      _ = (∫ y : ℝ, F y * g (z - y) ∂volume) +
          (∫ y : ℝ, G y * U (z - y) ∂volume) := by
            rw [real_causal_convolution_comm U G z]
  have hxnear : Ioi (4 * ε) ∈ 𝓝 x := by
    apply isOpen_Ioi.mem_nhds
    have hxsplit : x = 8 * ε := by dsimp [ε]; ring
    calc
      4 * ε < 8 * ε :=
        mul_lt_mul_of_pos_right (by norm_num : (4 : ℝ) < 8) hε
      _ = x := hxsplit.symm
  have hevent : (fun z : ℝ => ∫ y : ℝ, f y * g (z - y) ∂volume) =ᶠ[𝓝 x]
      (fun z : ℝ => (∫ y : ℝ, F y * g (z - y) ∂volume) +
        (∫ y : ℝ, G y * U (z - y) ∂volume)) := by
    filter_upwards [hxnear] with z hz
    exact hconv z hz
  have hgood : ContinuousAt (fun z : ℝ =>
      (∫ y : ℝ, F y * g (z - y) ∂volume) +
      (∫ y : ℝ, G y * U (z - y) ∂volume)) x :=
    hcontFG.continuousAt.add hcontGU.continuousAt
  exact (hgood.congr_of_eventuallyEq hevent).continuousWithinAt
