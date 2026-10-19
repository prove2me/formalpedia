-- Prove2me | solution 1 for CohnElkies.lowerRiemannLog_halfInteger_tail_integral_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:33.627368+00:00
-- url     : https://prove2.me/submissions/b5e07271-9e37-4105-9ed9-d064da0f4dab

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerRiemannLog_monotoneOn
import Theorems.Thm_CohnElkies_lowerRiemannLog_continuous

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Metric Set
open scoped ENNReal Interval Topology
namespace CohnElkies
theorem _root_.solution
    (k : ℕ) {ℓ T : ℝ}
    (hℓeq : ℓ = (k : ℝ) + 1 / 2)
    (hT : T ≠ 0) :
    ℓ * (∫ x in ((k : ℝ) / ℓ)..1,
      lowerRiemannLog T x) ≤
        (1 / 2 : ℝ) * lowerRiemannLog T 1 := by
  have hℓ : 0 < ℓ := by
    rw [hℓeq]
    positivity
  have hratio_nonneg : 0 ≤ (k : ℝ) / ℓ := by positivity
  have hratio_le : (k : ℝ) / ℓ ≤ 1 := by
    apply (div_le_one hℓ).2
    rw [hℓeq]
    linarith
  have hcont := lowerRiemannLog_continuous hT
  have hint : IntervalIntegrable
      (lowerRiemannLog T) volume ((k : ℝ) / ℓ) 1 :=
    hcont.intervalIntegrable _ _
  have hconst : IntervalIntegrable
      (fun _ : ℝ => lowerRiemannLog T 1)
      volume ((k : ℝ) / ℓ) 1 :=
    intervalIntegrable_const
  have hmono :
      (∫ x in ((k : ℝ) / ℓ)..1,
        lowerRiemannLog T x) ≤
        ∫ _x in ((k : ℝ) / ℓ)..1,
          lowerRiemannLog T 1 := by
    apply intervalIntegral.integral_mono_on
      hratio_le hint hconst
    intro x hx
    apply lowerRiemannLog_monotoneOn hT
    · exact (show x ∈ Ici (0 : ℝ) from
        le_trans hratio_nonneg hx.1)
    · exact (show (1 : ℝ) ∈ Ici (0 : ℝ) by norm_num)
    · exact hx.2
  rw [intervalIntegral.integral_const,
    smul_eq_mul] at hmono
  have hscaled := mul_le_mul_of_nonneg_left hmono hℓ.le
  have hfactor : ℓ * (1 - (k : ℝ) / ℓ) = (1 / 2 : ℝ) := by
    field_simp [hℓ.ne']
    rw [hℓeq]
    ring
  calc
    ℓ * (∫ x in ((k : ℝ) / ℓ)..1,
      lowerRiemannLog T x) ≤
        ℓ * ((1 - (k : ℝ) / ℓ) *
          lowerRiemannLog T 1) := hscaled
    _ = (1 / 2 : ℝ) * lowerRiemannLog T 1 := by
      rw [← mul_assoc, hfactor]
end CohnElkies
