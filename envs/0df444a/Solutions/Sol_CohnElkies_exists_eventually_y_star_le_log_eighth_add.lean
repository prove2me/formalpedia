-- Prove2me | solution 1 for CohnElkies.exists_eventually_y_star_le_log_eighth_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.981105+00:00
-- url     : https://prove2.me/submissions/2ad0108c-4f27-44a6-b5e6-2e46727a7b0c

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleSmallRadiusStar_pos
import Theorems.Thm_CohnElkies_exists_saddleSmallRadiusStar_coordinate_bound

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ d : ℕ in atTop,
        ∀ r : ℝ, 0 ≤ r →
          r ≤ saddleSmallRadiusStar ε d →
            saddleSmallRadiusVariable ε r ≤
              Real.log ((d : ℝ) / 2) / 8 + C := by
  obtain ⟨C, hC, hstar⟩ :=
    exists_saddleSmallRadiusStar_coordinate_bound
      hε horder
  refine ⟨C, hC, ?_⟩
  have hcast :
      Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlarge :
      ∀ᶠ d : ℕ in atTop,
        2 * Real.exp 8 < (d : ℝ) :=
    hcast.eventually
      (eventually_gt_atTop (2 * Real.exp 8))
  filter_upwards [hlarge] with d hd
  intro r hr hrstar
  have hℓ : 0 < (d : ℝ) / 2 := by
    have he := Real.exp_pos (8 : ℝ)
    linarith
  have hlog : 8 < Real.log ((d : ℝ) / 2) := by
    apply (Real.lt_log_iff_exp_lt hℓ).mpr
    linarith
  have hstarpositive : 0 < saddleSmallRadiusStar ε d :=
    saddleSmallRadiusStar_pos ε d
  have hsquare :
      r ^ 2 ≤ (saddleSmallRadiusStar ε d) ^ 2 := by
    nlinarith [mul_nonneg
      (sub_nonneg.mpr hrstar)
      (add_nonneg hstarpositive.le hr)]
  calc
    saddleSmallRadiusVariable ε r ≤
        saddleSmallRadiusVariable ε
          (saddleSmallRadiusStar ε d) := by
      unfold saddleSmallRadiusVariable
      gcongr
    _ ≤ Real.log ((d : ℝ) / 2) / 8 + C :=
      hstar d hlog
end CohnElkies
