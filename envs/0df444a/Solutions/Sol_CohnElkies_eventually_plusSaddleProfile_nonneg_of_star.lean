-- Prove2me | solution 1 for CohnElkies.eventually_plusSaddleProfile_nonneg_of_star
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.271862+00:00
-- url     : https://prove2.me/submissions/203a7849-222a-4edd-ac9c-15de0c4e1664

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleSmallRadiusStar_pos
import Theorems.Thm_CohnElkies_eventually_saddleSmallRadiusStar_log_coverage
import Theorems.Thm_CohnElkies_eventually_plusSaddleProfile_re_pos_at_firstBranchSaddles
import Theorems.Thm_CohnElkies_eventually_plusSaddleProfile_re_pos_at_secondBranchSaddles

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ᶠ d : ℕ in atTop,
        ∀ r : ℝ,
          saddleSmallRadiusStar ε d ≤ r →
            0 ≤ (plusSaddleProfile ε ((d : ℝ) / 2) r).re := by
  filter_upwards [eventually_saddleSmallRadiusStar_log_coverage,
    eventually_plusSaddleProfile_re_pos_at_firstBranchSaddles,
    eventually_plusSaddleProfile_re_pos_at_secondBranchSaddles]
    with ε hcoverage hfirst hsecond
  filter_upwards [hcoverage, hfirst, hsecond]
    with d hcoverage_d hfirst_d hsecond_d
  intro r hr
  obtain ⟨u, hu, hlog⟩ := hcoverage_d r hr
  have hrpos : 0 < r :=
    (saddleSmallRadiusStar_pos ε d).trans_le hr
  have hexp : Real.exp (saddleLogRadius ε d u) = r := by
    rw [hlog, Real.exp_log hrpos]
  by_cases hbranch : u ≤ 1 + ε / 2
  · have h := hfirst_d u hu hbranch
    rw [hexp] at h
    exact h.le
  · have hupper : 1 + ε / 2 ≤ u :=
      (lt_of_not_ge hbranch).le
    have h := hsecond_d u hupper
    rw [hexp] at h
    exact h.le
end CohnElkies
