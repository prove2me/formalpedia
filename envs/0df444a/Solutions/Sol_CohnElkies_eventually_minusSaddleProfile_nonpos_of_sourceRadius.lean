-- Prove2me | solution 1 for CohnElkies.eventually_minusSaddleProfile_nonpos_of_sourceRadius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.271862+00:00
-- url     : https://prove2.me/submissions/2c47280c-b062-4fb7-92bb-ac3db7177418

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_eventually_saddleSourceRadius_log_coverage
import Theorems.Thm_CohnElkies_eventually_minusSaddleProfile_re_neg_at_firstBranchSaddles
import Theorems.Thm_CohnElkies_eventually_minusSaddleProfile_re_neg_at_secondBranchSaddles

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
          saddleSourceRadius ε d ≤ r →
            (minusSaddleProfile ε ((d : ℝ) / 2) r).re ≤ 0 := by
  filter_upwards [eventually_saddleSourceRadius_log_coverage,
    eventually_minusSaddleProfile_re_neg_at_firstBranchSaddles,
    eventually_minusSaddleProfile_re_neg_at_secondBranchSaddles]
    with ε hcoverage hfirst hsecond
  filter_upwards [hfirst, hsecond,
    eventually_gt_atTop (0 : ℕ)] with d hfirst_d hsecond_d hd
  intro r hr
  obtain ⟨u, hu, hlog⟩ := hcoverage d hd r hr
  have hrpos : 0 < r :=
    (saddleSourceRadius_pos ε d).trans_le hr
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
