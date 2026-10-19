-- Prove2me | solution 1 for CohnElkies.stripPoissonPrimitive_centered_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:21.360486+00:00
-- url     : https://prove2.me/submissions/1c3476a5-6c42-4e3e-9c73-a4f47026e7ae

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripPoissonPrimitive_centered_antitoneOn
import Theorems.Thm_CohnElkies_stripPoissonPrimitive_centered_neg

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1)
    {r : ℝ} (hr : 0 ≤ r) (s : ℝ) :
    stripPoissonPrimitive σ (s + r) -
        stripPoissonPrimitive σ (s - r) ≤
      stripPoissonPrimitive σ r -
        stripPoissonPrimitive σ (-r) := by
  have hanti :=
    stripPoissonPrimitive_centered_antitoneOn
      hbelow habove hr
  by_cases hs : 0 ≤ s
  · convert! hanti (show (0 : ℝ) ∈ Ici 0 by simp)
      (show s ∈ Ici 0 from hs) hs using 1
    all_goals ring_nf
  · have hsneg : 0 ≤ -s := by linarith
    rw [← stripPoissonPrimitive_centered_neg
      hbelow habove r s]
    convert! hanti (show (0 : ℝ) ∈ Ici 0 by simp)
      (show -s ∈ Ici 0 from hsneg) hsneg using 1
    all_goals ring_nf
end CohnElkies
