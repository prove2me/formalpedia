-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsTorsion.realC
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:42.7038+00:00
-- url     : https://prove2.me/submissions/5fdf9ae1-a008-40cd-bfa1-575defbbeb26

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsTorsionFree
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsNoPrimeToPTorsion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open Formalism Formalism.ELL Formalism.ELL.FormalGroupPointsTorsion
open WeierstrassCurve Polynomial
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
variable {W : WeierstrassCurve K}
namespace Formalism.ELL.FormalGroupPointsTorsion
theorem _root_.solution {L V M : ℝ} (hL0 : 0 ≤ L) (hV0 : 0 ≤ V) (hLM : L ^ 2 ≤ M) (hM : 1 ≤ M)
    (hV : V ≤ max 1 L) : L ≤ M ∧ V ≤ M ∧ L * V ≤ M := by
  rcases le_total L 1 with h | h
  · have hV' : V ≤ 1 := by rw [max_eq_left h] at hV; exact hV
    refine ⟨by linarith, by linarith, ?_⟩
    nlinarith
  · have hV' : V ≤ L := by rw [max_eq_right h] at hV; exact hV
    refine ⟨by nlinarith, by nlinarith, by nlinarith⟩
end Formalism.ELL.FormalGroupPointsTorsion
