-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RelativeIndexFlags.real_ratio_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:47:45.391036+00:00
-- url     : https://prove2.me/submissions/d766bedf-26c9-4160-afc1-1c1ae419f67e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RelativeIndexFlags_RelIndexInfRightNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RelativeIndexFlags
variable {G : Type*} [Group G]
namespace Formalism.L2.SG.Pf.RelativeIndexFlags
theorem _root_.solution (a e c f β δ : ℕ) (hβ : β ≠ 0) (hδ : δ ≠ 0) (h1 : β * a = δ * c)
    (h2 : β * e = δ * f) : (a : ℝ) / e = c / f := by
  have hβ' : (β : ℝ) ≠ 0 := by exact_mod_cast hβ
  have hδ' : (δ : ℝ) ≠ 0 := by exact_mod_cast hδ
  have h1' : (β : ℝ) * a = δ * c := by exact_mod_cast h1
  have h2' : (β : ℝ) * e = δ * f := by exact_mod_cast h2
  rw [← mul_div_mul_left (a : ℝ) (e : ℝ) hβ', h1', h2', mul_div_mul_left _ _ hδ']
end Formalism.L2.SG.Pf.RelativeIndexFlags
