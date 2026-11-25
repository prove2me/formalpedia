-- Prove2me | solution 1 for Formalism.L2.SG.GGMirabolic.Inhab.gam_one_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:15:47.206866+00:00
-- url     : https://prove2.me/submissions/a08b1f81-4407-42a1-801d-5a61e000137d

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolicInhab
import Theorems.Thm_Formalism_L2_SG_GGMirabolic_Inhab_cardU_pos
import Theorems.Thm_Formalism_L2_SG_GGMirabolic_gam_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.GGMirabolic Formalism.L2.SG.GGMirabolic.Inhab
open Formalism.L2.SG.GGMirabolic
noncomputable section
open Classical
namespace Formalism.L2.SG.GGMirabolic.Inhab
theorem _root_.solution (F : Type) [Field F] [Fintype F] (k : ℕ) (ψ₀ : AddChar F ℂ) :
    gam ψ₀ (1 : GL (Fin k) F) ≠ 0 := by
  rw [gam_one]
  have h1 : (Fintype.card (GL (Fin k) F) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h2 : (cardU F k : ℂ) ≠ 0 := by exact_mod_cast (cardU_pos F k).ne'
  exact div_ne_zero h1 h2
end Formalism.L2.SG.GGMirabolic.Inhab
