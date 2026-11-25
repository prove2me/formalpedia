-- Prove2me | solution 1 for Formalism.L2.SG.Pf.AllRowsGA.conjA_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:56:37.828406+00:00
-- url     : https://prove2.me/submissions/94adda88-0aa1-49da-985a-0b4ea572fa2e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_AllRowsGA
import Theorems.Thm_Formalism_L2_SG_Pf_AllRowsGA_conjA_coeff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MonoidAlgebra
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.AllRowsGA
variable {G : Type} [Group G] [Fintype G]
namespace Formalism.L2.SG.Pf.AllRowsGA
theorem _root_.solution (a b : MonoidAlgebra ℂ G) : conjA (a - b) = conjA a - conjA b := by
  refine MonoidAlgebra.ext (Finsupp.ext fun g => ?_)
  simp [conjA_coeff, MonoidAlgebra.coeff_sub, star_sub]
end Formalism.L2.SG.Pf.AllRowsGA
