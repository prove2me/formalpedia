-- Prove2me | solution 1 for Formalism.L2.G.Model.sw_Dop_rowDiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:10:14.834194+00:00
-- url     : https://prove2.me/submissions/b39f01f0-db44-484b-9754-3a25d92e351c

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_SwRowDivZero
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LGradedLemmas
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_SwRowGenMonomial
import Theorems.Thm_Formalism_L2_G_Model_sw_Dop_self
import Theorems.Thm_Formalism_L2_G_Model_sw_Dop_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Model
open Formalism.GradedWeylDivisibility
namespace Formalism.L2.G.Model
theorem _root_.solution (R : Type) [CommRing R] {r n : ℕ} (a b : Fin r)
    (f : MvPolynomial (Fin r × Fin n) R) : Dop R a b f = rowDiv R a b 1 f := by
  by_cases hab : a = b
  · subst hab; exact sw_Dop_self R a f
  · exact sw_Dop_ne R a b hab f
end Formalism.L2.G.Model
