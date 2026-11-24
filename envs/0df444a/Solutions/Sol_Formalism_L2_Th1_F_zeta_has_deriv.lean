-- Prove2me | solution 1 for Formalism.L2.Th1.F.zeta_has_deriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:36:40.693101+00:00
-- url     : https://prove2.me/submissions/e7e8a858-5ced-4d38-a849-671a2f89e6a0

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_AnalyticIdentityTheoremsZetaFacts
import Theorems.Thm_Formalism_L2_Th1_F_AnalyticIdentityTheoremsZetaFacts_eqOn_deriv_wZeta
import Theorems.Thm_Formalism_L2_Th1_F_AnalyticIdentityTheoremsZetaFacts_differentiableOn_wZeta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open AnalyticIdentityTheoremsZetaFacts
namespace Formalism.L2.Th1.F
theorem _root_.solution : ZetaHasDeriv := by
  intro L z hz
  have hU : IsOpen ((L.lattice : Set ℂ)ᶜ) := L.isClosed_lattice.isOpen_compl
  have hd := (differentiableOn_wZeta L).differentiableAt (hU.mem_nhds hz)
  have := hd.hasDerivAt
  rwa [eqOn_deriv_wZeta L hz] at this
end Formalism.L2.Th1.F
