-- Prove2me | solution 1 for Formalism.L2.Th1.F.WeierstrassZetaQuasiPeriod.isOpen_compl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:30:10.418244+00:00
-- url     : https://prove2.me/submissions/3c72e2ac-9a35-4fbb-bcc5-1566803895a1

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_ZetaQuasi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.WeierstrassZetaQuasiPeriod
namespace Formalism.L2.Th1.F.WeierstrassZetaQuasiPeriod
theorem _root_.solution (L : PeriodPair) : IsOpen ((L.lattice : Set ℂ)ᶜ) :=
  L.isClosed_lattice.isOpen_compl
end Formalism.L2.Th1.F.WeierstrassZetaQuasiPeriod
