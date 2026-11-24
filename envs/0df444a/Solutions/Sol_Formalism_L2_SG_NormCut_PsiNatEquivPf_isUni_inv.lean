-- Prove2me | solution 1 for Formalism.L2.SG.NormCut.PsiNatEquivPf.isUni_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:25:01.013849+00:00
-- url     : https://prove2.me/submissions/cce3f063-dbff-4fa3-a72a-9c9f7b68ef38

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_NormCore
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_NormCorePsiNatEquiv
import Theorems.Thm_Formalism_L2_SG_NormCut_PsiNatEquivPf_IsUTm_inv_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open scoped ComplexConjugate
noncomputable section
open Classical
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.NormCut Formalism.L2.SG.NormCut.PsiNatEquivPf
open Formalism.L2.SG.GGMirabolic
variable {F : Type} [Field F] [Fintype F] {k : ℕ}
namespace Formalism.L2.SG.NormCut.PsiNatEquivPf
theorem _root_.solution {x : GL (Fin k) F} (hx : IsUni k x) : IsUni k x⁻¹ := IsUTm.inv_val x hx
end Formalism.L2.SG.NormCut.PsiNatEquivPf
