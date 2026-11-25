-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.eulerEta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:05:37.815227+00:00
-- url     : https://prove2.me/submissions/b1216d7f-024e-4f3f-83a1-ce139a8390e5

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EulerFacMulConjInvSplit
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LValEtaEqLValEtaF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_lValEta_eq_lValEtaF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_lValEta_pos
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_multipliable_eulerFac


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution : EulerEta := by
  intro K F _ _ _ _ _ _ hK hF M hM
  exact ⟨multipliable_eulerFac hK M hM, lValEta_pos hK M hM, lValEta_eq_lValEtaF hK hF M hM⟩
end Formalism.HermitianLattices.Ext.L3
