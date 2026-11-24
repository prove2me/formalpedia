-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.lValEta_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:29:16.422097+00:00
-- url     : https://prove2.me/submissions/7ff81e5b-f132-4b2f-9741-6ba298641606

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFilterResCharLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EulerFacMulConjInvSplit
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_IdealNormInequalities_summable_log_eulerFac
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_eulerFac_pos

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
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open IdealNormInequalities
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (M : ℕ) (hM : 2 ≤ M) :
    0 < Formalism.HermitianLatticesTheory.lValEta K M := by
  unfold Formalism.HermitianLatticesTheory.lValEta
  rw [← Real.rexp_tsum_eq_tprod (fun P => eulerFac_pos hK P.2 M (by omega))
    (summable_log_eulerFac hK hM)]
  exact Real.exp_pos _
end Formalism.HermitianLattices.Ext.L3
