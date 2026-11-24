-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.massRatio_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:32:17.772847+00:00
-- url     : https://prove2.me/submissions/99f80e97-a73b-44b7-946d-4c8059fd120f

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CovolumeIntegerLatticeEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LValEtaEqLValEtaF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_DifferentIdealEqTop
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassRatioEqLvalue
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_lValEta_pos
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_vInv_pos


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
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (M : ℕ) (hM : 2 ≤ M) :
    0 < Formalism.HermitianLatticesTheory.massRatioRightSide K M := by
  have hv := vInv_pos K
  unfold Formalism.HermitianLatticesTheory.massRatioRightSide
  refine mul_pos (div_pos (pow_pos (mul_pos ?_ (pow_pos (div_pos hv Real.pi_pos) _)) _) ?_)
    (lValEta_pos hK M hM)
  · exact_mod_cast Nat.factorial_pos _
  · exact Real.sqrt_pos.mpr (pow_pos (mul_pos two_pos hv) _)
end Formalism.HermitianLattices.Ext.L3
