-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.massRatio_eq_lvalue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:54:52.28339+00:00
-- url     : https://prove2.me/submissions/3e0a9256-9542-4b1e-85e0-5d0cf917abd3

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CovolumeIntegerLatticeEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LValEtaEqLValEtaF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_DifferentIdealEqTop
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassRatioEqLvalue
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_lValEta_eq_lValEtaF


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
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (m : ℕ) (hm : 2 ≤ m) :
    Formalism.HermitianLatticesTheory.massRatioRightSide K m =
      (((m - 1).factorial : ℝ) / Real.pi ^ m) ^ Formalism.HermitianLatticesTheory.fDeg K *
        Formalism.HermitianLatticesTheory.vInv K ^ (Formalism.HermitianLatticesTheory.fDeg K * m) /
          Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) * lValEtaF K F m := by
  unfold Formalism.HermitianLatticesTheory.massRatioRightSide
  rw [lValEta_eq_lValEtaF hK hF m hm, mul_comm (Formalism.HermitianLatticesTheory.fDeg K) m, pow_mul, ← mul_pow, div_pow]
  congr 3
  ring
end Formalism.HermitianLattices.Ext.L3
