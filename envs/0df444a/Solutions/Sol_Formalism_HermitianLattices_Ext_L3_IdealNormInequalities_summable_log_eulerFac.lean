-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.IdealNormInequalities.summable_log_eulerFac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:26:58.895784+00:00
-- url     : https://prove2.me/submissions/7b3abae3-e317-40d0-bd9a-52550006bdba

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFilterResCharLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EulerFacMulConjInvSplit
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_IdealNormInequalities_abs_smallTerm_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_IdealNormInequalities_abs_log_eulerFac_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_IdealNormInequalities_summable_resChar_sq


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
open Formalism.HermitianLattices.Ext.L3.IdealNormInequalities
namespace Formalism.HermitianLattices.Ext.L3.IdealNormInequalities
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {M : ℕ} (hM : 2 ≤ M) :
    Summable (fun P : {P : Ideal (𝓞 K) // P.IsMaximal} =>
      Real.log (Formalism.HermitianLatticesTheory.eulerFac K M P.1)) := by
  have h1 : Summable (fun P : {P : Ideal (𝓞 K) // P.IsMaximal} => smallTerm M P.1) :=
    Summable.of_norm_bounded summable_resChar_sq (fun P => abs_smallTerm_le hK P.2 hM)
  have h2 := (Real.summable_log_one_add_of_summable h1).abs
  exact Summable.of_norm_bounded h2 (fun P => abs_log_eulerFac_le P.2 (by omega))
end Formalism.HermitianLattices.Ext.L3.IdealNormInequalities
