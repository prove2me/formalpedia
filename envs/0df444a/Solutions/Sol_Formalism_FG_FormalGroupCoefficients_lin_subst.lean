-- Prove2me | solution 1 for Formalism.FG.FormalGroupCoefficients.lin_subst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:05.329351+00:00
-- url     : https://prove2.me/submissions/183830fb-fae4-4f12-ab23-624b761e4881

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FunctionalEquationHomVector
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_GroupV
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_cc_pderiv
import Theorems.Thm_Formalism_G_LogCR_pderiv_subst
import Theorems.Thm_Formalism_G_LogP_constantCoeff_subst_of_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v
open Formalism Formalism.FG Formalism.FG.FormalGroupCoefficients
open MvPowerSeries Formalism.G Formalism.LT
variable {R : Type u} [CommRing R]
namespace Formalism.FG.FormalGroupCoefficients
theorem _root_.solution {σ τ : Type*} [Fintype σ] [Finite τ] {a : σ → MvPowerSeries τ R}
    (ha : ∀ j, constantCoeff (a j) = 0) (g : MvPowerSeries σ R) (i : τ) :
    coeff (Finsupp.single i 1) (g.subst a) =
      ∑ j, coeff (Finsupp.single j 1) g * coeff (Finsupp.single i 1) (a j) := by
  rw [← cc_pderiv, Formalism.G.LogCR.pderiv_subst ha, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, cc_pderiv, Formalism.G.LogP.constantCoeff_subst_of_zero _ ha, cc_pderiv]
end Formalism.FG.FormalGroupCoefficients
