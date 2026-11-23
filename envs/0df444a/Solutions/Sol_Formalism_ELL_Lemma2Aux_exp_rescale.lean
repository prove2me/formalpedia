-- Prove2me | solution 1 for Formalism.ELL.Lemma2Aux.exp_rescale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:56.896974+00:00
-- url     : https://prove2.me/submissions/02e2e4aa-a370-4fab-b283-db108e451172

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionWeights
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CompExp
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CoefficientWeightsLemmaTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
open Formalism Formalism.ELL Formalism.ELL.Lemma2Aux
variable {K : Type*} [NormedField K] [IsUltrametricDist K]
open Formalism.G
namespace Formalism.ELL.Lemma2Aux
theorem _root_.solution (l E : PowerSeries K) (ζ : K) (hE0 : constantCoeff E = 0) (hl0 : constantCoeff l = 0)
    (hEl : E.subst l = X) (hlE : l.subst E = X) (hlz : (l.subst (ζ • X : PowerSeries K) : PowerSeries K) = ζ • l) :
    (E.subst (ζ • X : PowerSeries K) : PowerSeries K) = ζ • E := by
  have hE : PowerSeries.HasSubst E := PowerSeries.HasSubst.of_constantCoeff_zero' hE0
  have ha : PowerSeries.HasSubst (ζ • X : PowerSeries K) := PowerSeries.HasSubst.smul_X' ζ
  have hzE : (PowerSeries.subst E (ζ • X : PowerSeries K) : PowerSeries K) = ζ • E := by
    rw [PowerSeries.subst_smul hE, PowerSeries.subst_X hE]
  have hzE0 : constantCoeff (ζ • E) = 0 := by simp [hE0]
  have hzEs : PowerSeries.HasSubst (ζ • E) := PowerSeries.HasSubst.of_constantCoeff_zero' hzE0
  have h1 : (PowerSeries.subst (ζ • E) l : PowerSeries K) = ζ • X := by
    rw [← hzE, ← PowerSeries.subst_comp_subst_apply ha hE, hlz, PowerSeries.subst_smul hE, hlE]
  calc (E.subst (ζ • X : PowerSeries K) : PowerSeries K) = PowerSeries.subst (PowerSeries.subst (ζ • E) l : PowerSeries K) E := by rw [h1]
    _ = PowerSeries.subst (ζ • E) (PowerSeries.subst l E : PowerSeries K) :=
        (PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hl0) hzEs E).symm
    _ = ζ • E := by rw [hEl, PowerSeries.subst_X hzEs]
end Formalism.ELL.Lemma2Aux
