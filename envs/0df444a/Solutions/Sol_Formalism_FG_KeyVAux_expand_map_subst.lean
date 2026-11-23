-- Prove2me | solution 1 for Formalism.FG.KeyVAux.expand_map_subst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:58.233219+00:00
-- url     : https://prove2.me/submissions/3db2b3b4-a412-4951-920f-788f4b99c887

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_NormSigmaLeOne
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffV
import Definitions.Def_Lemmata_MultivariateIntegrals_IntegralMv
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FunctionalEquationSubstVector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
open Formalism Formalism.FG Formalism.FG.KeyVAux
open Formalism.G Formalism.LT
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.FG.KeyVAux
theorem _root_.solution {ι : Type v} {τ : Type w} {R : Type u} [CommRing R] (q : ℕ) (hq : q ≠ 0)
    (σ : R →+* R) {a : ι → MvPowerSeries τ R} (ha : MvPowerSeries.HasSubst a)
    (φ : MvPowerSeries ι R) :
    MvPowerSeries.expand q hq (MvPowerSeries.map σ (MvPowerSeries.subst a φ)) =
      MvPowerSeries.subst (fun i => MvPowerSeries.expand q hq (MvPowerSeries.map σ (a i)))
        (MvPowerSeries.map σ φ) := by
  rw [MvPowerSeries.map_subst ha, MvPowerSeries.expand_subst q hq (ha.map σ)]
end Formalism.FG.KeyVAux
