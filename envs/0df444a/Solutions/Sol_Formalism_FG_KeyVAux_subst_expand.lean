-- Prove2me | solution 1 for Formalism.FG.KeyVAux.subst_expand
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:11.755729+00:00
-- url     : https://prove2.me/submissions/bce6efc6-cc37-4020-8b10-c1faf827b251

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
    {a : ι → MvPowerSeries τ R} (ha : MvPowerSeries.HasSubst a) (φ : MvPowerSeries ι R) :
    MvPowerSeries.subst a (MvPowerSeries.expand q hq φ) =
      MvPowerSeries.subst (fun i => a i ^ q) φ := by
  simp only [MvPowerSeries.expand, MvPowerSeries.substAlgHom_apply]
  rw [MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.HasSubst.X_pow hq) ha]
  congr 1
  funext i
  rw [MvPowerSeries.subst_pow ha, MvPowerSeries.subst_X ha]
end Formalism.FG.KeyVAux
