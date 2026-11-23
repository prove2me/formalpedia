-- Prove2me | solution 1 for Formalism.FG.KeyVAux.bd_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:57.688849+00:00
-- url     : https://prove2.me/submissions/5812e0ef-be0b-4b0b-84b2-bd9b8115212a

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
theorem _root_.solution {τ : Type w} {C : ℝ} (hC : 0 ≤ C) {A B : MvPowerSeries τ K}
    (hA : IntegralMv A) (hB : Bd C B) : Bd C (A * B) := by
  classical
  intro d
  rw [MvPowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC fun x _ => ?_
  rw [norm_mul]
  calc ‖MvPowerSeries.coeff x.1 A‖ * ‖MvPowerSeries.coeff x.2 B‖ ≤ 1 * C :=
        mul_le_mul (hA _) (hB _) (norm_nonneg _) zero_le_one
    _ = C := one_mul C
end Formalism.FG.KeyVAux
