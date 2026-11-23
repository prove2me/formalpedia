-- Prove2me | solution 1 for Formalism.FG.KeyVAux.bd_prod_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:58.054622+00:00
-- url     : https://prove2.me/submissions/5f617280-4baf-4a56-99ca-17961147a037

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_NormSigmaLeOne
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffV
import Definitions.Def_Lemmata_MultivariateIntegrals_IntegralMv
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FunctionalEquationSubstVector
import Theorems.Thm_Bl_ProductIntegralBounds_goal1


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
theorem _root_.solution {τ : Type w} {ι : Type v} {C : ℝ} (hC : 0 ≤ C) (X Y : ι → MvPowerSeries τ K)
    (s : Finset ι) (hX : ∀ i ∈ s, IntegralMv (X i)) (hY : ∀ i ∈ s, IntegralMv (Y i))
    (hXY : ∀ i ∈ s, Bd C (X i - Y i)) :
    Bd C (∏ i ∈ s, X i - ∏ i ∈ s, Y i) := by
  first | exact Bl.ProductIntegralBounds.goal1 .. | (apply Bl.ProductIntegralBounds.goal1 <;> assumption) | (intros; apply Bl.ProductIntegralBounds.goal1 <;> assumption) | (apply @Bl.ProductIntegralBounds.goal1 <;> assumption) | (intros; apply @Bl.ProductIntegralBounds.goal1 <;> assumption) | (apply @Bl.ProductIntegralBounds.goal1 <;> first | assumption | infer_instance) | exact @Bl.ProductIntegralBounds.goal1 K ‹_› ‹_› τ ι C hC X Y s hX hY hXY | exact @Bl.ProductIntegralBounds.goal1 K ‹_› ‹_› τ ι C hC X Y s hX hY | exact @Bl.ProductIntegralBounds.goal1 K ‹_› ‹_› τ ι C hC X Y s hX | exact @Bl.ProductIntegralBounds.goal1 K ‹_› ‹_› τ ι C hC X Y s | exact @Bl.ProductIntegralBounds.goal1 K ‹_› ‹_› τ ι C hC X Y | exact @Bl.ProductIntegralBounds.goal1 K ‹_› ‹_› τ ι C hC X | exact @Bl.ProductIntegralBounds.goal1 K ‹_› ‹_› τ ι C hC | exact @Bl.ProductIntegralBounds.goal1 K ‹_› ‹_› τ ι C | exact @Bl.ProductIntegralBounds.goal1 K ‹_› ‹_› τ ι | exact @Bl.ProductIntegralBounds.goal1 K ‹_› ‹_› τ | exact @Bl.ProductIntegralBounds.goal1 K ‹_› ‹_› | exact @Bl.ProductIntegralBounds.goal1 K ‹_› | exact @Bl.ProductIntegralBounds.goal1 K
end Formalism.FG.KeyVAux
