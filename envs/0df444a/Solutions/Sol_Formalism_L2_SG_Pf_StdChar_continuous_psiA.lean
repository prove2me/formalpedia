-- Prove2me | solution 1 for Formalism.L2.SG.Pf.StdChar.continuous_psiA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:38:40.608811+00:00
-- url     : https://prove2.me/submissions/b003031f-4ee2-44a0-a907-38da63ff615f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_MeasCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EmbeddingTraceSumAlt_NormUnitsOfCalculation
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_FundamentalContinuity_AdelicIsomorphismStatement
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_StdChar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Topology Filter
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.StdChar
variable (F : Type) [Field F] [NumberField F]
namespace Formalism.L2.SG.Pf.StdChar
theorem _root_.solution : Continuous (psiA F) := by
  have hp : ∀ w : InfinitePlace F, Continuous (fun x : Ainf F => x w) := fun w => continuous_apply w
  have hc : ∀ w : InfinitePlace F, Continuous (InfinitePlace.Completion.extensionEmbedding w) := by
    intro w
    first
      | exact (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous
      | exact UniformSpace.Completion.continuous_extension
  have hs : Continuous (fun x : Ainf F =>
      (∑ w : InfinitePlace F, (InfinitePlace.Completion.extensionEmbedding w (x w)).re : ℝ)) :=
    continuous_finset_sum _ (fun w _ => Complex.continuous_re.comp ((hc w).comp (hp w)))
  unfold psiA
  exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hs))
end Formalism.L2.SG.Pf.StdChar
