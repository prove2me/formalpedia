-- Prove2me | solution 1 for CompanionTheory.D.DSIC.qminor_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:54:47.962574+00:00
-- url     : https://prove2.me/submissions/9510f879-8ee6-45d9-a489-52827f0d69ad

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QnCovDet
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QnCovLin
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_Spread

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.DSIC
open Formalism.REAL Formalism.FourierDecayAlt.Q
namespace CompanionTheory.D.DSIC
theorem _root_.solution {A : Type} [Ring A] [Algebra ℂ A] (T : Subalgebra ℂ A) {n t : ℕ}
    (E : Fin n → Fin n → A) (hE : ∀ c d, E c d ∈ T) (a b : Fin t → Fin n) (u : ℂ) : qminor E a b u ∈ T := by
  refine T.sum_mem fun σ _ => T.mul_mem (intCast_mem T _) (T.list_prod_mem fun x hx => ?_)
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  refine T.add_mem ?_ (hE _ _)
  split_ifs
  · exact T.algebraMap_mem _
  · exact T.zero_mem
end CompanionTheory.D.DSIC
