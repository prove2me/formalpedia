-- Prove2me | solution 1 for Formalism.MainNotions.G.GLWeightTheory.sourcePart_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:40:17.411081+00:00
-- url     : https://prove2.me/submissions/cb0fb485-8a4a-4f4e-ac07-975fe2fdfa25

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RootWeights_MatrixSubstTransvectionX
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RootWeights_MatrixSubstTransvectionMonomialOfFixed
import Theorems.Thm_Formalism_MainNotions_G_GLWeightTheory_sum_single_sourceVar_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory
open Formalism.MainNotions.G
variable {B : Type*} [CommRing B] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
  (a b : Fin n) (t : B) (m : ι × Fin n →₀ ℕ)
namespace Formalism.MainNotions.G.GLWeightTheory
theorem _root_.solution : sourceVariableExponent LL S a b m ≤ m := by
  classical
  rw [Finsupp.le_def]
  intro v
  unfold sourceVariableExponent
  rw [sum_single_sourceVar_apply]
  split_ifs with h
  · unfold sourceExp
    split_ifs
    · exact (congrArg m h.symm).le
    · exact Nat.zero_le _
  · exact Nat.zero_le _
end Formalism.MainNotions.G.GLWeightTheory
