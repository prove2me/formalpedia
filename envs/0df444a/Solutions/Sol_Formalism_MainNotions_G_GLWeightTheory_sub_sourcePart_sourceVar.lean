-- Prove2me | solution 1 for Formalism.MainNotions.G.GLWeightTheory.sub_sourcePart_sourceVar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:40:04.96963+00:00
-- url     : https://prove2.me/submissions/a4cb2a8a-03af-4ab7-a66d-a2f8fda04d05

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RootWeights_MatrixSubstTransvectionX
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RootWeights_MatrixSubstTransvectionMonomialOfFixed
import Theorems.Thm_Formalism_MainNotions_G_GLWeightTheory_sourceVar_fst
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
theorem _root_.solution (l : ι) (hl : l ∈ S) : (m - sourceVariableExponent LL S a b m) (sourceVar LL a b l) = 0 := by
  classical
  rw [Finsupp.tsub_apply]
  unfold sourceVariableExponent
  rw [sum_single_sourceVar_apply, sourceVar_fst, if_pos rfl]
  unfold sourceExp
  rw [if_pos hl]
  exact Nat.sub_self _
end Formalism.MainNotions.G.GLWeightTheory
