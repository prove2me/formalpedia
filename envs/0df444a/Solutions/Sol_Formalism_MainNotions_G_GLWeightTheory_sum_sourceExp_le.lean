-- Prove2me | solution 1 for Formalism.MainNotions.G.GLWeightTheory.sum_sourceExp_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:40:11.594519+00:00
-- url     : https://prove2.me/submissions/8e1323ef-1415-4782-b56a-7fd22bc4a1c0

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RootWeights_MatrixSubstTransvectionMonomialOfFixed
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RootWeights_SumFinsuppAntidiagEqSumPiFinset
import Theorems.Thm_Formalism_MainNotions_G_GLWeightTheory_sourceVar_fst


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
theorem _root_.solution : ∑ l : ι, sourceExp LL S a b m l ≤ m.sum fun _ e => e := by
  classical
  have hinj : ∀ x ∈ (Finset.univ : Finset ι), ∀ y ∈ (Finset.univ : Finset ι),
      sourceVar LL a b x = sourceVar LL a b y → x = y := by
    intro x _ y _ h
    have h1 := congrArg Prod.fst h
    rwa [sourceVar_fst, sourceVar_fst] at h1
  calc ∑ l : ι, sourceExp LL S a b m l ≤ ∑ l : ι, m (sourceVar LL a b l) :=
        Finset.sum_le_sum fun l _ => by unfold sourceExp; split_ifs <;> simp
    _ = ∑ v ∈ Finset.univ.image (sourceVar LL a b), m v := (Finset.sum_image hinj).symm
    _ ≤ ∑ v ∈ m.support, m v := Finset.sum_le_sum_of_ne_zero fun v _ h => Finsupp.mem_support_iff.mpr h
    _ = m.sum fun _ e => e := rfl
end Formalism.MainNotions.G.GLWeightTheory
