-- Prove2me | solution 1 for Formalism.REAL.arr_operator_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:43:13.126075+00:00
-- url     : https://prove2.me/submissions/b2005fbc-4e8d-49af-8d9b-2e5750ca8d17

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactGeneratorRaisesPfil
import Theorems.Thm_Formalism_REAL_arr_finset_sum_apply
import Theorems.Thm_Formalism_REAL_pointwise_operator_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open scoped InnerProductSpace
open Finset
noncomputable section
namespace Formalism.REAL
section U1Pfil
variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (u : V)
end U1Pfil
section U1Arr
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
private theorem arr_add_apply {j : ℕ} (F G : Arr V n j) (α : Fin j → Fin n × Fin n) :
    (F + G) α = F α + G α := rfl
end U1Arr
section U1Arr2
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
end U1Arr2
section U1Arr3
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
end U1Arr3
section U1Arr4
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
end U1Arr4
section U1Theta
variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (u : V)
end U1Theta
end Formalism.REAL
end
end

set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
namespace Formalism.REAL
theorem _root_.solution {j : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (c d : Fin n) (F : Arr V n j)
    (α : Fin j → Fin n × Fin n) : arrE E j c d F α = ∑ i, factorAction i c d F α + E c d (F α) := by
  have h1 : arrE E j c d F = (∑ i : Fin j, factorAction i c d F) + ptE E c d F := by
    show ((∑ i : Fin j, factorAction i c d) + ptE E c d : Module.End ℂ (Arr V n j)) F = _
    rw [LinearMap.add_apply, LinearMap.sum_apply]
  rw [h1, arr_add_apply, arr_finset_sum_apply, pointwise_operator_apply]
end Formalism.REAL
