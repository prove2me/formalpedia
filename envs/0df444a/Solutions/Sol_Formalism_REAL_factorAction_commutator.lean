-- Prove2me | solution 1 for Formalism.REAL.factorAction_commutator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:34:57.17539+00:00
-- url     : https://prove2.me/submissions/e8093097-3afe-4177-8c87-0577c8afbadc

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactGeneratorRaisesPfil
import Theorems.Thm_P2M_Formalism_REAL_factorAction_apply__702f0fa4e7c4
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
end U1Arr
section U1Arr2
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
private theorem arr_ext {j : ℕ} {F G : Arr V n j} (h : ∀ α, F α = G α) : F = G := by
  first
  | exact PiLp.ext h
  | exact (WithLp.linearEquiv 2 ℂ ((Fin j → Fin n × Fin n) → V)).injective (funext h)
  | exact funext h
private theorem arr_sub_apply {j : ℕ} (F G : Arr V n j) (α : Fin j → Fin n × Fin n) :
    (F - G) α = F α - G α := rfl
private theorem arr_zero_apply {j : ℕ} (α : Fin j → Fin n × Fin n) :
    (0 : Arr V n j) α = 0 := rfl
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
theorem _root_.solution {j : ℕ} (i : Fin j) (a b c d : Fin n) :
    (factorAction i a b * factorAction i c d - factorAction i c d * factorAction i a b : Module.End ℂ (Arr V n j)) =
      (if b = c then factorAction i a d else 0) - (if d = a then factorAction i c b else 0) := by
  apply LinearMap.ext; intro F
  apply arr_ext; intro α
  show factorAction i a b (factorAction i c d F) α - factorAction i c d (factorAction i a b F) α = _
  split_ifs <;> simp [arr_sub_apply, arr_zero_apply, factorAction_apply'] <;> (try split_ifs) <;>
    first | abel1 | (simp_all; done) | (simp_all; abel1) | (subst_vars; abel1) | (subst_vars; simp_all)
end Formalism.REAL
