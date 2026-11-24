-- Prove2me | solution 1 for Formalism.G0.TypeIIDownP.codimCount
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:23:40.081258+00:00
-- url     : https://prove2.me/submissions/5e57f027-0f7a-4d11-9563-b8b4030f19e3

import Definitions.Def_Formalism_SubspaceCounting_StatementB
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_QVandermonde
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_SubspaceCount
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TypeIIDown
import Theorems.Thm_Formalism_G0_TypeIIDownP_gb_symm
import Theorems.Thm_Formalism_G0_QVandermondeP_gb_eq_zero
import Theorems.Thm_Formalism_G0_SubspaceCountP_gb_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.G0
open Formalism.G0.TypeIIDownP
open QVandermondeP
namespace Formalism.G0.TypeIIDownP
theorem _root_.solution (hS : SubspaceCount) {F W : Type} [Field F] [Fintype F] [AddCommGroup W]
    [Module F W] [Finite W] (n j : ℕ) (hn : Module.finrank F W = n) :
    Nat.card {V : Submodule F W // Module.finrank F V + j = n} =
      gaussBinom (Fintype.card F) n j := by
  have h : Formalism.G0.countBelow (⊤ : Submodule F W) (n - j) =
      gaussBinom (Fintype.card F) (Module.finrank F W) (n - j) := hS (n - j)
  unfold Formalism.G0.countBelow at h
  rw [hn] at h
  by_cases hj : j ≤ n
  · have e : Nat.card {V : Submodule F W // Module.finrank F V + j = n} =
        Nat.card {U : Submodule F W // U ≤ ⊤ ∧ Module.finrank F U = n - j} :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun V => by
        simp only [le_top, true_and]
        constructor <;> intro h' <;> omega))
    rw [e, h]
    have hs := gb_symm (Fintype.card F) (n - j) j
    rw [Nat.sub_add_cancel hj] at hs
    exact hs
  · have : IsEmpty {V : Submodule F W // Module.finrank F V + j = n} :=
      ⟨fun V => hj (by have := V.2; omega)⟩
    rw [Nat.card_of_isEmpty, Formalism.G0.QVandermondeP.gb_eq_zero _ n j (by omega)]
end Formalism.G0.TypeIIDownP
