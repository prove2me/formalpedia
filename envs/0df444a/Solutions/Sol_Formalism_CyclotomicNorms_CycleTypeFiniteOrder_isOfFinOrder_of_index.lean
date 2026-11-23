-- Prove2me | solution 1 for Formalism.CyclotomicNorms.CycleTypeFiniteOrder.isOfFinOrder_of_index
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:54:18.103808+00:00
-- url     : https://prove2.me/submissions/f7f1c1a9-9108-4c94-b6e9-1602cc15f6bf

import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive
import Definitions.Def_Lemmata_GeneralBFactSecondBis_Imports
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_IrreducibilityOfRestriction
import Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_iter_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.CyclotomicNorms Formalism.CyclotomicNorms.CycleTypeFiniteOrder
variable {g : ℕ} [hg : Fact g.Prime]
variable {N : ℕ} {f : (ZMod g)[X]}
variable {r : Fin N → Fbar g} {σ : Equiv.Perm (Fin N)}
namespace Formalism.CyclotomicNorms.CycleTypeFiniteOrder
theorem _root_.solution (hσ : ∀ i, r (σ i) = r i ^ g) (i : Fin N) (h0 : r i ≠ 0) :
    IsOfFinOrder (r i) := by
  have hM := orderOf_pos σ
  have h1 := iter_eq hσ (orderOf σ) i
  rw [pow_orderOf_eq_one, Equiv.Perm.one_apply] at h1
  have h2 : 2 ≤ g ^ orderOf σ := by
    calc 2 ≤ g := hg.out.two_le
      _ = g ^ 1 := (pow_one g).symm
      _ ≤ g ^ orderOf σ := Nat.pow_le_pow_right hg.out.pos hM
  rw [isOfFinOrder_iff_pow_eq_one]
  refine ⟨g ^ orderOf σ - 1, by omega, ?_⟩
  apply mul_right_cancel₀ h0
  rw [← pow_succ, Nat.sub_add_cancel (by omega), one_mul, ← h1]
end Formalism.CyclotomicNorms.CycleTypeFiniteOrder
