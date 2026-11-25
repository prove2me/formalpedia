-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qh_equiv_of_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:06:22.500498+00:00
-- url     : https://prove2.me/submissions/f2bbf73c-ce71-4e15-960c-3be60d1bef3b

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhDetZpowMem
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhEquivOfCount

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
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} {R : Type} [CommRing R]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {α β : Type} [Fintype α] [Fintype β] (f : α → ℕ) (g : β → ℕ)
    (hf : ∀ a, 0 < f a) (hg : ∀ b, 0 < g b)
    (h : ∀ t, (univ.filter fun a => t < f a).card = (univ.filter fun b => t < g b).card) :
    ∃ e : α ≃ β, ∀ a, g (e a) = f a := by
  classical
  have hfib : ∀ k : ℕ, (univ.filter fun a => f a = k).card = (univ.filter fun b => g b = k).card := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have h1 : (univ.filter fun a => f a = 0) = ∅ := by
        ext a
        simp [(hf a).ne']
      have h2 : (univ.filter fun b => g b = 0) = ∅ := by
        ext b
        simp [(hg b).ne']
      rw [h1, h2, Finset.card_empty, Finset.card_empty]
    · have key : ∀ {γ : Type} [Fintype γ] (u : γ → ℕ), (univ.filter fun x => u x = k).card
          = (univ.filter fun x => k - 1 < u x).card - (univ.filter fun x => k < u x).card := by
        intro γ _ u
        have hsplit : (univ.filter fun x => k - 1 < u x) =
            (univ.filter fun x => u x = k) ∪ (univ.filter fun x => k < u x) := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
          constructor
          · intro hx
            omega
          · intro hx
            omega
        have hdisj : Disjoint (univ.filter fun x => u x = k) (univ.filter fun x => k < u x) := by
          rw [Finset.disjoint_filter]
          intro x _ hx
          omega
        rw [hsplit, Finset.card_union_of_disjoint hdisj]
        omega
      rw [key f, key g, h (k - 1), h k]
  have hcard : ∀ k : ℕ, Fintype.card {a // f a = k} = Fintype.card {b // g b = k} := by
    intro k
    first
      | (rw [Fintype.card_subtype, Fintype.card_subtype]; exact hfib k)
      | simpa [Fintype.card_subtype] using hfib k
  let e : α ≃ β := (Equiv.sigmaFiberEquiv f).symm.trans
    ((Equiv.sigmaCongrRight fun k => Fintype.equivOfCardEq (hcard k)).trans (Equiv.sigmaFiberEquiv g))
  refine ⟨e, fun a => ?_⟩
  exact (Fintype.equivOfCardEq (hcard (f a)) ⟨a, rfl⟩).2
end Formalism.InvariantFactorPaths.ColumnFamilies
