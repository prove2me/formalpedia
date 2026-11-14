-- Prove2me | solution 1 for DvorakNorin2018.balanced_separators_treewidth
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-13T18:28:50.763635+00:00
-- url     : https://prove2.me/submissions/7f5fd62b-a87f-4f68-afa2-2762739fd4ff

import Theorems.Thm_DvorakNorin2018_haven_order_bound
import Theorems.Thm_SeymourThomas1993_haven_of_not_treewidth_le
set_option autoImplicit false
namespace StableMSR.Recovery.Havens
open TreewidthApprox.Pushed RobertsonSeymour1986.GM5

lemma balanced_separation_parameter_positive {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : SimpleGraph V} {a : ℕ} (hsep : HasBalancedSeparations G a) : 1 ≤ a := by
  classical
  let v : V := Classical.choice inferInstance
  obtain ⟨L,S,R,hpart,_,hS,hL,hR⟩ := hsep {v}
  have hc : L.card + S.card + R.card = 1 := by
    have he := congrArg Finset.card hpart.2.2.2
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hpart.2.1,hpart.2.2.1⟩),
      Finset.card_union_of_disjoint hpart.1,Finset.card_singleton] at he
    exact he
  simp only [Finset.card_singleton] at hL hR
  omega

lemma treewidthLE_empty {V : Type} [DecidableEq V] [IsEmpty V] (G : SimpleGraph V) (w : ℕ) :
    TreewidthLE G w := by
  refine ⟨Unit,inferInstance,⊥,fun _ => ∅,?_,?_⟩
  · refine ⟨SimpleGraph.IsTree.of_subsingleton,?_,?_,?_⟩
    · intro v; exact isEmptyElim v
    · intro x; exact isEmptyElim x
    · intro s s' s'' p hp hs; simp
  · intro s; simp

/-- The remaining source theorem is isolated as an explicit hypothesis, not an axiom. -/
theorem treewidth_bound_of_haven_duality {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (a : ℕ) (hsep : HasBalancedSeparations G a)
    (hdual : ∀ w : ℕ, ¬ TreewidthLE G w → ∃ β : Finset V → Finset V, Haven G (w+2) β) :
    TreewidthLE G (15*a) := by
  classical
  cases isEmpty_or_nonempty V with
  | inl he =>
    letI := he
    exact treewidthLE_empty G (15*a)
  | inr hn =>
    letI := hn
    have ha := balanced_separation_parameter_positive hsep
    by_contra hwidth
    obtain ⟨β,hβ⟩ := hdual (15*a) hwidth
    have hbound := DvorakNorin2018.haven_order_bound hβ hsep ha
    omega
end StableMSR.Recovery.Havens

open StableMSR.Recovery.Havens RobertsonSeymour1986.GM5
theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (a : ℕ) (hsep : HasBalancedSeparations G a) :
    TreewidthLE G (15*a) := by
  exact treewidth_bound_of_haven_duality G a hsep (fun w hw =>
    SeymourThomas1993.haven_of_not_treewidth_le G w hw)
