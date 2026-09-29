-- Prove2me | solution 2 for Erdos77.finite_asymmetric_ramsey
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T11:59:43.596916+00:00
-- url     : https://prove2.me/submissions/5e9fc278-ba97-402f-a754-4e8e8c524bc7

import Mathlib
import Theorems.Thm_Erdos77_finite_asymmetric_ramsey_step

theorem solution (r s : Nat) (hr : 1 <= r) (hs : 1 <= s) :
    Exists fun n : Nat => forall G : SimpleGraph (Fin n),
      Or
        (Exists fun t : Finset (Fin n) => And (t.card = r) (G.IsClique t))
        (Exists fun t : Finset (Fin n) => And (t.card = s) ((Compl.compl G).IsClique t)) := by
  let Ramsey := fun (a b : Nat) =>
    Exists fun n : Nat => forall G : SimpleGraph (Fin n),
      Or
        (Exists fun t : Finset (Fin n) => And (t.card = a) (G.IsClique t))
        (Exists fun t : Finset (Fin n) => And (t.card = b) ((Compl.compl G).IsClique t))
  have hmain : ∀ k a b, a + b = k → 1 <= a → 1 <= b → Ramsey a b := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro a b hab ha hb
      by_cases hbase₁ : a = 1
      · subst a
        refine ⟨1, ?_⟩
        intro G
        left
        refine ⟨Finset.univ, ?_, ?_⟩
        · simp
        · intro x hx y hy hxy
          exact (hxy (Subsingleton.elim x y)).elim
      by_cases hbase₂ : b = 1
      · subst b
        refine ⟨1, ?_⟩
        intro G
        right
        refine ⟨Finset.univ, ?_, ?_⟩
        · simp
        · intro x hx y hy hxy
          exact (hxy (Subsingleton.elim x y)).elim
      have ha' : 1 < a := by omega
      have hb' : 1 < b := by omega
      have h₁ : Ramsey (a - 1) b := by
        exact ih (a + b - 1) (by omega) (a - 1) b (by omega) (by omega) hb
      have h₂ : Ramsey a (b - 1) := by
        exact ih (a + b - 1) (by omega) a (b - 1) (by omega) ha (by omega)
      rcases h₁ with ⟨n₁, hn₁⟩
      rcases h₂ with ⟨n₂, hn₂⟩
      exact Erdos77.finite_asymmetric_ramsey_step a b ha' hb' ⟨n₁, hn₁⟩ ⟨n₂, hn₂⟩
  exact hmain (r + s) r s rfl hr hs
