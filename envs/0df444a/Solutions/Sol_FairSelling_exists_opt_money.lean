-- Prove2me | solution 1 for FairSelling.exists_opt_money
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:27:58.535883+00:00
-- url     : https://prove2.me/submissions/c7ac43e3-e109-41ac-a09b-0aad3a82d194

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
section
open scoped BigOperators
namespace FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
private lemma continuous_iInf_add (c : Fin n → ℝ) :
    Continuous (fun m : Fin n → ℝ => ⨅ j, c j + m j) := by
  cases n with
  | zero => simpa using (continuous_const : Continuous (fun _ : Fin 0 → ℝ => (0 : ℝ)))
  | succ k =>
    haveI : Nonempty (Fin (k + 1)) := ⟨0⟩
    have heq : (fun m : Fin (k + 1) → ℝ => ⨅ j, c j + m j)
        = Finset.univ.inf' Finset.univ_nonempty
            (fun (j : Fin (k + 1)) (m : Fin (k + 1) → ℝ) => c j + m j) := by
      funext m
      rw [Finset.inf'_apply (f := fun (j : Fin (k + 1)) (m : Fin (k + 1) → ℝ) => c j + m j)]
      rw [Finset.inf'_univ_eq_ciInf]
    rw [heq]
    exact Continuous.finset_inf' Finset.univ_nonempty
      (fun j _ => continuous_const.add (continuous_apply j))
end FairSelling
end

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
omit [DecidableEq G]
namespace FairSelling
theorem _root_.solution (v p : G → ℝ) (hp : ∀ g, 0 ≤ p g) (assign : G → Option (Fin n)) :
    ∃ m : Fin n → ℝ, (∀ j, 0 ≤ m j) ∧ (∑ j, m j ≤ procOf p assign) ∧
      ∀ m', (∀ j, 0 ≤ m' j) → (∑ j, m' j ≤ procOf p assign) →
        minUtilData v assign m' ≤ minUtilData v assign m := by
  set P := procOf p assign with hP
  have hP0 : 0 ≤ P := Finset.sum_nonneg (fun g _ => hp g)
  set K : Set (Fin n → ℝ) := {m | (∀ j, 0 ≤ m j) ∧ ∑ j, m j ≤ P} with hK
  have hKcomp : IsCompact K := by
    apply IsCompact.of_isClosed_subset (isCompact_Icc (a := (0 : Fin n → ℝ)) (b := fun _ => P))
    · have h1 : IsClosed {m : Fin n → ℝ | ∀ j, 0 ≤ m j} := by
        have he : {m : Fin n → ℝ | ∀ j, 0 ≤ m j} = ⋂ j, {m : Fin n → ℝ | 0 ≤ m j} := by
          ext m; simp
        rw [he]; exact isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)
      have h2 : IsClosed {m : Fin n → ℝ | ∑ j, m j ≤ P} :=
        isClosed_le (continuous_finset_sum _ fun j _ => continuous_apply j) continuous_const
      exact h1.inter h2
    · intro m hm
      obtain ⟨hnn, hsum⟩ := hm
      simp only [Set.mem_Icc]
      refine ⟨fun j => hnn j, fun j => ?_⟩
      calc m j ≤ ∑ i, m i := Finset.single_le_sum (fun i _ => hnn i) (Finset.mem_univ j)
        _ ≤ P := hsum
  have hKne : K.Nonempty := ⟨0, ⟨fun j => le_refl 0, by simpa using hP0⟩⟩
  have hcont : Continuous (fun m : Fin n → ℝ => minUtilData v assign m) :=
    continuous_iInf_add (keptVal v assign)
  obtain ⟨m, hmK, hmax⟩ := hKcomp.exists_isMaxOn hKne hcont.continuousOn
  exact ⟨m, hmK.1, hmK.2, fun m' h0 hs => hmax (show m' ∈ K from ⟨h0, hs⟩)⟩
end FairSelling
