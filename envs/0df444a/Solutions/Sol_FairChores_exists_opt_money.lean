-- Prove2me | solution 1 for FairChores.exists_opt_money
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:26:28.4582+00:00
-- url     : https://prove2.me/submissions/c0171895-5b60-4788-9781-cdba3450d942

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresMMSPartition
import Theorems.Thm_FairChores_maxCostData_mono
import Theorems.Thm_FairChores_exists_shrink
import Theorems.Thm_FairChores_cbarSum_empty
attribute [local simp] FairChores.cbarSum_empty


section
open scoped BigOperators
namespace FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
private lemma continuous_iSup_add (K : Fin n → ℝ) :
    Continuous (fun m : Fin n → ℝ => ⨆ j, K j + m j) := by
  cases n with
  | zero => simpa using (continuous_const : Continuous (fun _ : Fin 0 → ℝ => (0 : ℝ)))
  | succ k =>
    haveI : Nonempty (Fin (k + 1)) := ⟨0⟩
    have heq : (fun m : Fin (k + 1) → ℝ => ⨆ j, K j + m j)
        = Finset.univ.sup' Finset.univ_nonempty
            (fun (j : Fin (k + 1)) (m : Fin (k + 1) → ℝ) => K j + m j) := by
      funext m
      rw [Finset.sup'_apply (f := fun (j : Fin (k + 1)) (m : Fin (k + 1) → ℝ) => K j + m j)]
      rw [Finset.sup'_univ_eq_ciSup]
    rw [heq]
    exact Continuous.finset_sup' Finset.univ_nonempty
      (fun j _ => continuous_const.add (continuous_apply j))
end FairChores
end

set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
omit [DecidableEq T]
namespace FairChores
theorem _root_.solution (c p : T → ℝ) (hp : ∀ t, 0 ≤ p t) (hn : 0 < n)
    (assign : T → Option (Fin n)) :
    ∃ m : Fin n → ℝ, (∀ j, 0 ≤ m j) ∧ (billOf p assign ≤ ∑ j, m j) ∧
      ∀ m', (∀ j, 0 ≤ m' j) → (billOf p assign ≤ ∑ j, m' j) →
        maxCostData c assign m ≤ maxCostData c assign m' := by
  classical
  set B := billOf p assign with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg (fun t _ => hp t)
  set K : Set (Fin n → ℝ) := {m | (∀ j, 0 ≤ m j) ∧ ∑ j, m j = B} with hK
  have hKcomp : IsCompact K := by
    apply IsCompact.of_isClosed_subset (isCompact_Icc (a := (0 : Fin n → ℝ)) (b := fun _ => B))
    · have h1 : IsClosed {m : Fin n → ℝ | ∀ j, 0 ≤ m j} := by
        have he : {m : Fin n → ℝ | ∀ j, 0 ≤ m j} = ⋂ j, {m : Fin n → ℝ | 0 ≤ m j} := by
          ext m; simp
        rw [he]; exact isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)
      have h2 : IsClosed {m : Fin n → ℝ | ∑ j, m j = B} :=
        isClosed_eq (continuous_finset_sum _ fun j _ => continuous_apply j) continuous_const
      exact h1.inter h2
    · intro m hm
      obtain ⟨hnn, hsum⟩ := hm
      simp only [Set.mem_Icc]
      refine ⟨fun j => hnn j, fun j => ?_⟩
      calc m j ≤ ∑ i, m i := Finset.single_le_sum (fun i _ => hnn i) (Finset.mem_univ j)
        _ = B := hsum
  have hKne : K.Nonempty := by
    refine ⟨fun j => if j = ⟨0, hn⟩ then B else 0, fun j => ?_, ?_⟩
    · by_cases hj : j = ⟨0, hn⟩ <;> simp [hj, hB0]
    · simp
  have hcont : Continuous (fun m : Fin n → ℝ => maxCostData c assign m) :=
    continuous_iSup_add (keptCost c assign)
  obtain ⟨m, hmK, hmin⟩ := hKcomp.exists_isMinOn hKne hcont.continuousOn
  refine ⟨m, hmK.1, le_of_eq hmK.2.symm, ?_⟩
  intro m' h0 hs
  obtain ⟨m'', h0'', hle'', hsum''⟩ := exists_shrink hB0 m' h0 hs
  calc maxCostData c assign m ≤ maxCostData c assign m'' :=
        hmin (show m'' ∈ K from ⟨h0'', hsum''⟩)
    _ ≤ maxCostData c assign m' := maxCostData_mono c assign hle''
end FairChores
