-- Prove2me | solution 1 for ConsistentSubmodular.WindowSamples.toRounded
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:37:08.181361+00:00
-- url     : https://prove2.me/submissions/63af0761-cb9c-45ae-8b0c-4a9ab859d466

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_RoundedWindow
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_WindowSamples
import Theorems.Thm_ConsistentSubmodular_SetOperationPath_exists_insertion_path
import Theorems.Thm_ConsistentSubmodular_SetOperationPath_exists_chain_fin

section

noncomputable section

namespace ConsistentSubmodular

namespace SetOperationPath

variable {n : ℕ} (P : SetOperationPath n)

theorem append_property (Q : SetOperationPath n) (hjoin)
    (good : Finset (Fin n) → Prop) (hP : ∀ i, good (P.node i))
    (hQ : ∀ i, good (Q.node i)) : ∀ i, good ((P.append Q hjoin).node i) := by
  intro i
  change good (if i ≤ P.length then P.node i else Q.node (i - P.length))
  split
  · exact hP i
  · exact hQ _

end SetOperationPath

end ConsistentSubmodular

end

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

namespace SetOperationPath

variable {n : ℕ}

theorem prepend_forced (P : SetOperationPath n) (A D U : Finset (Fin n))
    (B : ℕ) (good : Finset (Fin n) → Prop)
    (hmono : ∀ S T, S ⊆ T → good S → good T)
    (hstart : P.node 0 = D ∪ A) (hA : good A)
    (hAU : A ⊆ U) (hDU : D ⊆ U) (hcard : A.card + D.card ≤ B)
    (hP : ∀ i, P.node i ⊆ U ∧ (P.node i).card ≤ B ∧ good (P.node i)) :
    ∃ R : SetOperationPath n,
      R.length = D.card + P.length ∧ R.node 0 = A ∧
      R.node R.length = P.node P.length ∧
      ∀ i, R.node i ⊆ U ∧ (R.node i).card ≤ B ∧ good (R.node i) := by
  obtain ⟨L, hLlen, hLinit, hLterm, hLnode⟩ := exists_insertion_path A D
  have hj : L.node L.length = P.node 0 := by rw [hLterm, hstart, Finset.union_comm]
  refine ⟨L.append P hj, by simp [hLlen], by simpa using hLinit, ?_, ?_⟩
  · exact L.append_terminal P hj
  · apply L.append_property P hj (fun S => S ⊆ U ∧ S.card ≤ B ∧ good S) _ hP
    intro i
    exact ⟨(hLnode i).2.trans (Finset.union_subset hAU hDU),
      (Finset.card_le_card (hLnode i).2).trans ((Finset.card_union_le _ _).trans hcard),
      hmono _ _ (hLnode i).1 hA⟩

theorem append_unforced (P : SetOperationPath n) (A D U : Finset (Fin n))
    (B : ℕ) (good : Finset (Fin n) → Prop)
    (hmono : ∀ S T, S ⊆ T → good S → good T)
    (hend : P.node P.length = D ∪ A) (hA : good A)
    (hAU : A ⊆ U) (hDU : D ⊆ U) (hcard : A.card + D.card ≤ B)
    (hP : ∀ i, P.node i ⊆ U ∧ (P.node i).card ≤ B ∧ good (P.node i)) :
    ∃ R : SetOperationPath n,
      R.length = P.length + D.card ∧ R.node 0 = P.node 0 ∧
      R.node R.length = A ∧
      ∀ i, R.node i ⊆ U ∧ (R.node i).card ≤ B ∧ good (R.node i) := by
  obtain ⟨L, hLlen, hLinit, hLterm, hLnode⟩ := exists_insertion_path A D
  have hj : P.node P.length = L.reverse.node 0 := by
    rw [reverse_initial, hLterm, hend, Finset.union_comm]
  refine ⟨P.append L.reverse hj, by simp [reverse, hLlen], by simp, ?_, ?_⟩
  · simpa using (P.append_terminal L.reverse hj).trans ((reverse_terminal L).trans hLinit)
  · apply P.append_property L.reverse hj (fun S => S ⊆ U ∧ S.card ≤ B ∧ good S) hP
    intro i
    exact ⟨(hLnode _).2.trans (Finset.union_subset hAU hDU),
      (Finset.card_le_card (hLnode _).2).trans ((Finset.card_union_le _ _).trans hcard),
      hmono _ _ (hLnode _).1 hA⟩

end SetOperationPath

end ConsistentSubmodular

end

end

section

namespace ConsistentSubmodular

/-- Markov's operation budget and both forced-set endpoint adjustments fit
in one uniform integral length coefficient. -/
theorem window_operation_count (S s κ changes cleanup : ℕ)
    (hs : s ≤ S) (hchanges : changes ≤ 8 * s * κ)
    (hcleanup : cleanup ≤ 2 * κ) :
    changes + cleanup ≤ windowLengthBound S * κ := by
  have hh := Nat.mul_le_mul_right κ (Nat.mul_le_mul_left 8 hs)
  have hextra : 0 ≤ (92 * S + 8) * κ := Nat.zero_le _
  unfold windowLengthBound
  nlinarith

theorem window_uniform_operation_count (S κ changes cleanup : ℕ)
    (hchanges : changes ≤ 8 * S * κ) (hcleanup : cleanup ≤ 2 * κ) :
    changes + cleanup ≤ windowLengthBound S * κ :=
  window_operation_count S S κ changes cleanup le_rfl hchanges hcleanup

end ConsistentSubmodular

end

section

open scoped BigOperators
open ConsistentSubmodular
open ConsistentSubmodular.WindowSamples
variable {n κ N T S H : ℕ} {α : ℝ} {f : Objective n} {old initial terminal : Finset (Fin n)}
  {Q : ℕ → Finset (Fin n)} {hQ : Monotone Q}
  {W : FractionalWindow f old Q hQ κ N T initial terminal α S}
  (Smp : WindowSamples W H)

include Smp in
theorem solution (hκ : H ≤ κ) : Nonempty (RoundedWindow W H (windowLengthBound S)) := by
  classical
  let B := ⌊(κ : ℝ) + (κ : ℝ) / N⌋₊
  let Btotal := B + H
  let β : ℝ := α - 2 / N
  let goodE := fun A => β * f.bufferedOptimum old (Q 0) κ ≤ f.value (Q 0 ∪ A)
  let goodX := fun A => β * f.bufferedOptimum old (Q T) κ ≤ f.value (Q T ∪ A)
  have hmonoE : ∀ A B, A ⊆ B → goodE A → goodE B := by
    intro A B h hA
    exact hA.trans (f.monotone _ _ (Finset.union_subset_union_right h))
  have hmonoX : ∀ A B, A ⊆ B → goodX A → goodX B := by
    intro A B h hA
    exact hA.trans (f.monotone _ _ (Finset.union_subset_union_right h))
  have hsubE : ∀ j, Smp.entry j ⊆ old ∧ (Smp.entry j).card ≤ B :=
    fun j => ⟨Smp.entry_subset j, Nat.le_floor (Smp.entry_card j)⟩
  have hsubX : ∀ j, Smp.exit j ⊆ old ∧ (Smp.exit j).card ≤ B :=
    fun j => ⟨Smp.exit_subset j, Nat.le_floor (Smp.exit_card j)⟩
  obtain ⟨E, hEl, hE0, hE1, hE⟩ := SetOperationPath.exists_chain_fin Smp.entry B old
    (fun A => goodE (Smp.forced ∪ A))
    (fun A B h => hmonoE _ _ (Finset.union_subset_union_right h))
    Smp.entry_first_good hsubE Smp.entry_intersection
  obtain ⟨X, hXl, hX0, hX1, hX⟩ := SetOperationPath.exists_chain_fin Smp.exit B old
    (fun A => goodX (Smp.forced ∪ A))
    (fun A B h => hmonoX _ _ (Finset.union_subset_union_right h))
    Smp.exit_first_good hsubX Smp.exit_intersection
  have hforced := Smp.forced_card.le
  have hκB : κ ≤ B := Nat.le_floor (by
    have : 0 ≤ (κ : ℝ) / N := by positivity
    linarith)
  have hinitcard : initial.card ≤ κ := by simpa only [W.core_initial] using W.core_card 0
  have htermcard : terminal.card ≤ κ := by
    simpa only [W.core_terminal] using W.core_card (Fin.last (3 * N + 1))
  have hinitold : initial ⊆ old := by simpa only [W.core_initial] using W.core_subset 0
  have htermold : terminal ⊆ old := by
    simpa only [W.core_terminal] using W.core_subset (Fin.last (3 * N + 1))
  have hβ : β ≤ 1 := by
    dsimp [β]
    have : 0 ≤ (2 : ℝ) / N := by positivity
    linarith [W.level_le]
  have hinitgood : goodE initial := by
    have hh := W.retained_optimal 0
    rw [W.retained_initial, W.core_initial] at hh
    dsimp [goodE]
    rw [hh]
    exact mul_le_of_le_one_left (f.bufferedOptimum_nonnegative _ _ _) hβ
  have htermgood : goodX terminal := by
    have hh := W.retained_optimal (Fin.last (3 * N + 1))
    rw [W.retained_terminal, W.core_terminal] at hh
    dsimp [goodX]
    rw [hh]
    exact mul_le_of_le_one_left (f.bufferedOptimum_nonnegative _ _ _) hβ
  have hEF (j : ℕ) : (E.withForced Smp.forced).node j ⊆ old ∧
      ((E.withForced Smp.forced).node j).card ≤ Btotal ∧ goodE ((E.withForced Smp.forced).node j) := by
    refine ⟨Finset.union_subset Smp.forced_subset (hE j).1, ?_, (hE j).2.2⟩
    exact (Finset.card_union_le _ _).trans (by dsimp [Btotal]; have := (hE j).2.1; omega)
  have hXF (j : ℕ) : (X.withForced Smp.forced).node j ⊆ old ∧
      ((X.withForced Smp.forced).node j).card ≤ Btotal ∧ goodX ((X.withForced Smp.forced).node j) := by
    refine ⟨Finset.union_subset Smp.forced_subset (hX j).1, ?_, (hX j).2.2⟩
    exact (Finset.card_union_le _ _).trans (by dsimp [Btotal]; have := (hX j).2.1; omega)
  obtain ⟨entry, hel, he0, he1, henode⟩ := (E.withForced Smp.forced).prepend_forced
    initial Smp.forced old Btotal goodE hmonoE
    (by change Smp.forced ∪ E.node 0 = _; rw [hE0, Smp.entry_initial]) hinitgood
    hinitold Smp.forced_subset (by dsimp [Btotal]; omega) hEF
  obtain ⟨exit, hxl, hx0, hx1, hxnode⟩ := (X.withForced Smp.forced).append_unforced
    terminal Smp.forced old Btotal goodX hmonoX
    (by change Smp.forced ∪ X.node X.length = _; rw [hX1, Smp.exit_terminal]) htermgood
    htermold Smp.forced_subset (by dsimp [Btotal]; omega) hXF
  have hcard (A : Finset (Fin n)) (hA : A.card ≤ Btotal) :
      (A.card : ℝ) ≤ (κ : ℝ) + (κ : ℝ) / N + H := by
    have hb : (B : ℝ) ≤ (κ : ℝ) + (κ : ℝ) / N := Nat.floor_le (by positivity)
    have ha : (A.card : ℝ) ≤ (B : ℝ) + H := by exact_mod_cast hA
    linarith
  refine ⟨{
    entry := entry
    exit := exit
    entry_initial := he0
    join := ?_
    exit_terminal := hx1
    length := ?_
    entry_subset := fun j => (henode j).1
    exit_subset := fun j => (hxnode j).1
    entry_card := fun j => hcard _ (henode j).2.1
    exit_card := fun j => hcard _ (hxnode j).2.1
    entry_good := fun j => (henode j).2.2
    exit_good := fun j => (hxnode j).2.2
    checkpoint_tests := ?_ }⟩
  · rw [he1, hx0]
    change Smp.forced ∪ E.node E.length = Smp.forced ∪ X.node 0
    rw [hE1, hX0, Smp.join]
  · have hcost : E.length + X.length ≤ 8 * S * κ := by
      rw [hEl, hXl]
      exact_mod_cast Smp.cost
    have hcleanup : 2 * Smp.forced.card ≤ 2 * κ := by omega
    have hh := window_uniform_operation_count S κ (E.length + X.length)
      (2 * Smp.forced.card) hcost hcleanup
    rw [hel, hxl]
    change Smp.forced.card + E.length + (X.length + Smp.forced.card) ≤ _
    omega
  · intro i
    rw [he1]
    change _ ≤ f.value (Q (W.retained i) ∪ (Smp.forced ∪ E.node E.length))
    rw [hE1]
    exact Smp.checkpoint_tests i

end
