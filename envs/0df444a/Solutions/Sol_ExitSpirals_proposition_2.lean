-- Prove2me | solution 1 for ExitSpirals.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:56:13.999204+00:00
-- url     : https://prove2.me/submissions/d3b17b31-0f65-4469-824c-042051dbef14

import Mathlib
import Definitions.Def_ExitSpirals_Network
import Definitions.Def_ExitSpirals_IsMutuallyStable
import Definitions.Def_ExitSpirals_activity

namespace Aux_ESp2

open ExitSpirals

theorem mem_BR {n : ℕ} (ER EC : Network n) (W A : Finset (Fin n)) (i : Fin n) :
    i ∈ bestResponse ER EC W A ↔
      i ∉ W ∧ (∃ j ∈ A, (j, i) ∈ ER) ∧ (∃ j ∈ A, (j, i) ∈ EC) := by
  simp [bestResponse]

theorem mem_strip {n : ℕ} (E : Network n) (W : Finset (Fin n)) (j i : Fin n) :
    (j, i) ∈ strip E W ↔ (j, i) ∈ E ∧ j ∉ W ∧ i ∉ W := by
  simp [strip]

theorem mem_maxEq {n : ℕ} (ER EC : Network n) (W : Finset (Fin n)) (i : Fin n) :
    i ∈ maxEq ER EC W ↔ ∃ A : Finset (Fin n), IsEquilibrium ER EC W A ∧ i ∈ A := by
  simp [maxEq]

theorem mono {n : ℕ} (ER EC : Network n) (W A A' : Finset (Fin n)) (h : A ⊆ A') :
    bestResponse ER EC W A ⊆ bestResponse ER EC W A' := by
  intro i hi
  rw [mem_BR] at hi ⊢
  obtain ⟨hW, ⟨j, hj, hjr⟩, ⟨k, hk, hkc⟩⟩ := hi
  exact ⟨hW, ⟨j, h hj, hjr⟩, ⟨k, h hk, hkc⟩⟩

theorem key {n : ℕ} (ER EC : Network n) (W : Finset (Fin n)) :
    IsEquilibrium ER EC W (maxEq ER EC W) ∧
      ∀ V : Finset (Fin n), V ⊆ bestResponse ER EC W V → V ⊆ maxEq ER EC W := by
  classical
  let U : Finset (Fin n) := Finset.univ.filter fun i =>
    ∃ V : Finset (Fin n), V ⊆ bestResponse ER EC W V ∧ i ∈ V
  have hsub : ∀ V : Finset (Fin n), V ⊆ bestResponse ER EC W V → V ⊆ U := by
    intro V hV i hi
    simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨V, hV, hi⟩
  have hU1 : U ⊆ bestResponse ER EC W U := by
    intro i hi
    simp only [U, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨V, hV, hiV⟩ := hi
    exact mono ER EC W V U (hsub V hV) (hV hiV)
  have hU2 : bestResponse ER EC W U ⊆ U := hsub _ (mono ER EC W _ _ hU1)
  have hUeq : IsEquilibrium ER EC W U := Finset.Subset.antisymm hU2 hU1
  have hMU : maxEq ER EC W = U := by
    apply Finset.Subset.antisymm
    · intro i hi
      rw [mem_maxEq] at hi
      obtain ⟨A, hA, hiA⟩ := hi
      have hA' : A ⊆ bestResponse ER EC W A := by
        unfold IsEquilibrium at hA; rw [hA]
      exact hsub A hA' hiA
    · intro i hi
      rw [mem_maxEq]
      exact ⟨U, hUeq, hi⟩
  rw [hMU]
  exact ⟨hUeq, hsub⟩

end Aux_ESp2

open ExitSpirals Aux_ESp2 in
theorem solution {n : ℕ} (ER EC : Network n) (hR : IsLoopless ER) (hC : IsLoopless EC)
    (W : Finset (Fin n)) :
    IsEquilibrium ER EC W (maxEq ER EC W) ∧
      IsGreatest {V : Finset (Fin n) | IsMutuallyStable (strip ER W) (strip EC W) V}
        (maxEq ER EC W) := by
  obtain ⟨hEq, hmax⟩ := key ER EC W
  refine ⟨hEq, ⟨?_, ?_⟩⟩
  · have hM : ∀ i ∈ maxEq ER EC W, i ∈ bestResponse ER EC W (maxEq ER EC W) := by
      intro i hi
      unfold IsEquilibrium at hEq
      rw [hEq]; exact hi
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · obtain ⟨hiW, ⟨j, hj, hjr⟩, -⟩ := (mem_BR _ _ _ _ _).mp (hM i hi)
      obtain ⟨hjW, -, -⟩ := (mem_BR _ _ _ _ _).mp (hM j hj)
      exact ⟨j, hj, (mem_strip _ _ _ _).mpr ⟨hjr, hjW, hiW⟩⟩
    · obtain ⟨hiW, -, ⟨j, hj, hjc⟩⟩ := (mem_BR _ _ _ _ _).mp (hM i hi)
      obtain ⟨hjW, -, -⟩ := (mem_BR _ _ _ _ _).mp (hM j hj)
      exact ⟨j, hj, (mem_strip _ _ _ _).mpr ⟨hjc, hjW, hiW⟩⟩
  · intro V hV
    obtain ⟨hVR, hVC⟩ := hV
    apply hmax V
    intro i hi
    obtain ⟨j, hj, hjr⟩ := hVR i hi
    obtain ⟨k, hk, hkc⟩ := hVC i hi
    rw [mem_strip] at hjr hkc
    exact (mem_BR _ _ _ _ _).mpr ⟨hjr.2.2, ⟨j, hj, hjr.1⟩, ⟨k, hk, hkc.1⟩⟩
