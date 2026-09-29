-- Prove2me | solution 1 for Erdos77.diagonalRamsey_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T13:05:26.659727+00:00
-- url     : https://prove2.me/submissions/efe090a0-b313-4235-afdc-10c98b9ae932

import Mathlib
import Definitions.Def_Erdos77_diagonal_ramsey
import Theorems.Thm_Erdos77_finite_asymmetric_ramsey

theorem solution (k : Nat) (hk : 0 < k) :
    1 ≤ Erdos77.diagonalRamsey k := by
  unfold Erdos77.diagonalRamsey
  have hnonempty :
      {n : Nat | ∀ G : SimpleGraph (Fin n),
        (∃ s : Finset (Fin n), G.IsNClique k s) ∨
        (∃ s : Finset (Fin n), Gᶜ.IsNClique k s)}.Nonempty := by
    rcases Erdos77.finite_asymmetric_ramsey k k (by omega) (by omega) with
      ⟨n, hn⟩
    refine ⟨n, ?_⟩
    intro G
    rcases hn G with h | h
    · rcases h with ⟨s, hs, hclique⟩
      exact Or.inl ⟨s, ⟨hclique, hs⟩⟩
    · rcases h with ⟨s, hs, hclique⟩
      exact Or.inr ⟨s, ⟨hclique, hs⟩⟩
  have hmin := Nat.sInf_mem hnonempty
  have hmin_pos : 0 < sInf {n : Nat | ∀ G : SimpleGraph (Fin n),
        (∃ s : Finset (Fin n), G.IsNClique k s) ∨
        (∃ s : Finset (Fin n), Gᶜ.IsNClique k s)} := by
    by_contra h
    have hz : sInf {n : Nat | ∀ G : SimpleGraph (Fin n),
        (∃ s : Finset (Fin n), G.IsNClique k s) ∨
        (∃ s : Finset (Fin n), Gᶜ.IsNClique k s)} = 0 := by omega
    rw [hz] at hmin
    change ∀ G : SimpleGraph (Fin 0),
        (∃ s : Finset (Fin 0), G.IsNClique k s) ∨
        (∃ s : Finset (Fin 0), Gᶜ.IsNClique k s) at hmin
    have hbad := hmin ⊥
    rcases hbad with ⟨s, hs⟩ | ⟨s, hs⟩
    · rcases hs with ⟨_, hcard⟩
      have hcard0 : s.card = 0 := by
        have hle : s.card ≤ (Finset.univ : Finset (Fin 0)).card :=
          Finset.card_le_card (Finset.subset_univ s)
        have huniv : (Finset.univ : Finset (Fin 0)).card = 0 := by simp
        omega
      omega
    · rcases hs with ⟨_, hcard⟩
      have hcard0 : s.card = 0 := by
        have hle : s.card ≤ (Finset.univ : Finset (Fin 0)).card :=
          Finset.card_le_card (Finset.subset_univ s)
        have huniv : (Finset.univ : Finset (Fin 0)).card = 0 := by simp
        omega
      omega
  omega

