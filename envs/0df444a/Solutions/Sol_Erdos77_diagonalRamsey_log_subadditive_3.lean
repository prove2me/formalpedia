-- Prove2me | solution 3 for Erdos77.diagonalRamsey_log_subadditive
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-09-26T18:04:32.479819+00:00
-- url     : https://prove2.me/submissions/c5b95ddc-ba5e-44fe-9f0c-7dde8ed65607

import Mathlib
import Definitions.Def_Erdos77_diagonal_ramsey

private lemma noNCliqueTwo_of_fin_le_one (n : Nat) (hn : n ≤ 1)
    (G : SimpleGraph (Fin n)) :
    ¬ ∃ s : Finset (Fin n), G.IsNClique 2 s := by
  rintro ⟨s, hs⟩
  rw [SimpleGraph.isNClique_iff] at hs
  have hcard : s.card ≤ (Finset.univ : Finset (Fin n)).card :=
    Finset.card_le_card (Finset.subset_univ s)
  have huniv : (Finset.univ : Finset (Fin n)).card = n := by simp
  omega

private lemma ramseyTwo_on_two (G : SimpleGraph (Fin 2)) :
    (∃ s : Finset (Fin 2), G.IsNClique 2 s) ∨
      (∃ s : Finset (Fin 2), (Compl.compl G).IsNClique 2 s) := by
  by_cases hEdge : G.Adj 0 1
  · left
    refine ⟨Finset.univ, ?_⟩
    rw [SimpleGraph.isNClique_iff]
    constructor
    · intro x hx y hy hxy
      fin_cases x <;> fin_cases y <;>
        first | exact (hxy rfl).elim | exact hEdge | exact SimpleGraph.Adj.symm hEdge
    · simp
  · right
    refine ⟨Finset.univ, ?_⟩
    rw [SimpleGraph.isNClique_iff]
    constructor
    · intro x hx y hy hxy
      rw [SimpleGraph.compl_adj]
      fin_cases x <;> fin_cases y <;>
        first
        | exact (hxy rfl).elim
        | exact ⟨by decide, hEdge⟩
        | exact ⟨by decide, fun h => hEdge (SimpleGraph.Adj.symm h)⟩
    · simp

theorem solution :
    ¬ (And (Subadditive (fun k : Nat => Real.log (Erdos77.diagonalRamsey k : Real)))
      (And (∀ k : Nat, 0 ≤ Real.log (Erdos77.diagonalRamsey k : Real))
        (∃ N : Nat, ∀ k : Nat, N ≤ k →
          0 < (Erdos77.diagonalRamsey k : Real)))) := by
  rintro ⟨hsub, hnonneg, hpos⟩
  have hR1upper : Erdos77.diagonalRamsey 1 ≤ 1 := by
    unfold Erdos77.diagonalRamsey
    apply Nat.sInf_le
    intro G
    left
    refine ⟨Finset.univ, ?_⟩
    rw [SimpleGraph.isNClique_iff]
    constructor
    · intro x hx y hy hxy
      exact (hxy (Subsingleton.elim x y)).elim
    · simp
  let P2 : Set Nat := fun N => ∀ G : SimpleGraph (Fin N),
    (∃ s : Finset (Fin N), G.IsNClique 2 s) ∨
      (∃ s : Finset (Fin N), (Compl.compl G).IsNClique 2 s)
  have hP2 : P2.Nonempty := ⟨2, fun G => ramseyTwo_on_two G⟩
  have hR2prop : P2 (Erdos77.diagonalRamsey 2) := by
    exact Nat.sInf_mem hP2
  have hR2lower : 2 ≤ Erdos77.diagonalRamsey 2 := by
    by_contra hsmall
    have hle : Erdos77.diagonalRamsey 2 ≤ 1 := by omega
    have hbad : ¬ P2 (Erdos77.diagonalRamsey 2) := by
      intro hP
      let G : SimpleGraph (Fin (Erdos77.diagonalRamsey 2)) :=
        SimpleGraph.emptyGraph (Fin (Erdos77.diagonalRamsey 2))
      rcases hP G with hs | hs
      · exact (noNCliqueTwo_of_fin_le_one _ hle G) hs
      · exact (noNCliqueTwo_of_fin_le_one _ hle (Compl.compl G)) hs
    exact hbad hR2prop
  have hR1log : Real.log (Erdos77.diagonalRamsey 1 : Real) = 0 := by
    have hn : (Erdos77.diagonalRamsey 1 : Real) ≤ 1 := by exact_mod_cast hR1upper
    by_cases hz : Erdos77.diagonalRamsey 1 = 0
    · simp [hz]
    · have hnat : Erdos77.diagonalRamsey 1 = 1 := by omega
      simp [hnat]
  have hR2log : Real.log 2 ≤ Real.log (Erdos77.diagonalRamsey 2 : Real) := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast hR2lower
  have hsub12 := hsub 1 1
  have hR2upper : Real.log (Erdos77.diagonalRamsey 2 : Real) ≤ 0 := by
    simpa [hR1log] using hsub12
  have : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith
