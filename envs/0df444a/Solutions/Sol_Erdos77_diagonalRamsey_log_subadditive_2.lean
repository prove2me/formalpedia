-- Prove2me | solution 2 for Erdos77.diagonalRamsey_log_subadditive
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-09-26T18:03:02.286258+00:00
-- url     : https://prove2.me/submissions/61f367ba-0d17-4f74-87e8-fed17c758198

import Mathlib
import Definitions.Def_Erdos77_diagonal_ramsey

private lemma noNCliqueTwo_of_fin_le_one (n : Nat) (hn : n <= 1)
    (G : SimpleGraph (Fin n)) :
    Not (Exists fun s : Finset (Fin n) => G.IsNClique 2 s) := by
  intro h
  rcases h with ⟨s, hs⟩
  rw [SimpleGraph.isNClique_iff] at hs
  have hcard : s.card <= (Finset.univ : Finset (Fin n)).card :=
    Finset.card_le_card (Finset.subset_univ s)
  have huniv : (Finset.univ : Finset (Fin n)).card = n := by simp
  omega

private lemma noNCliqueOne_fin0 (G : SimpleGraph (Fin 0)) :
    Not (Exists fun s : Finset (Fin 0) => G.IsNClique 1 s) := by
  intro h
  rcases h with ⟨s, hs⟩
  rw [SimpleGraph.isNClique_iff] at hs
  have hcard : s.card <= (Finset.univ : Finset (Fin 0)).card :=
    Finset.card_le_card (Finset.subset_univ s)
  have huniv : (Finset.univ : Finset (Fin 0)).card = 0 := by simp
  omega

private lemma ramseyTwo_on_two (G : SimpleGraph (Fin 2)) :
    Or (Exists fun s : Finset (Fin 2) => G.IsNClique 2 s)
      (Exists fun s : Finset (Fin 2) => (Compl.compl G).IsNClique 2 s) := by
  by_cases hEdge : G.Adj 0 1
  · apply Or.inl
    refine ⟨Finset.univ, ?_⟩
    rw [SimpleGraph.isNClique_iff]
    constructor
    · intro x hx y hy hxy
      fin_cases x <;> fin_cases y <;>
        first | exact (hxy rfl).elim | exact hEdge | exact SimpleGraph.Adj.symm hEdge
    · simp
  · apply Or.inr
    refine ⟨Finset.univ, ?_⟩
    rw [SimpleGraph.isNClique_iff]
    constructor
    · intro x hx y hy hxy
      rw [SimpleGraph.compl_adj]
      fin_cases x <;> fin_cases y <;>
        first
        | exact (hxy rfl).elim
        | exact And.intro (by decide) hEdge
        | exact And.intro (by decide) (fun h => hEdge (SimpleGraph.Adj.symm h))
    · simp

theorem solution :
    Not (And (Subadditive (fun k : Nat => Real.log (Erdos77.diagonalRamsey k : Real)))
      (And (forall k : Nat, 0 <= Real.log (Erdos77.diagonalRamsey k : Real))
        (Exists fun N : Nat => forall k : Nat, N <= k ->
          0 < (Erdos77.diagonalRamsey k : Real)))) := by
  rintro ⟨hsub, _, _⟩

  have hR1upper : Erdos77.diagonalRamsey 1 <= 1 := by
    unfold Erdos77.diagonalRamsey
    apply Nat.sInf_le
    intro G
    apply Or.inl
    refine ⟨Finset.univ, ?_⟩
    rw [SimpleGraph.isNClique_iff]
    constructor
    · intro x hx y hy hxy
      exact (hxy (Subsingleton.elim x y)).elim
    · simp

  let P1 : Set Nat := fun n => forall G : SimpleGraph (Fin n),
    (Exists fun s : Finset (Fin n) => G.IsNClique 1 s) ∨
      (Exists fun s : Finset (Fin n) => (Compl.compl G).IsNClique 1 s)
  have hP1one : P1 1 := by
    intro G
    apply Or.inl
    refine ⟨Finset.univ, ?_⟩
    rw [SimpleGraph.isNClique_iff]
    constructor
    · intro x hx y hy hxy
      exact (hxy (Subsingleton.elim x y)).elim
    · simp
  have hR1lower : 1 <= Erdos77.diagonalRamsey 1 := by
    unfold Erdos77.diagonalRamsey
    have hnonempty : P1.Nonempty := ⟨1, hP1one⟩
    have hmem := Nat.sInf_mem hnonempty
    by_contra hsmall
    change ¬ (1 <= sInf P1) at hsmall
    have hz : sInf P1 = 0 := by omega
    rw [hz] at hmem
    have hbad := hmem (SimpleGraph.emptyGraph (Fin 0))
    rcases hbad with hclique | hclique
    · exact noNCliqueOne_fin0 _ hclique
    · exact noNCliqueOne_fin0 _ hclique

  have hR1 : Erdos77.diagonalRamsey 1 = 1 := by omega

  have hR2lower : 2 <= Erdos77.diagonalRamsey 2 := by
    unfold Erdos77.diagonalRamsey
    let P2 : Set Nat := fun n => forall G : SimpleGraph (Fin n),
      (Exists fun s : Finset (Fin n) => G.IsNClique 2 s) ∨
        (Exists fun s : Finset (Fin n) => (Compl.compl G).IsNClique 2 s)
    have hnonempty : P2.Nonempty := ⟨2, fun G => ramseyTwo_on_two G⟩
    have hmem := Nat.sInf_mem hnonempty
    by_contra hsmall
    change ¬ (2 <= sInf P2) at hsmall
    have hle : sInf P2 <= 1 := by omega
    have hbad : Not (P2 (sInf P2)) := by
      intro hP
      let G : SimpleGraph (Fin (sInf P2)) :=
        SimpleGraph.emptyGraph (Fin (sInf P2))
      cases hP G with
      | inl hs => exact noNCliqueTwo_of_fin_le_one _ hle G hs
      | inr hs => exact noNCliqueTwo_of_fin_le_one _ hle (Compl.compl G) hs
    exact hbad hmem

  have hsubAtOne := hsub 1 1
  have hR2positive : (1 : Real) < (Erdos77.diagonalRamsey 2 : Real) := by
    exact_mod_cast hR2lower
  have hlogR2positive : 0 < Real.log (Erdos77.diagonalRamsey 2 : Real) :=
    Real.log_pos hR2positive
  have hlogR2upper : Real.log (Erdos77.diagonalRamsey 2 : Real) <= 0 := by
    simpa [hR1] using hsubAtOne
  exact (not_lt_of_ge hlogR2upper) hlogR2positive
