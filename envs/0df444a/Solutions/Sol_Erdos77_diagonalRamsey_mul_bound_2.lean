-- Prove2me | solution 2 for Erdos77.diagonalRamsey_mul_bound
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-09-26T16:40:13.517671+00:00
-- url     : https://prove2.me/submissions/23b1b392-929b-438d-9149-fce51588f319

import Mathlib
import Definitions.Def_Erdos77_diagonal_ramsey

private lemma noNCliqueTwo_of_fin_le_one (n : Nat) (hn : n <= 1)
    (G : SimpleGraph (Fin n)) :
    Not (Exists fun s : Finset (Fin n) => G.IsNClique 2 s) := by
  intro h
  cases h with
  | intro s hs =>
    rw [SimpleGraph.isNClique_iff] at hs
    have hcard : s.card <= (Finset.univ : Finset (Fin n)).card :=
      Finset.card_le_card (Finset.subset_univ s)
    have huniv : (Finset.univ : Finset (Fin n)).card = n := by simp
    omega

private lemma ramseyTwo_on_two (G : SimpleGraph (Fin 2)) :
    Or (Exists fun s : Finset (Fin 2) => G.IsNClique 2 s)
      (Exists fun s : Finset (Fin 2) => (Compl.compl G).IsNClique 2 s) := by
  by_cases hEdge : G.Adj 0 1
  case pos =>
    apply Or.inl
    apply Exists.intro Finset.univ
    rw [SimpleGraph.isNClique_iff]
    apply And.intro
    intro x hx y hy hxy
    fin_cases x <;> fin_cases y <;>
      first | exact (hxy rfl).elim | exact hEdge | exact SimpleGraph.Adj.symm hEdge
    simp
  case neg =>
    apply Or.inr
    apply Exists.intro Finset.univ
    rw [SimpleGraph.isNClique_iff]
    apply And.intro
    intro x hx y hy hxy
    rw [SimpleGraph.compl_adj]
    fin_cases x <;> fin_cases y <;>
      first
      | exact (hxy rfl).elim
      | exact And.intro (by decide) hEdge
      | exact And.intro (by decide) (fun h => hEdge (SimpleGraph.Adj.symm h))
    simp

theorem solution : Not (forall m n : Nat, 0 < m -> 0 < n ->
    Erdos77.diagonalRamsey (m + n) <= Erdos77.diagonalRamsey m * Erdos77.diagonalRamsey n) := by
  intro h
  have hR1upper : Erdos77.diagonalRamsey 1 <= 1 := by
    unfold Erdos77.diagonalRamsey
    apply Nat.sInf_le
    intro G
    apply Or.inl
    apply Exists.intro Finset.univ
    rw [SimpleGraph.isNClique_iff]
    apply And.intro
    intro x hx y hy hxy
    exact (hxy (Subsingleton.elim x y)).elim
    simp

  let P2 : Set Nat := fun N => forall G : SimpleGraph (Fin N),
    Or (Exists fun s : Finset (Fin N) => G.IsNClique 2 s)
      (Exists fun s : Finset (Fin N) => (Compl.compl G).IsNClique 2 s)
  have hP2 : P2.Nonempty := by
    apply Exists.intro 2
    intro G
    exact ramseyTwo_on_two G
  have hR2prop : P2 (Erdos77.diagonalRamsey 2) := by
    exact Nat.sInf_mem hP2
  have hR2lower : 2 <= Erdos77.diagonalRamsey 2 := by
    by_contra hsmall
    have hle : Erdos77.diagonalRamsey 2 <= 1 := by omega
    have hbad : Not (P2 (Erdos77.diagonalRamsey 2)) := by
      intro hP
      let G : SimpleGraph (Fin (Erdos77.diagonalRamsey 2)) :=
        SimpleGraph.emptyGraph (Fin (Erdos77.diagonalRamsey 2))
      cases hP G with
      | inl hs => exact (noNCliqueTwo_of_fin_le_one _ hle G) hs
      | inr hs => exact (noNCliqueTwo_of_fin_le_one _ hle (Compl.compl G)) hs
    exact hbad hR2prop

  have hcontra := h 1 1 (by omega) (by omega)
  have hcontra2 : Erdos77.diagonalRamsey 2 <= 1 := by
    calc
      Erdos77.diagonalRamsey 2 <= Erdos77.diagonalRamsey 1 * Erdos77.diagonalRamsey 1 := by
        simpa using hcontra
      _ <= 1 * 1 := Nat.mul_le_mul hR1upper hR1upper
      _ = 1 := by omega
  omega
