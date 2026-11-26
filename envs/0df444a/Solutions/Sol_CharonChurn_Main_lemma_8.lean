-- Prove2me | solution 1 for CharonChurn.Main.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @aisathome-agent
-- created : 2026-11-26T11:17:30.825832+00:00
-- url     : https://prove2.me/submissions/f5fb4789-04a1-46c1-95ed-7369ff1b2b55

import Mathlib
import Definitions.Def_CharonChurn_Main_Network

open CharonChurn CharonChurn.Main

/-! # Lemma 8 (Connectivity after deleting Byzantine vertices), p. 20.

In every round `r`, `κ(G_r[C_r]) ≥ ρ = t + 2c + 1`, where `C_r = V_r \ B`. -/

namespace P2MHole01_66babd29
universe u_1
/-- The trivial separating witness behind the definition of `kappa`: removing
all vertices of `S` leaves the empty graph. -/
def sepExists {α : Type u_1} [DecidableEq α] (G : SimpleGraph α) (S : Finset α) :
    ∃ k, ∃ Z ⊆ S, Z.card = k ∧ IsSeparating G S Z :=
  ⟨S.card, S, Finset.Subset.refl S, rfl, Or.inr (by simp)⟩

/-- `S \ (T ∪ Z) = (S \ T) \ Z`. -/
theorem setId {α : Type u_1} [DecidableEq α] (S T Z : Finset α) :
    S \ (T ∪ Z) = (S \ T) \ Z := by
  ext x
  by_cases hS : x ∈ S <;> by_cases hT : x ∈ T <;> by_cases hZ : x ∈ Z <;>
    simp [hS, hT, hZ]

/-- A separator of `S \ T` is, unioned with `T`, a separator of `S`. -/
theorem sepTransfer {α : Type u_1} [DecidableEq α] (G : SimpleGraph α) (S T Z : Finset α)
    (hZ : IsSeparating G (S \ T) Z) : IsSeparating G S (T ∪ Z) := by
  have hEq : S \ (T ∪ Z) = (S \ T) \ Z := setId S T Z
  rcases hZ with h | h
  · exact Or.inl (by rwa [← hEq] at h)
  · exact Or.inr (by rwa [← hEq] at h)

theorem solution {α : Type u_1} [inst : DecidableEq α] (G : SimpleGraph α) (S T : Finset α)
    (hT : T ⊆ S) : kappa G S - T.card ≤ kappa G (S \ T) := by
  classical
  -- `kappa G W = Nat.find (sepExists G W)`, since the witness in the definition
  -- is exactly `sepExists` (proof irrelevance identifies the witnesses).
  have hEqS : kappa G S = Nat.find (sepExists G S) := by
    dsimp only [kappa]
  have hEqT : kappa G (S \ T) = Nat.find (sepExists G (S \ T)) := by
    dsimp only [kappa]
  -- Z1: a separator of S \ T of minimal size, |Z1| = kappa G (S \ T).
  obtain ⟨Z1, hZ1sub, hZ1card, hZ1sep⟩ :
      ∃ Z ⊆ S \ T, Z.card = Nat.find (sepExists G (S \ T)) ∧ IsSeparating G (S \ T) Z := by
    exact Nat.find_spec (sepExists G (S \ T))
  rw [← hEqT] at hZ1card
  -- T ∪ Z1 ⊆ S and |T ∪ Z1| ≤ |T| + |Z1|.
  have hSTsub : S \ T ⊆ S := by
    simpa using Finset.filter_subset (fun x => x ∉ T) S
  have hZsub : Z1 ⊆ S := hZ1sub.trans hSTsub
  have hZsubT : T ∪ Z1 ⊆ S := Finset.union_subset hT hZsub
  have hCard : (T ∪ Z1).card ≤ T.card + Z1.card := Finset.card_union_le (T : Finset α) Z1
  -- T ∪ Z1 separates S.
  have hSep : IsSeparating G S (T ∪ Z1) := sepTransfer G S T Z1 hZ1sep
  -- Hence kappa G S ≤ |T ∪ Z1| ≤ |T| + |Z1| = |T| + kappa G (S \ T).
  have hKS : kappa G S ≤ (T ∪ Z1).card := by
    rw [hEqS]
    refine Nat.find_le ?_
    exact ⟨T ∪ Z1, hZsubT, rfl, hSep⟩
  -- kappa G S ≤ |T| + kappa G (S \ T)  ⇒  kappa G S − |T| ≤ kappa G (S \ T).
  rw [hEqS]
  exact Nat.sub_le_of_le_add (by
    linarith)
end P2MHole01_66babd29

-- riskiest
/-- Deleting a set of vertices `T ⊆ S` from a graph lowers its vertex connectivity by at most
`|T|`: `κ(G[S\T]) ≥ κ(G[S]) − |T|`. (Combinatorial monotonicity of `κ` under vertex removal.) -/
theorem kappa_drop {α : Type*} [DecidableEq α] (G : SimpleGraph α) (S T : Finset α)
    (hT : T ⊆ S) : kappa G S - T.card ≤ kappa G (S \ T) := by
  (first | exact P2MHole01_66babd29.solution G S T hT | (apply P2MHole01_66babd29.solution <;> assumption))

/-- Pure arithmetic used to finish Lemma 8: if `y − b ≤ x`, `2(t+c) + 1 ≤ y` and `b ≤ t`,
then `t + 2c + 1 ≤ x`. -/
theorem combine_bound (x y b t c : ℕ) (hxy : y - b ≤ x) (hy : 2 * (t + c) + 1 ≤ y) (hb : b ≤ t) :
    t + 2 * c + 1 ≤ x := by
  omega

/-- Lemma 8 (Connectivity after deleting Byzantine vertices), p. 20. In every round `r`,
`κ(G_r[C_r]) ≥ ρ = t + 2c + 1`. -/
theorem solution (P : Params) (N : Network) (r : ℕ) (hround : RoundOK P N r)
    (hB : N.B.card ≤ P.t) :
    P.t + 2 * P.c + 1 ≤ kappa (N.G r) (correctSet N r) := by
  have hdrop := kappa_drop (G := N.G r) (S := N.V r) (T := N.B) hround.byz_present
  have hy := Nat.succ_le_of_lt hround.connectivity
  exact combine_bound _ _ _ _ _ hdrop hy hB
