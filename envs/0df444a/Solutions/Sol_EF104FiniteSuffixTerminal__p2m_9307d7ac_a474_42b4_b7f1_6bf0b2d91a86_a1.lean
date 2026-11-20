-- Prove2me | solution 1 for EF104FiniteSuffixTerminal__p2m_9307d7ac_a474_42b4_b7f1_6bf0b2d91a86_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-19T15:03:43.052844+00:00
-- url     : https://prove2.me/submissions/07d4b4cf-8edf-4519-b0ae-d7bd1f2799dd

import Definitions.Def_EnvyFreeCake104_Divide_Protocols
import Definitions.Def_EF104GreedyProfile__p2m_e30dcdf5_697c_4dac_9565_d07a1e730ebe_a1
import Theorems.Thm_EF104NumericChainTerminal__p2m_f402ad90_5cdc_4dae_8aed_bffe50fa4e83_a1
import Theorems.Thm_EF104AcyclicPairedOrdering__p2m_f402ad90_5cdc_4dae_8aed_bffe50fa4e83_a1

open EnvyFreeCake104.Divide

theorem solution
    {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (hN : N.Nonempty) (P : ι → Piece) (hP : ∀ i ∈ N, (P i).WF)
    (hPdisj : ∀ i ∈ N, ∀ j ∈ N, i ≠ j → Disjoint (P i).toSet (P j).toSet)
    (δ : ℝ) (hδ : 0 < δ) (m : ι → ℕ) (D : ι → ℕ → Set ℝ)
    (hD :
    ∀ j ∈ N,
      D j 0 = ∅ ∧ D j (m j) = (P j).toSet ∧
      (∀ k ≤ m j, IsSuffix (D j k) (P j)) ∧
      ∀ k < m j, D j k ⊆ D j (k + 1) ∧
        ∀ i ∈ N, 0 ≤ (V i).value (D j (k + 1)) - (V i).value (D j k) ∧
          (V i).value (D j (k + 1)) - (V i).value (D j k) ≤ δ) :
    ∃ g ∈ guesses N, ∃ X : ι → Set ℝ,
      (∀ p ∈ g.1.zip g.2, IsSuffix (X p.1) (P p.2)) ∧
      (∀ i ∈ N, ∀ j ∈ N, (V i).value (X j) ≤ (V i).value (X i) + δ) ∧
    ∀ (before : List (ι × ι)) (p : ι × ι) (after : List (ι × ι)),
      g.1.zip g.2 = before ++ p :: after →
        X p.1 = (P p.2).toSet ∨
        ∃ q ∈ before, (V q.1).value (X q.1) < (V q.1).value (X p.1) := by
  classical
  let u : ι → ι → ℕ → ℝ := fun i j k ↦ (V i).value (D j k)
  have hzero : ∀ i ∈ N, ∀ j ∈ N, u i j 0 = 0 := by
    intro i hi j hj
    simp [u, (hD j hj).1, Valuation.value]
  have hstep : ∀ j ∈ N, ∀ k < m j, ∀ i ∈ N,
      0 ≤ u i j (k + 1) - u i j k ∧
        u i j (k + 1) - u i j k ≤ δ := by
    intro j hj k hkm i hi
    exact ((hD j hj).2.2.2 k hkm).2 i hi
  obtain ⟨σ, hσ, k, hk, hEF, hacyc, hterminal⟩ :=
    EF104NumericChainTerminal__p2m_f402ad90_5cdc_4dae_8aed_bffe50fa4e83_a1 N hN m u δ hδ hzero hstep
  let X : ι → Set ℝ := fun i ↦ D (σ i) (k i)
  let R : ι → ι → Prop := fun i j ↦
    i ∈ N ∧ j ∈ N ∧ (V i).value (X i) < (V i).value (X j)
  have hRacyc : ∀ i, ¬ Relation.TransGen R i i := by
    simpa only [R, X, u] using hacyc
  obtain ⟨g, hg, hpairs, horder⟩ :=
    EF104AcyclicPairedOrdering__p2m_f402ad90_5cdc_4dae_8aed_bffe50fa4e83_a1 N σ hσ R hRacyc
  refine ⟨g, hg, X, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨hi, heq⟩ := hpairs p hp
    change IsSuffix (D (σ p.1) (k p.1)) (P p.2)
    rw [heq]
    exact (hD (σ p.1) ((hσ p.1).mp hi)).2.2.1 (k p.1) (hk p.1 hi)
  · simpa only [X, u] using hEF
  · intro before p after heq
    have hp : p ∈ g.1.zip g.2 := by
      rw [heq]
      simp
    obtain ⟨hi, hpiece⟩ := hpairs p hp
    rcases hterminal p.1 hi with hfull | ⟨i, hiN, henvy⟩
    · left
      change D (σ p.1) (k p.1) = (P p.2).toSet
      rw [hfull, (hD (σ p.1) ((hσ p.1).mp hi)).2.1, hpiece]
    · right
      have hincoming : ∃ i ∈ N, R i p.1 := by
        refine ⟨i, hiN, hiN, hi, ?_⟩
        exact henvy
      obtain ⟨q, hq, hR⟩ := horder before p after heq hincoming
      exact ⟨q, hq, hR.2.2⟩

