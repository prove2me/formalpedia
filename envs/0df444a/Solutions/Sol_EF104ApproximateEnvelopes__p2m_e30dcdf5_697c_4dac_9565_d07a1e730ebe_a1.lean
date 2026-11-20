-- Prove2me | solution 1 for EF104ApproximateEnvelopes__p2m_e30dcdf5_697c_4dac_9565_d07a1e730ebe_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-19T09:36:16.607065+00:00
-- url     : https://prove2.me/submissions/86a667b5-2cad-44c8-b7c5-6c6b670a3815

import Theorems.Thm_EF104SmallSuffixChains__p2m_9307d7ac_a474_42b4_b7f1_6bf0b2d91a86_a1
import Theorems.Thm_EF104FiniteSuffixTerminal__p2m_9307d7ac_a474_42b4_b7f1_6bf0b2d91a86_a1
import Theorems.Thm_EF104TerminalContainsGreedy__p2m_9307d7ac_a474_42b4_b7f1_6bf0b2d91a86_a1
import Definitions.Def_EnvyFreeCake104_Divide_Protocols
import Definitions.Def_EF104GreedyProfile__p2m_e30dcdf5_697c_4dac_9565_d07a1e730ebe_a1
open EnvyFreeCake104.Divide

set_option autoImplicit false

theorem solution
    {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (hN : N.Nonempty) (P : ι → Piece) (hP : ∀ i ∈ N, (P i).WF)
    (hPdisj : ∀ i ∈ N, ∀ j ∈ N, i ≠ j → Disjoint (P i).toSet (P j).toSet)
    (C : (List ι × List ι) → ι → Set ℝ)
    (hC : ∀ g ∈ guesses N,
      EF104GreedyProfile__p2m_e30dcdf5_697c_4dac_9565_d07a1e730ebe_a1
        V P g.1 g.2 (C g)) :
    ∀ δ : ℝ, 0 < δ →
      ∃ g ∈ guesses N, ∃ X : ι → Set ℝ,
        (∀ p ∈ g.1.zip g.2, IsSuffix (X p.1) (P p.2)) ∧
        (∀ i ∈ N, C g i ⊆ X i) ∧
        (∀ i ∈ N, ∀ j ∈ N, (V i).value (X j) ≤ (V i).value (X i) + δ) := by
  intro δ hδ
  obtain ⟨m, D, hD⟩ := EF104SmallSuffixChains__p2m_9307d7ac_a474_42b4_b7f1_6bf0b2d91a86_a1 V N P hP δ hδ
  obtain ⟨g, hg, X, hX, henvy, hstop⟩ :=
    EF104FiniteSuffixTerminal__p2m_9307d7ac_a474_42b4_b7f1_6bf0b2d91a86_a1
      V N hN P hP hPdisj δ hδ m D hD
  refine ⟨g, hg, X, hX, ?_, henvy⟩
  exact EF104TerminalContainsGreedy__p2m_9307d7ac_a474_42b4_b7f1_6bf0b2d91a86_a1
    V N P hP g hg (C g) X (hC g hg) hX hstop

