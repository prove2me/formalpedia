-- Prove2me | solution 1 for EnvyFreeCake104.Divide.uniform_envy_free_guess__p2m_d0bc930f_c16f_4335_ae11_af8796226afb_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-19T09:19:53.9981+00:00
-- url     : https://prove2.me/submissions/6b819870-8bf6-43da-a05c-faaeb9d52aa4

import Definitions.Def_EnvyFreeCake104_Divide_Protocols
import Theorems.Thm_EnvyFreeCake104_Divide_prefixCut_maximal_suffix__p2m_28b14736_b9c5_4b5f_8ea1_07aaaeb21183_a2
import Theorems.Thm_EnvyFreeCake104_Divide_claim_7
import Theorems.Thm_EF104CandidateFamily__p2m_e30dcdf5_697c_4dac_9565_d07a1e730ebe_a1
import Theorems.Thm_EF104ApproximateEnvelopes__p2m_e30dcdf5_697c_4dac_9565_d07a1e730ebe_a1
import Theorems.Thm_EF104Compactness__p2m_e30dcdf5_697c_4dac_9565_d07a1e730ebe_a1
open EnvyFreeCake104.Divide

theorem solution
    {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (hN : N.Nonempty) (P : ι → Piece) (hP : ∀ i ∈ N, (P i).WF)
    (hPdisj : ∀ i ∈ N, ∀ j ∈ N, i ≠ j → Disjoint (P i).toSet (P j).toSet) :
    ∃ g ∈ guesses N,
      ∀ (t : Rec ι), t.Valid V N → (∀ i ∈ N, t.Aligned (P i)) →
        ∀ q : ChoiceOracle ι,
          ∃ (Y : ι → Piece) (R : Piece) (u : Rec ι) (tr : List (Event ι)),
            exec V q (candidate N P g.1 g.2) t = some ((Y, R), u, tr) ∧
            EnvyFree V N (fun i ↦ (Y i).toSet) := by
  classical
  obtain ⟨C, hC⟩ := EF104CandidateFamily__p2m_e30dcdf5_697c_4dac_9565_d07a1e730ebe_a1
    V N P hP
  have hgreedy : ∀ g ∈ guesses N,
      EF104GreedyProfile__p2m_e30dcdf5_697c_4dac_9565_d07a1e730ebe_a1 V P g.1 g.2 (C g) := by
    intro g hg
    exact (hC g hg).1
  have happrox := EF104ApproximateEnvelopes__p2m_e30dcdf5_697c_4dac_9565_d07a1e730ebe_a1
    V N hN P hP hPdisj C hgreedy
  obtain ⟨g, hg, hEF⟩ :=
    EF104Compactness__p2m_e30dcdf5_697c_4dac_9565_d07a1e730ebe_a1 V N hN P hP hPdisj C hgreedy happrox
  refine ⟨g, hg, ?_⟩
  intro t ht hPt q
  obtain ⟨Y, R, u, tr, hrun, hsets⟩ := (hC g hg).2 t ht hPt q
  refine ⟨Y, R, u, tr, hrun, ?_⟩
  intro i hi j hj
  change (V i).value (Y j).toSet ≤ (V i).value (Y i).toSet
  rw [hsets j hj, hsets i hi]
  exact hEF i hi j hj
