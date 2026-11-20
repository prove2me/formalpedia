-- Prove2me | solution 1 for EnvyFreeCake104.Divide.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-19T07:03:37.071806+00:00
-- url     : https://prove2.me/submissions/da038815-d240-4360-8e38-5fb4e43ea529

import Definitions.Def_EnvyFreeCake104_Divide_Protocols
import Theorems.Thm_EnvyFreeCake104_Divide_uniform_envy_free_guess__p2m_d0bc930f_c16f_4335_ae11_af8796226afb_a1
import Theorems.Thm_EnvyFreeCake104_Divide_permute_search_complete__p2m_d0bc930f_c16f_4335_ae11_af8796226afb_a1
import Theorems.Thm_EnvyFreeCake104_Divide_candidate_ranked_certificate__p2m_d0bc930f_c16f_4335_ae11_af8796226afb_a1

open EnvyFreeCake104.Divide

set_option autoImplicit false

theorem solution
    {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (hN : N.Nonempty) (P : ι → Piece) (hP : ∀ i ∈ N, (P i).WF)
    (hPdisj : ∀ i ∈ N, ∀ j ∈ N, i ≠ j → Disjoint (P i).toSet (P j).toSet)
    (s : Rec ι) (hs : s.Valid V N) (hPs : ∀ i ∈ N, s.Aligned (P i))
    (o : ChoiceOracle ι) :
    ∃ (Y : ι → Piece) (R : Piece) (s' : Rec ι) (tr : List (Event ι)),
      exec V o (permute N P) s = some ((Y, R), s', tr) ∧
      EnvyFree V N (fun i ↦ (Y i).toSet) ∧
      R.toSet = (⋃ i ∈ N, (P i).toSet) \ ⋃ i ∈ N, (Y i).toSet ∧
      (∃ π : ι → ι, Set.BijOn π (N : Set ι) (N : Set ι) ∧
        (∀ i ∈ N, IsSuffix (Y i).toSet (P (π i))) ∧
        (∃ istar ∈ N, (Y istar).toSet = (P (π istar)).toSet) ∧
        (∀ S ⊆ N, S.Nonempty → (∀ i ∈ S, (Y i).toSet ≠ (P (π i)).toSet) →
          ∃ istar ∈ S, ∃ jstar ∈ N, jstar ∉ S ∧
            (V jstar).value (Y istar).toSet = (V jstar).value (Y jstar).toSet)) ∧
      s'.prefixCuts ≤ s.prefixCuts + N.card.choose 2 * (N.card.factorial) ^ 2 := by
  classical
  obtain ⟨Y, R, s', tr, hrun, hEF, hbudget, g, t, q, tc, hg, ht, hPt, hcand⟩ :=
    EnvyFreeCake104.Divide.permute_search_complete__p2m_d0bc930f_c16f_4335_ae11_af8796226afb_a1 V N hN P hP hPdisj
      (EnvyFreeCake104.Divide.uniform_envy_free_guess__p2m_d0bc930f_c16f_4335_ae11_af8796226afb_a1 V N hN P hP hPdisj)
      s hs hPs o
  obtain ⟨hR, π, rank, hπ, hsuffix, hlink⟩ :=
    EnvyFreeCake104.Divide.candidate_ranked_certificate__p2m_d0bc930f_c16f_4335_ae11_af8796226afb_a1 V N hN P hP hPdisj
      t ht hPt g hg q Y R s' tc hcand
  refine ⟨Y, R, s', tr, hrun, hEF, hR, ?_, hbudget⟩
  refine ⟨π, hπ, hsuffix, ?_, ?_⟩
  · obtain ⟨i, hi, hmin⟩ := N.exists_min_image rank hN
    refine ⟨i, hi, ?_⟩
    by_contra htrim
    obtain ⟨j, hj, hji, _⟩ := hlink i hi htrim
    exact (not_lt_of_ge (hmin j hj)) hji
  · intro S hSN hS htrim
    obtain ⟨i, hi, hmin⟩ := S.exists_min_image rank hS
    obtain ⟨j, hj, hji, heq⟩ := hlink i (hSN hi) (htrim i hi)
    refine ⟨i, hi, j, hj, ?_, heq⟩
    intro hjS
    exact (not_lt_of_ge (hmin j hjS)) hji

