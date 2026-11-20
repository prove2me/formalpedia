-- Prove2me | solution 1 for EnvyFreeCake104.Divide.candidate_ranked_certificate__p2m_d0bc930f_c16f_4335_ae11_af8796226afb_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-19T09:13:06.005172+00:00
-- url     : https://prove2.me/submissions/9e61f4d9-b137-4669-b0b4-0e217be56397

import Definitions.Def_EnvyFreeCake104_Divide_Protocols
import Theorems.Thm_EnvyFreeCake104_Divide_prefixCut_maximal_suffix__p2m_28b14736_b9c5_4b5f_8ea1_07aaaeb21183_a2
import Theorems.Thm_EnvyFreeCake104_Divide_trimAgainst_largest_admissible_suffix__p2m_c4a65f99_9210_4042_b875_f3bc26f0537d_a1
import Theorems.Thm_EnvyFreeCake104_Divide_candidate_history_rule__p2m_c4a65f99_9210_4042_b875_f3bc26f0537d_a1
import Theorems.Thm_EnvyFreeCake104_Divide_trimAgainst_last_trim__p2m_5bed9376_8889_49fb_a2d7_44e0177be346_a1
import Theorems.Thm_EnvyFreeCake104_Divide_candidate_residue__p2m_5bed9376_8889_49fb_a2d7_44e0177be346_a1
import Theorems.Thm_EnvyFreeCake104_Divide_guess_order_certificate__p2m_5bed9376_8889_49fb_a2d7_44e0177be346_a1

open EnvyFreeCake104.Divide

set_option autoImplicit false

theorem solution
    {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (hN : N.Nonempty) (P : ι → Piece) (hP : ∀ i ∈ N, (P i).WF)
    (hPdisj : ∀ i ∈ N, ∀ j ∈ N, i ≠ j → Disjoint (P i).toSet (P j).toSet)
    (s : Rec ι) (hs : s.Valid V N) (hPs : ∀ i ∈ N, s.Aligned (P i))
    (g : List ι × List ι) (hg : g ∈ guesses N) (o : ChoiceOracle ι)
    (Y : ι → Piece) (R : Piece) (s' : Rec ι) (tr : List (Event ι))
    (hrun : exec V o (candidate N P g.1 g.2) s = some ((Y, R), s', tr)) :
    R.toSet = (⋃ i ∈ N, (P i).toSet) \ ⋃ i ∈ N, (Y i).toSet ∧
    ∃ (π : ι → ι) (rank : ι → ℕ),
      Set.BijOn π (N : Set ι) (N : Set ι) ∧
      (∀ i ∈ N, IsSuffix (Y i).toSet (P (π i))) ∧
      ∀ i ∈ N, (Y i).toSet ≠ (P (π i)).toSet →
        ∃ j ∈ N, rank j < rank i ∧
          (V j).value (Y i).toSet = (V j).value (Y j).toSet := by
  classical
  obtain ⟨hag, hmem, π, rank, hbij, horder⟩ :=
    guess_order_certificate__p2m_5bed9376_8889_49fb_a2d7_44e0177be346_a1 N g hg
  let K : List ι → (ι → Piece) → Piece → Piece → Prop :=
    fun earlier A Q B ↦ IsSuffix B.toSet Q ∧
      (B.toSet ≠ Q.toSet →
        ∃ j ∈ earlier, (V j).value B.toSet = (V j).value (A j).toSet)
  have hstable : ∀ (earlier : List ι) (A Z : ι → Piece) (Q B : Piece),
      (∀ i ∈ earlier, A i = Z i) → K earlier A Q B → K earlier Z Q B := by
    intro earlier A Z Q B hAZ hK
    rcases hK with ⟨hsuffix, hwitness⟩
    refine ⟨hsuffix, ?_⟩
    intro hchanged
    obtain ⟨j, hj, heq⟩ := hwitness hchanged
    refine ⟨j, hj, ?_⟩
    simpa only [hAZ j hj] using heq
  have htrim : ∀ (A : ι → Piece) (earlier : List ι) (Q : Piece) (st : Rec ι),
      (∀ i ∈ N, (A i).WF) → (∀ i ∈ earlier, i ∈ N) →
      Q.WF → st.Valid V N →
      (∀ i ∈ N, st.Aligned (A i)) → st.Aligned Q →
      ∀ (oracle : ChoiceOracle ι) (tr₀ : List (Event ι)),
      ∃ (B rem : Piece) (st' : Rec ι) (tr' : List (Event ι)),
        Prog.run V oracle ((trimAgainst N A earlier Q []).run st) tr₀ =
          some (((B, rem), st'), tr') ∧
        st'.Valid V N ∧ st.pts ⊆ st'.pts ∧ B.WF ∧ st'.Aligned B ∧
          K earlier A Q B := by
    intro A earlier Q st hA hear hQ hst hAs hQs oracle tr₀
    obtain ⟨B, rem, st', tr', hr, hv, hp, hB, hBs, hsuf, hbounds, hmax⟩ :=
      trimAgainst_largest_admissible_suffix__p2m_c4a65f99_9210_4042_b875_f3bc26f0537d_a1
        V N
        (prefixCut_maximal_suffix__p2m_28b14736_b9c5_4b5f_8ea1_07aaaeb21183_a2 V N)
        A hA earlier hear Q [] hQ st hst hAs hQs oracle tr₀
    refine ⟨B, rem, st', tr', hr, hv, hp, hB, hBs, hsuf, ?_⟩
    intro hchanged
    exact trimAgainst_last_trim__p2m_5bed9376_8889_49fb_a2d7_44e0177be346_a1
      V N A hA earlier hear Q [] hQ st hst hAs hQs oracle tr₀ B rem st' tr' hr hchanged
  obtain ⟨Y₀, R₀, st₀, tr₀, he, hcert⟩ :=
    candidate_history_rule__p2m_c4a65f99_9210_4042_b875_f3bc26f0537d_a1
      V N K hstable htrim P hP s hs hPs g.1 g.2 hag hmem o
  have hYeq : Y₀ = Y :=
    congrArg (fun z ↦ z.1.1) (Option.some.inj (he.symm.trans hrun))
  subst Y₀
  have hres := candidate_residue__p2m_5bed9376_8889_49fb_a2d7_44e0177be346_a1
    V N P hP hPdisj s hs hPs g hg o Y R s' tr hrun
  refine ⟨hres, π, rank, hbij, ?_, ?_⟩
  · intro i hi
    obtain ⟨before, after, hzip, hbefore⟩ := horder i hi
    exact (hcert before (i, π i) after hzip).1
  · intro i hi hchanged
    obtain ⟨before, after, hzip, hbefore⟩ := horder i hi
    obtain ⟨j, hj, heq⟩ := (hcert before (i, π i) after hzip).2 hchanged
    exact ⟨j, (hbefore j hj).1, (hbefore j hj).2, heq⟩

