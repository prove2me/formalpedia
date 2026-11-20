-- Prove2me | solution 1 for EnvyFreeCake104.Divide.candidate_residue__p2m_5bed9376_8889_49fb_a2d7_44e0177be346_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-19T15:28:26.863715+00:00
-- url     : https://prove2.me/submissions/829511df-5211-4c94-926c-14372f6baac9

import Definitions.Def_EnvyFreeCake104_Divide_Protocols
import Theorems.Thm_EnvyFreeCake104_Divide_prefixCut_maximal_suffix__p2m_28b14736_b9c5_4b5f_8ea1_07aaaeb21183_a2
import Theorems.Thm_EnvyFreeCake104_Divide_trimAgainst_partition__p2m_2a34ca2a_650a_4889_96ad_7ccf35f2b7ad_a2
import Theorems.Thm_EnvyFreeCake104_Divide_candidateLoop_partition_of_trim__p2m_2a34ca2a_650a_4889_96ad_7ccf35f2b7ad_a2

open EnvyFreeCake104.Divide

set_option autoImplicit false

theorem solution
    {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (P : ι → Piece) (hP : ∀ i ∈ N, (P i).WF)
    (hPdisj : ∀ i ∈ N, ∀ j ∈ N, i ≠ j → Disjoint (P i).toSet (P j).toSet)
    (s : Rec ι) (hs : s.Valid V N) (hPs : ∀ i ∈ N, s.Aligned (P i))
    (g : List ι × List ι) (hg : g ∈ guesses N) (o : ChoiceOracle ι)
    (Y : ι → Piece) (R : Piece) (s' : Rec ι) (tr : List (Event ι))
    (hrun : exec V o (candidate N P g.1 g.2) s = some ((Y, R), s', tr)) :
    R.toSet = (⋃ i ∈ N, (P i).toSet) \ ⋃ i ∈ N, (Y i).toSet := by
  classical
  have horders : g.1.Perm N.toList ∧ g.2.Perm N.toList := by
    have hm : g.1 ∈ N.toList.permutations ∧ g.2 ∈ N.toList.permutations := by
      change (g.1, g.2) ∈ N.toList.permutations.product N.toList.permutations at hg
      exact List.mem_product.mp hg
    exact ⟨List.mem_permutations.mp hm.1, List.mem_permutations.mp hm.2⟩
  have hlen : g.1.length = g.2.length :=
    horders.1.length_eq.trans horders.2.length_eq.symm
  have hfst : (g.1.zip g.2).map Prod.fst = g.1 :=
    List.map_fst_zip (by omega)
  have hsnd : (g.1.zip g.2).map Prod.snd = g.2 :=
    List.map_snd_zip (by omega)
  have hag : ((g.1.zip g.2).map Prod.fst).Nodup := by
    rw [hfst]
    exact horders.1.nodup_iff.mpr N.nodup_toList
  have hagents : ∀ q ∈ g.1.zip g.2, q.1 ∈ N := by
    intro q hq
    have hmem := List.mem_map_of_mem (f := Prod.fst) hq
    rw [hfst] at hmem
    exact Finset.mem_toList.mp (horders.1.mem_iff.mp hmem)
  have hpieces : ((g.1.zip g.2).map Prod.snd).Perm N.toList := by
    rw [hsnd]
    exact horders.2
  have hrun' : Prog.run V o
      ((candidateLoop N P (g.1.zip g.2) [] (fun _ ↦ []) []).run s) [] =
        some (((Y, R), s'), tr) := by
    cases h : Prog.run V o ((candidate N P g.1 g.2).run s) [] with
    | none => simp [exec, h] at hrun
    | some z =>
      rcases z with ⟨⟨a, t⟩, ts⟩
      simp only [exec, h, Option.some.injEq, Prod.mk.injEq] at hrun
      rcases hrun with ⟨rfl, rfl, rfl⟩
      all_goals first | rfl | simpa only [candidate] using h
  obtain ⟨hcover, hdis⟩ :=
    EnvyFreeCake104.Divide.candidateLoop_partition_of_trim__p2m_2a34ca2a_650a_4889_96ad_7ccf35f2b7ad_a2 V N
      (EnvyFreeCake104.Divide.trimAgainst_partition__p2m_2a34ca2a_650a_4889_96ad_7ccf35f2b7ad_a2 V N)
      P hP hPdisj (g.1.zip g.2) hag hagents hpieces s hs hPs o [] Y R s' tr hrun'
  ext x
  have hc := Set.ext_iff.mp hcover x
  constructor
  · intro hx
    exact ⟨hc.mp (Or.inl hx), fun hy ↦ (Set.disjoint_left.mp hdis) hx hy⟩
  · rintro ⟨hx, hnot⟩
    exact (hc.mpr hx).resolve_right hnot

