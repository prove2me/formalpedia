-- Prove2me | solution 1 for EnvyFreeCake104.Divide.prefix_value_decomposition__p2m_48d250a1_98ba_4f69_b3ca_e5987441b51d_a2
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-19T02:09:08.439519+00:00
-- url     : https://prove2.me/submissions/feace220-1c0b-44f4-add5-dde9a3d8ef8c

import Definitions.Def_EnvyFreeCake104_Divide_Query
import Theorems.Thm_EnvyFreeCake104_Divide_disjoint_piece_value__p2m_30dca544_0c8a_4339_b224_0ca0d046b555_a1
import Theorems.Thm_EnvyFreeCake104_Divide_cut_disjoint_partition__p2m_4f88c27f_5aff_4766_80c5_ebd56db53b44_a1

open EnvyFreeCake104.Divide
open scoped Classical

set_option autoImplicit false

private theorem interval_value_ico__p2m_c352c62d_d5ac_4bcc_999b_94964f7c4827_a2
    (v : Valuation) (I : Interval) (ha : 0 ≤ I.a) (hb : I.b ≤ 1) :
    v.value I.toSet = v.value (Set.Ico I.a I.b) := by
  have hsub : I.toSet ⊆ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    by_cases h : I.b = 1 ∧ I.a < I.b
    · rw [Interval.toSet, if_pos h] at hx
      exact ⟨ha.trans hx.1, hx.2.trans hb⟩
    · rw [Interval.toSet, if_neg h] at hx
      exact ⟨ha.trans hx.1, hx.2.le.trans hb⟩
  have hico : Set.Ico I.a I.b ⊆ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    exact ⟨ha.trans hx.1, hx.2.le.trans hb⟩
  unfold Valuation.value
  rw [Set.inter_eq_left.mpr hsub, Set.inter_eq_left.mpr hico]
  unfold Interval.toSet
  split_ifs
  · exact MeasureTheory.integral_Icc_eq_integral_Ico
  · rfl

private theorem ico_value_mono__p2m_c352c62d_d5ac_4bcc_999b_94964f7c4827_a2
    (v : Valuation) (a x b : ℝ) (hxb : x ≤ b) :
    v.value (Set.Ico a x) ≤ v.value (Set.Ico a b) := by
  unfold Valuation.value
  apply MeasureTheory.setIntegral_mono_set
      (v.integrable.mono_set Set.inter_subset_right)
  · filter_upwards [MeasureTheory.ae_restrict_mem
        ((measurableSet_Ico : MeasurableSet (Set.Ico a b)).inter measurableSet_Icc)]
        with y hy
    exact v.nonneg y hy.2
  · exact Filter.Eventually.of_forall fun y hy ↦
      ⟨⟨hy.1.1, hy.1.2.trans_le hxb⟩, hy.2⟩

theorem solution
    {ι : Type} (V : ι → Valuation) (s : Rec ι) (i : ι)
    (hrecord : ∀ P : Piece, P.WF → s.Aligned P →
      s.pieceVal i P = (V i).value P.toSet)
    (Q : Piece) (hQ : Q.WF) (hQs : s.Aligned Q)
    (p : Pos) (hp : Q.ValidPos p) :
    (V i).value (prefixList Q p).toSet =
        s.pieceVal i (Q.take p.1) +
          (V i).value (Set.Ico (Q.getD p.1 default).a p.2) ∧
      (V i).value (prefixList Q p).toSet ≤
        s.pieceVal i (Q.take (p.1 + 1)) := by
  let I : Interval := Q.getD p.1 default
  have hImem : I ∈ Q := by
    dsimp [I]
    rw [List.getD_eq_getElem Q default hp.1]
    exact List.getElem_mem hp.1
  have hIb : 0 ≤ I.a ∧ I.a ≤ I.b ∧ I.b ≤ 1 := hQ.1 I hImem
  have htake : ∀ n : ℕ, Piece.WF (Q.take n) := by
    intro n
    exact ⟨fun J hJ ↦ hQ.1 J (List.mem_of_mem_take hJ),
      List.Pairwise.sublist (List.take_sublist n Q) hQ.2⟩
  have halign : ∀ n : ℕ, s.Aligned (Q.take n) := by
    intro n J hJ
    exact hQs J (List.mem_of_mem_take hJ)
  have hcorrect : ∀ n : ℕ,
      s.pieceVal i (Q.take n) = (V i).value (Piece.toSet (Q.take n)) := by
    intro n
    exact hrecord (Q.take n) (htake n) (halign n)
  have hprefWF : (prefixList Q p).WF :=
    (cut_disjoint_partition__p2m_4f88c27f_5aff_4766_80c5_ebd56db53b44_a1 Q hQ p hp).1
  have hpref : prefixList Q p = Q.take p.1 ++ [⟨I.a, p.2⟩] := by
    simp only [prefixList, if_pos hp.1, I]
  have hnext : Q.take (p.1 + 1) = Q.take p.1 ++ [I] := by
    simpa only [I, List.getD_eq_getElem Q default hp.1] using
      (List.take_succ_eq_append_getElem hp.1)
  have hpartial :
      (V i).value (Interval.toSet ⟨I.a, p.2⟩) = (V i).value (Set.Ico I.a p.2) :=
    interval_value_ico__p2m_c352c62d_d5ac_4bcc_999b_94964f7c4827_a2
      (V i) ⟨I.a, p.2⟩ hIb.1 (hp.2.2.trans hIb.2.2)
  have hfull : (V i).value I.toSet = (V i).value (Set.Ico I.a I.b) :=
    interval_value_ico__p2m_c352c62d_d5ac_4bcc_999b_94964f7c4827_a2
      (V i) I hIb.1 hIb.2.2
  have hdecomp : (V i).value (prefixList Q p).toSet =
      s.pieceVal i (Q.take p.1) + (V i).value (Set.Ico I.a p.2) := by
    rw [← disjoint_piece_value__p2m_30dca544_0c8a_4339_b224_0ca0d046b555_a1
      (V i) (prefixList Q p) hprefWF, hpref]
    simp only [List.map_append, List.map_singleton, List.sum_append, List.sum_singleton]
    rw [disjoint_piece_value__p2m_30dca544_0c8a_4339_b224_0ca0d046b555_a1
      (V i) (Q.take p.1) (htake p.1), ← hcorrect p.1, hpartial]
  have hcomplete : s.pieceVal i (Q.take (p.1 + 1)) =
      s.pieceVal i (Q.take p.1) + (V i).value I.toSet := by
    rw [hcorrect (p.1 + 1)]
    rw [← disjoint_piece_value__p2m_30dca544_0c8a_4339_b224_0ca0d046b555_a1
      (V i) (Q.take (p.1 + 1)) (htake (p.1 + 1)), hnext]
    simp only [List.map_append, List.map_singleton, List.sum_append, List.sum_singleton]
    rw [disjoint_piece_value__p2m_30dca544_0c8a_4339_b224_0ca0d046b555_a1
      (V i) (Q.take p.1) (htake p.1), ← hcorrect p.1]
  refine ⟨hdecomp, ?_⟩
  calc
    (V i).value (prefixList Q p).toSet =
        s.pieceVal i (Q.take p.1) + (V i).value (Set.Ico I.a p.2) := hdecomp
    _ ≤ s.pieceVal i (Q.take p.1) + (V i).value (Set.Ico I.a I.b) :=
      add_le_add_right
        (ico_value_mono__p2m_c352c62d_d5ac_4bcc_999b_94964f7c4827_a2
          (V i) I.a p.2 I.b hp.2.2) _
    _ = s.pieceVal i (Q.take (p.1 + 1)) := by rw [← hfull, ← hcomplete]
