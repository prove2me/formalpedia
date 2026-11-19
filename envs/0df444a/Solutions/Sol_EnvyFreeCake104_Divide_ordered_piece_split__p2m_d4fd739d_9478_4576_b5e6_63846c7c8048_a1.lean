-- Prove2me | solution 1 for EnvyFreeCake104.Divide.ordered_piece_split__p2m_d4fd739d_9478_4576_b5e6_63846c7c8048_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-18T19:02:11.314199+00:00
-- url     : https://prove2.me/submissions/b8829bab-4a6e-40b7-8515-c1dfb7ebe73a

import Definitions.Def_EnvyFreeCake104_Divide_Model
import Theorems.Thm_EnvyFreeCake104_Divide_cut_disjoint_partition__p2m_4f88c27f_5aff_4766_80c5_ebd56db53b44_a1
import Theorems.Thm_EnvyFreeCake104_Divide_valid_suffix_antitone__p2m_4f88c27f_5aff_4766_80c5_ebd56db53b44_a1

open EnvyFreeCake104.Divide

set_option autoImplicit false

theorem solution
    (v : Valuation) (Q : Piece) (hQ : Q.WF) (p : Pos)
    (hp : Q = [] ∨ Q.ValidPos p) :
    (prefixList Q p).WF ∧ (suffixList Q p).WF ∧
    v.value (suffixList Q p).toSet =
      v.value Q.toSet - v.value (prefixList Q p).toSet ∧
    IsSuffix (suffixList Q p).toSet Q ∧
    ∀ q : Pos, Q.ValidPos q →
      (p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 ≤ q.2)) →
      (suffixList Q q).toSet ⊆ (suffixList Q p).toSet := by
  classical
  rcases hp with rfl | hp
  · simp [prefixList, suffixList, Piece.WF, Piece.toSet, Valuation.value,
      IsSuffix, Piece.ValidPos]
  obtain ⟨hpre, hsuf, hdisj, hunion⟩ :=
    EnvyFreeCake104.Divide.cut_disjoint_partition__p2m_4f88c27f_5aff_4766_80c5_ebd56db53b44_a1 Q hQ p hp
  have hm : ∀ P : Piece, MeasurableSet P.toSet := by
    intro P
    induction P with
    | nil =>
        simpa [Piece.toSet] using
          (MeasurableSet.empty : MeasurableSet (∅ : Set ℝ))
    | cons I P ih =>
        have hI : MeasurableSet I.toSet := by
          unfold Interval.toSet
          split
          · exact measurableSet_Icc
          · exact measurableSet_Ico
        have he : Piece.toSet (I :: P) = I.toSet ∪ Piece.toSet P := by
          ext x
          simp [Piece.toSet]
        rw [he]
        exact hI.union ih
  have hadd : v.value Q.toSet =
      v.value (prefixList Q p).toSet + v.value (suffixList Q p).toSet := by
    unfold Valuation.value
    rw [← hunion, Set.union_inter_distrib_right]
    apply MeasureTheory.setIntegral_union
    · exact hdisj.mono Set.inter_subset_left Set.inter_subset_left
    · exact (hm _).inter measurableSet_Icc
    · exact v.integrable.mono_set Set.inter_subset_right
    · exact v.integrable.mono_set Set.inter_subset_right
  refine ⟨hpre, hsuf, ?_, Or.inr ⟨p, hp, rfl⟩, ?_⟩
  · linarith
  · intro q hq hpq
    exact EnvyFreeCake104.Divide.valid_suffix_antitone__p2m_4f88c27f_5aff_4766_80c5_ebd56db53b44_a1 Q p q hp hq hpq
