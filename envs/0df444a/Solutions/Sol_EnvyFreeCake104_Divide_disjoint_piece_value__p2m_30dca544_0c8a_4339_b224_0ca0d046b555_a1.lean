-- Prove2me | solution 1 for EnvyFreeCake104.Divide.disjoint_piece_value__p2m_30dca544_0c8a_4339_b224_0ca0d046b555_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-18T19:52:34.787793+00:00
-- url     : https://prove2.me/submissions/5da1871c-e16a-4021-923b-48d2090048af

import Definitions.Def_EnvyFreeCake104_Divide_Model

open EnvyFreeCake104.Divide

set_option autoImplicit false

theorem solution (v : Valuation) (P : Piece) (hP : P.WF) :
    (P.map (fun I ↦ v.value I.toSet)).sum = v.value P.toSet := by
  have hcons (I : Interval) (Q : Piece) :
      Piece.toSet (I :: Q) = I.toSet ∪ Piece.toSet Q := by
    ext x
    constructor
    · rintro ⟨J, hJ, hx⟩
      rcases List.mem_cons.mp hJ with hJ | hJ
      · subst J
        exact Or.inl hx
      · exact Or.inr ⟨J, hJ, hx⟩
    · rintro (hx | ⟨J, hJ, hx⟩)
      · exact ⟨I, by simp, hx⟩
      · exact ⟨J, List.mem_cons_of_mem I hJ, hx⟩
  have hinterval (I : Interval) : MeasurableSet I.toSet := by
    unfold Interval.toSet
    split
    · exact measurableSet_Icc
    · exact measurableSet_Ico
  have hmeas (Q : Piece) : MeasurableSet (Piece.toSet Q) := by
    induction Q with
    | nil =>
        have hempty : Piece.toSet ([] : Piece) = ∅ := by
          ext x
          simp [Piece.toSet]
        rw [hempty]
        exact MeasurableSet.empty
    | cons I Q ih =>
        rw [hcons]
        exact (hinterval I).union ih
  revert hP
  induction P with
  | nil =>
      intro hP
      simp [Piece.toSet, Valuation.value]
  | cons I P ih =>
      intro hP
      have hpw := List.pairwise_cons.mp hP.2
      have htail : Piece.WF P :=
        ⟨fun J hJ ↦ hP.1 J (List.mem_cons_of_mem I hJ), hpw.2⟩
      have hdisj : Disjoint I.toSet (Piece.toSet P) := by
        apply Set.disjoint_left.mpr
        intro x hx hxP
        obtain ⟨J, hJ, hxJ⟩ := hxP
        exact Set.disjoint_left.mp (hpw.1 J hJ) hx hxJ
      have hd : Disjoint (I.toSet ∩ Set.Icc (0 : ℝ) 1)
          (Piece.toSet P ∩ Set.Icc (0 : ℝ) 1) := by
        apply Set.disjoint_left.mpr
        intro x hx hy
        exact Set.disjoint_left.mp hdisj hx.1 hy.1
      have hi : MeasureTheory.IntegrableOn v.density
          (I.toSet ∩ Set.Icc (0 : ℝ) 1) :=
        v.integrable.mono_set Set.inter_subset_right
      have ht : MeasureTheory.IntegrableOn v.density
          (Piece.toSet P ∩ Set.Icc (0 : ℝ) 1) :=
        v.integrable.mono_set Set.inter_subset_right
      calc
        ((I :: P).map (fun J ↦ v.value J.toSet)).sum =
            v.value I.toSet + v.value (Piece.toSet P) := by
          rw [List.map_cons, List.sum_cons, ih htail]
        _ = v.value (Piece.toSet (I :: P)) := by
          unfold Valuation.value
          rw [hcons, Set.union_inter_distrib_right]
          exact (MeasureTheory.setIntegral_union hd
            ((hmeas P).inter measurableSet_Icc) hi ht).symm
