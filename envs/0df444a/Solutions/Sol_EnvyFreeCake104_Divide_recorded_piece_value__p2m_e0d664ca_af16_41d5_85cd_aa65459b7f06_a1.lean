-- Prove2me | solution 1 for EnvyFreeCake104.Divide.recorded_piece_value__p2m_e0d664ca_af16_41d5_85cd_aa65459b7f06_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-18T19:09:47.31439+00:00
-- url     : https://prove2.me/submissions/cce189d2-b3df-4286-aee0-b7d93739a37e

import Definitions.Def_EnvyFreeCake104_Divide_Query
import Theorems.Thm_EnvyFreeCake104_Divide_cell_partition_value__p2m_30dca544_0c8a_4339_b224_0ca0d046b555_a1
import Theorems.Thm_EnvyFreeCake104_Divide_disjoint_piece_value__p2m_30dca544_0c8a_4339_b224_0ca0d046b555_a1

open EnvyFreeCake104.Divide

set_option autoImplicit false

theorem solution
    {ι : Type} (V : ι → Valuation) (N : Finset ι) (s : Rec ι)
    (hs : s.Valid V N) (i : ι) (hi : i ∈ N) (P : Piece)
    (hP : P.WF) (hPs : s.Aligned P) :
    s.pieceVal i P = (V i).value P.toSet := by
  classical
  have hI : ∀ I ∈ P, s.intervalVal i I = (V i).value I.toSet := by
    intro I hIP
    have hbound := hP.1 I hIP
    calc
      s.intervalVal i I =
          ∑ c ∈ s.pts.filter (fun c ↦ I.a ≤ c ∧ c < I.b),
            (V i).value (Set.Ico c (s.nextPt c)) := by
        unfold Rec.intervalVal
        apply Finset.sum_congr rfl
        intro c hc
        have hc' := Finset.mem_filter.mp hc
        exact hs.2.2.2 i hi c hc'.1 (lt_of_lt_of_le hc'.2.2 hbound.2.2)
      _ = (V i).value I.toSet :=
        EnvyFreeCake104.Divide.cell_partition_value__p2m_30dca544_0c8a_4339_b224_0ca0d046b555_a1
          (V i) s I hs.2.2.1 (hPs I hIP).1 (hPs I hIP).2 hbound.2.1
  calc
    s.pieceVal i P = (P.map (fun I ↦ (V i).value I.toSet)).sum := by
      unfold Rec.pieceVal
      exact congrArg (fun l : List ℝ ↦ l.sum) (List.map_congr_left hI)
    _ = (V i).value P.toSet :=
      EnvyFreeCake104.Divide.disjoint_piece_value__p2m_30dca544_0c8a_4339_b224_0ca0d046b555_a1
        (V i) P hP
