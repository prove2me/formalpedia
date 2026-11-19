-- Prove2me | solution 1 for EnvyFreeCake104.Divide.prefixCut_first_crossing__p2m_d4fd739d_9478_4576_b5e6_63846c7c8048_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-18T19:01:49.473206+00:00
-- url     : https://prove2.me/submissions/88b47388-3516-47e8-8279-9a2a6d73633f

import Theorems.Thm_EnvyFreeCake104_Divide_cutAnswer_cell_spec__p2m_66383be6_e21c_48b5_b706_d04a2a36f8ee_a2
import Theorems.Thm_EnvyFreeCake104_Divide_splitCell_preserves_records__p2m_66383be6_e21c_48b5_b706_d04a2a36f8ee_a2
import Theorems.Thm_EnvyFreeCake104_Divide_prefixPosition_first_crossing__p2m_66383be6_e21c_48b5_b706_d04a2a36f8ee_a2
import Theorems.Thm_EnvyFreeCake104_Divide_prefixCut_simulates_position__p2m_66383be6_e21c_48b5_b706_d04a2a36f8ee_a2
import Theorems.Thm_EnvyFreeCake104_Divide_recorded_piece_value__p2m_e0d664ca_af16_41d5_85cd_aa65459b7f06_a1
import Definitions.Def_EnvyFreeCake104_Divide_Query

open EnvyFreeCake104.Divide

set_option autoImplicit false

theorem solution
    {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (i : ι) (hi : i ∈ N) (Q : Piece) (hQ : Q.WF)
    (s : Rec ι) (hs : s.Valid V N) (hQs : s.Aligned Q)
    (w : ℝ) (hw : 0 ≤ w) (hwQ : w ≤ (V i).value Q.toSet)
    (o : ChoiceOracle ι) (tr₀ : List (Event ι)) :
    ∃ (p : Pos) (s' : Rec ι) (tr : List (Event ι)),
      Prog.run V o ((prefixCut N i Q w).run s) tr₀ = some ((p, s'), tr) ∧
      s'.Valid V N ∧ s.pts ⊆ s'.pts ∧
      (Q = [] ∨ Q.ValidPos p) ∧
      s'.Aligned (prefixList Q p) ∧ s'.Aligned (suffixList Q p) ∧
      (V i).value (prefixList Q p).toSet = w ∧
      ∀ q : Pos, Q.ValidPos q → w ≤ (V i).value (prefixList Q q).toSet →
        p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 ≤ q.2) := by
  have hrecord : ∀ P : Piece, P.WF → s.Aligned P →
      s.pieceVal i P = (V i).value P.toSet :=
    fun P hP hPs ↦ EnvyFreeCake104.Divide.recorded_piece_value__p2m_e0d664ca_af16_41d5_85cd_aa65459b7f06_a1
      V N s hs i hi P hP hPs
  have hcut := EnvyFreeCake104.Divide.cutAnswer_cell_spec__p2m_66383be6_e21c_48b5_b706_d04a2a36f8ee_a2 V i
  obtain ⟨p, hp, hpos, hvalue, hfirst⟩ :=
    EnvyFreeCake104.Divide.prefixPosition_first_crossing__p2m_66383be6_e21c_48b5_b706_d04a2a36f8ee_a2
      V N s hs i hi hrecord hcut Q hQ hQs w hw hwQ
  obtain ⟨s', tr, hrun, hs', hpts, hpre, hsuf⟩ :=
    EnvyFreeCake104.Divide.prefixCut_simulates_position__p2m_66383be6_e21c_48b5_b706_d04a2a36f8ee_a2
      V N (EnvyFreeCake104.Divide.splitCell_preserves_records__p2m_66383be6_e21c_48b5_b706_d04a2a36f8ee_a2 V N)
      i hi hcut Q hQ s hs hQs w hw p hp o tr₀
  exact ⟨p, s', tr, hrun, hs', hpts, hpos, hpre, hsuf, hvalue, hfirst⟩

