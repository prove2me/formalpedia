-- Prove2me | solution 1 for EnvyFreeCake104.Divide.prefixCut_maximal_suffix__p2m_28b14736_b9c5_4b5f_8ea1_07aaaeb21183_a2
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-18T18:40:26.17596+00:00
-- url     : https://prove2.me/submissions/b99e0987-4873-49e5-8586-b8d3c4f3e312

import Definitions.Def_EnvyFreeCake104_Divide_Protocols
import Theorems.Thm_EnvyFreeCake104_Divide_prefixCut_first_crossing__p2m_d4fd739d_9478_4576_b5e6_63846c7c8048_a1
import Theorems.Thm_EnvyFreeCake104_Divide_ordered_piece_split__p2m_d4fd739d_9478_4576_b5e6_63846c7c8048_a1

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
      (prefixList Q p).WF ∧ (suffixList Q p).WF ∧
      s'.Aligned (prefixList Q p) ∧ s'.Aligned (suffixList Q p) ∧
      (V i).value (prefixList Q p).toSet = w ∧
      (V i).value (suffixList Q p).toSet = (V i).value Q.toSet - w ∧
      IsSuffix (suffixList Q p).toSet Q ∧
      ∀ S : Set ℝ, IsSuffix S Q →
        (V i).value S ≤ (V i).value Q.toSet - w →
        S ⊆ (suffixList Q p).toSet := by
  obtain ⟨p, s', tr, hrun, hs', hpts, hp, hpa, hsa, hpval, hfirst⟩ :=
    prefixCut_first_crossing__p2m_d4fd739d_9478_4576_b5e6_63846c7c8048_a1
      V N i hi Q hQ s hs hQs w hw hwQ o tr₀
  obtain ⟨hpwf, hswf, hsval, his, hmono⟩ :=
    ordered_piece_split__p2m_d4fd739d_9478_4576_b5e6_63846c7c8048_a1
      (V i) Q hQ p hp
  refine ⟨p, s', tr, hrun, hs', hpts, hpwf, hswf, hpa, hsa, hpval,
    ?_, his, ?_⟩
  · simpa only [hpval] using hsval
  · intro S hS hbound
    rcases hS with hS | ⟨q, hq, rfl⟩
    · rw [hS]
      exact Set.empty_subset _
    · obtain ⟨_, _, hqval, _, _⟩ :=
        ordered_piece_split__p2m_d4fd739d_9478_4576_b5e6_63846c7c8048_a1
          (V i) Q hQ q (Or.inr hq)
      apply hmono q hq
      apply hfirst q hq
      linarith
