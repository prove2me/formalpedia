-- Prove2me | solution 1 for FirstPassageLinearTransport.RecertificationRun.toCertifiedRankChain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:43:43.4382+00:00
-- url     : https://prove2.me/submissions/750ab969-2628-493f-81fd-e3266563129f

import Definitions.Def_FirstPassageLinearTransport_RecertificationStep
import Definitions.Def_FirstPassageLinearTransport_RecertificationRun
import Theorems.Thm_FirstPassageLinearTransport_CertifiedRankChain_directFirstPassage
import Theorems.Thm_FirstPassageLinearTransport_CertifiedRankChain_first_of_stage
import Theorems.Thm_FirstPassageLinearTransport_CertifiedRankChain_next_of_stage
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_rationalTargetRank_lt_parent
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell



set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section
namespace FirstPassageLinearTransport
namespace RecertificationRun
theorem _root_.solution
    {r : ℚ} {eta : ℝ} {p : StageSetup (r : ℝ) eta} {n elapsed q : ℕ}
    (hrun : RecertificationRun p n elapsed q) :
    CertifiedRankChain r n elapsed q := by
  have hr : 0 < r := by exact_mod_cast p.r_pos
  have hr1 : r < 1 := by exact_mod_cast p.r_lt_one
  induction hrun with
  | @first m hm0 hnShell hnGood =>
      exact CertifiedRankChain.first_of_stage p hr hm0 hnShell hnGood
  | @next elapsed qprev m hrun hm0 hsourceShell hsourceGood ih =>
      have hfp := ih.directFirstPassage
      have hpow : 2 ^ m ≤ 2 ^ qprev :=
        (mem_dyadicShell.mp hsourceShell).1.trans hfp.1
      have hmq : m ≤ qprev := by
        by_contra hnot
        have hstrict : 2 ^ qprev < 2 ^ m :=
          Nat.pow_lt_pow_right (by omega) (by omega)
        omega
      have hmpos : 0 < m := by
        have ht := p.target_one_lt m hm0
        by_contra hm
        have hmzero : m = 0 := Nat.eq_zero_of_not_pos hm
        subst m
        norm_num [targetScale] at ht
      have htargetlt : rationalTargetRank r m < m :=
        rationalTargetRank_lt_parent hr.le hr1 hmpos
      have hgap : rationalTargetRank r m < qprev := htargetlt.trans_le hmq
      exact CertifiedRankChain.next_of_stage p hr ih hm0 hsourceShell
        hsourceGood hgap
end RecertificationRun
end FirstPassageLinearTransport
