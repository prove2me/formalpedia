-- Prove2me | solution 1 for Bl.general_b_fact_right_variant.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:26:09.093887+00:00
-- url     : https://prove2.me/submissions/9ea0fed3-6441-470a-99a7-7af883fb30ff

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactRightVariant_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open Bl Bl.general_b_fact_right_variant
namespace Bl.general_b_fact_right_variant
theorem _root_.solution :
  ∀ {R : Type u_1} [inst : CommRing.{u_1} R] (P : Ideal.{u_1} R) [hP : Ideal.IsPrime.{u_1} P] (n : Nat),
  Ne.{1} n 0 →
    Membership.mem.{u_1, u_1} P (Nat.cast.{u_1} n) →
      Exists.{1} fun (p : Nat) ↦
        And (Nat.Prime p) (And (Dvd.dvd.{0} p n) (Membership.mem.{u_1, u_1} P (Nat.cast.{u_1} p))) := by
  intro R _ P hP n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hmem
    by_cases h1 : n = 1
    · subst h1
      rw [Nat.cast_one] at hmem
      exact absurd ((Ideal.eq_top_iff_one P).2 hmem) hP.ne_top
    · have hp := Nat.minFac_prime h1
      obtain ⟨m, hm⟩ := Nat.minFac_dvd n
      have hmem' : ((n.minFac : R) * (m : R)) ∈ P := by
        rw [← Nat.cast_mul, ← hm]
        exact hmem
      rcases hP.mem_or_mem hmem' with h | h
      · exact ⟨_, hp, Nat.minFac_dvd n, h⟩
      · have hm0 : m ≠ 0 := by
          rintro rfl
          exact hn (by simpa using hm)
        have hpos : 0 < m := Nat.pos_of_ne_zero hm0
        have h2 := hp.two_le
        have hlt : m < n := by nlinarith
        obtain ⟨p, pp, pd, pm⟩ := ih m hlt hm0 h
        exact ⟨p, pp, Dvd.dvd.trans pd ⟨n.minFac, hm.trans (Nat.mul_comm _ _)⟩, pm⟩
end Bl.general_b_fact_right_variant
