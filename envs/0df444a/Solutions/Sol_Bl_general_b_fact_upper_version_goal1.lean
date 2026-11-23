-- Prove2me | solution 1 for Bl.general_b_fact_upper_version.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:29:54.391467+00:00
-- url     : https://prove2.me/submissions/e9fd39d1-184b-49cc-aeba-7f1566bafa78

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactUpperVersion_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_upper_version
namespace Bl.general_b_fact_upper_version
theorem _root_.solution :
  ∀ {R : Type} [inst : CommRing.{0} R] [IsDomain.{0} R] (ζ : R) (M : Nat) (P : Ideal.{0} R),
  Ne.{1} ζ 1 →
    Eq.{1} (HPow.hPow.{0, 0, 0} ζ M) 1 →
      Membership.mem.{0, 0} P (HSub.hSub.{0, 0, 0} ζ 1) → Membership.mem.{0, 0} P (Nat.cast.{0} M) := by
  intro R _ _ ζ M P h1 hM hP
  have hs : (∑ i ∈ Finset.range M, ζ ^ i) = 0 := by
    have h := geom_sum_mul ζ M
    rw [hM, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr h1)
  rw [← Ideal.Quotient.eq_zero_iff_mem] at hP ⊢
  have h2 : Ideal.Quotient.mk P ζ = 1 := by
    rw [map_sub, map_one, sub_eq_zero] at hP
    exact hP
  have h3 := congrArg (Ideal.Quotient.mk P) hs
  simpa [map_sum, map_pow, h2] using h3
end Bl.general_b_fact_upper_version
