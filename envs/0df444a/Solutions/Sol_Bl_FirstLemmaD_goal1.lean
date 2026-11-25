-- Prove2me | solution 1 for Bl.FirstLemmaD.goal1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:08:48.370315+00:00
-- url     : https://prove2.me/submissions/e7e5b842-2eeb-44a6-9892-6a06e2c8c3d6

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CapelliComplements_FirstLemmaD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.FirstLemmaD
namespace Bl.FirstLemmaD
theorem _root_.solution :
  ∀ {F : Type} [inst : Field.{0} F] [NumberField.{0} F]
  (v : IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} F)),
  Exists.{1} fun (p : Nat) ↦
    And (Nat.Prime p) (Membership.mem.{0, 0} (IsDedekindDomain.HeightOneSpectrum.asIdeal.{0} v) (Nat.cast.{0} p)) := by
  intro F _ _ v
  have := v.isPrime
  have hne : v.asIdeal.comap (algebraMap ℤ (NumberField.RingOfIntegers F)) ≠ ⊥ :=
    fun h => v.ne_bot (Ideal.eq_bot_of_comap_eq_bot h)
  have hpr : (v.asIdeal.comap (algebraMap ℤ (NumberField.RingOfIntegers F))).IsPrime :=
    Ideal.comap_isPrime _ _
  obtain ⟨x, hx, hxp⟩ := hpr.exists_mem_prime_of_ne_bot hne
  refine ⟨x.natAbs, Int.prime_iff_natAbs_prime.mp hxp, ?_⟩
  obtain ⟨c, hc⟩ : x ∣ (x.natAbs : ℤ) := Int.dvd_natAbs.mpr dvd_rfl
  have hmem : ((x.natAbs : ℤ)) ∈ v.asIdeal.comap (algebraMap ℤ (NumberField.RingOfIntegers F)) := by
    rw [hc]
    exact Ideal.mul_mem_right c _ hx
  rw [Ideal.mem_comap, map_natCast] at hmem
  exact hmem
end Bl.FirstLemmaD
