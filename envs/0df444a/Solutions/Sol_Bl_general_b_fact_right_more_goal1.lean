-- Prove2me | solution 1 for Bl.general_b_fact_right_more.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:26:09.06006+00:00
-- url     : https://prove2.me/submissions/e93ea807-07d2-4c91-b5ec-adcf57c15b2a

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactRightMore_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_right_more
namespace Bl.general_b_fact_right_more
theorem _root_.solution :
  ∀ {E : Type} [inst : Field.{0} E] [NumberField.{0} E] [StarRing.{0} E]
  (P : IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} E)),
  Exists.{1} fun (a : NumberField.RingOfIntegers.{0} E) ↦
    And (Membership.mem.{0, 0} (IsDedekindDomain.HeightOneSpectrum.asIdeal.{0} P) a)
      (Exists.{1} fun (c : NumberField.RingOfIntegers.{0} E) ↦
        And (Not (Membership.mem.{0, 0} (IsDedekindDomain.HeightOneSpectrum.asIdeal.{0} P) c))
          (∀ (p : NumberField.RingOfIntegers.{0} E),
            Membership.mem.{0, 0} (IsDedekindDomain.HeightOneSpectrum.asIdeal.{0} P) p →
              Exists.{1} fun (t : NumberField.RingOfIntegers.{0} E) ↦
                Eq.{1} (HMul.hMul.{0, 0, 0} c p) (HMul.hMul.{0, 0, 0} a t)))  := by
  intro E _ _ _ P
  have h0 : P.asIdeal ≠ ⊥ := P.ne_bot
  have h1 : P.asIdeal ≠ ⊤ := P.isPrime.ne_top
  have hlt : P.asIdeal ^ 2 < P.asIdeal := Ideal.pow_lt_self _ h0 h1 2 le_rfl
  obtain ⟨a, haP, ha2⟩ := SetLike.exists_of_lt hlt
  have hdvd : P.asIdeal ∣ Ideal.span {a} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr haP)
  obtain ⟨J, hJ⟩ := hdvd
  have hJP : ¬ J ≤ P.asIdeal := by
    intro hle
    apply ha2
    have h2 : Ideal.span {a} ≤ P.asIdeal ^ 2 := by
      rw [hJ, pow_two]; exact Ideal.mul_mono_right hle
    exact (Ideal.span_singleton_le_iff_mem _).mp h2
  obtain ⟨c, hcJ, hcP⟩ := SetLike.not_le_iff_exists.mp hJP
  refine ⟨a, haP, c, hcP, fun p hp => ?_⟩
  have hm : c * p ∈ Ideal.span {a} := by
    rw [hJ, mul_comm c p]; exact Ideal.mul_mem_mul hp hcJ
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hm
  exact ⟨t, by rw [← ht, mul_comm]⟩
end Bl.general_b_fact_right_more
