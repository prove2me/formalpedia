-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.hostOrbitsPlaces
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:16:49.62196+00:00
-- url     : https://prove2.me/submissions/58d62933-9d8e-47b7-b456-c2bcd25dabf2

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostOrbitsPlaces
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Orbits
namespace Formalism.FrobeniusOrbits
theorem _root_.solution : HostOrbitsPlaces := by
  unfold HostOrbitsPlaces
  intro e φ hφ τ hτ i
  have hτ2 : τ.1.2 = 1 := by simpa [Psi, chD] using hτ
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  rcases Nat.even_or_odd i with hi | hi
  · have hc : φ.1 ^ i = 1 := by
      rcases hφ with h | h
      · rw [h, c0]; ext <;> simp [hi.neg_one_pow]
      · rw [h]; ext <;> simp [hi.neg_one_pow]
    have hp : placeOf (φ ^ i * τ) = φ ^ i * τ := by
      unfold placeOf
      rw [if_pos]
      simp [Prod.pow_fst, hc, hτ2]
    rw [hp]
    refine ⟨by simp, fun _ => by simp [hc], fun _ => by simp [hc, hi]⟩
  · have hp : placeOf (φ ^ i * τ) = cc e * (φ ^ i * τ) := by
      unfold placeOf
      rw [if_neg]
      rcases hφ with h | h
      · simp [h, c0, hi.neg_one_pow, hτ2, hne]
      · simp [h, hi.neg_one_pow, hτ2, hne]
    rw [hp]
    refine ⟨by simp [cc], fun h => ?_, fun h => ?_⟩
    · ext <;> simp [cc, c0, h, hi.neg_one_pow, hτ2]
    · have hni : ¬ Even i := Nat.not_even_iff_odd.mpr hi
      ext <;> simp [cc, c0, h, hi.neg_one_pow, hτ2, hni, sg]
end Formalism.FrobeniusOrbits
