-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.tunedIdeal_le_derivIdeal_tunedIdeal_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:27:41.893435+00:00
-- url     : https://prove2.me/submissions/8777392c-22f3-4059-9def-ba1a724de7b9

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_TunedIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_tunedIdeal_antitone
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealIterate_tunedIdeal_le
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_span_pow_mul_tunedIdeal_le
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealIterate_succ
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivation_apply_mem_derivIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_le_derivIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace FunctorialResolution.EmbeddedResolution
section
variable (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
section
variable [Algebra ℚ S]
private theorem mem_of_natCast_add_one_mul_mem {A : Type*} [CommRing A] [Algebra ℚ A] (n : ℕ)
    (I : Ideal A) (y : A) (h : ((n : A) + 1) * y ∈ I) : y ∈ I := by
  have hpos : (0 : ℚ) < (n : ℚ) + 1 := by positivity
  have hq : ((n : ℚ) + 1) ≠ 0 := hpos.ne'
  have hmap : algebraMap ℚ A ((n : ℚ) + 1) = (n : A) + 1 := by
    rw [map_add, map_one, map_natCast]
  have h1 : algebraMap ℚ A ((n : ℚ) + 1)⁻¹ * (((n : A) + 1) * y) ∈ I :=
    Ideal.mul_mem_left I _ h
  rw [← hmap, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hq, map_one, one_mul] at h1
  exact h1
private theorem pow_mul_mem_tunedIdeal (R : Type*) [CommRing R] {A : Type*} [CommRing A]
    [Algebra R A] (J : Ideal A) (m : ℕ) (hm : 1 ≤ m) {x : A}
    (hx : x ∈ derivIdealIterate R (m - 1) J) (s n p : ℕ) {g : A}
    (hg : g ∈ derivIdealIterate R n (tunedIdeal R J m s)) :
    x ^ p * g ∈ tunedIdeal R J m ((s - n) + p) := by
  have hg' : g ∈ tunedIdeal R J m (s - n) := derivIdealIterate_tunedIdeal_le R J m s n hg
  exact span_pow_mul_tunedIdeal_le R J m hm hx p (s - n)
    (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self (x ^ p)) hg')
private theorem pow_mul_mem_derivIdeal_tunedIdeal_succ (R : Type*) [CommRing R] {A : Type*}
    [CommRing A] [Algebra R A] [Algebra ℚ A] (J : Ideal A) (m : ℕ) (hm : 1 ≤ m) {x : A}
    (hx : x ∈ derivIdealIterate R (m - 1) J) (δ : Derivation R A A) (hδ : δ x = 1) (s : ℕ) :
    ∀ d n : ℕ, s + 1 ≤ n + d → ∀ g : A, g ∈ derivIdealIterate R n (tunedIdeal R J m s) →
      x ^ n * g ∈ derivIdeal R (tunedIdeal R J m (s + 1)) := by
  intro d
  induction d with
  | zero =>
      intro n hn g hg
      have h1 : x ^ n * g ∈ tunedIdeal R J m ((s - n) + n) :=
        pow_mul_mem_tunedIdeal R J m hm hx s n n hg
      have h2 : s + 1 ≤ (s - n) + n := by omega
      exact le_derivIdeal R _ (tunedIdeal_antitone R J m h2 h1)
  | succ d ih =>
      intro n hn g hg
      have h1 : x ^ (n + 1) * g ∈ tunedIdeal R J m ((s - n) + (n + 1)) :=
        pow_mul_mem_tunedIdeal R J m hm hx s n (n + 1) hg
      have h2 : s + 1 ≤ (s - n) + (n + 1) := by omega
      have h3 : x ^ (n + 1) * g ∈ tunedIdeal R J m (s + 1) :=
        tunedIdeal_antitone R J m h2 h1
      have h4 : δ (x ^ (n + 1) * g) ∈ derivIdeal R (tunedIdeal R J m (s + 1)) :=
        derivation_apply_mem_derivIdeal R (tunedIdeal R J m (s + 1)) δ h3
      have h5 : δ g ∈ derivIdealIterate R (n + 1) (tunedIdeal R J m s) := by
        rw [derivIdealIterate_succ]
        exact derivation_apply_mem_derivIdeal R (derivIdealIterate R n (tunedIdeal R J m s)) δ hg
      have h6 : x ^ (n + 1) * δ g ∈ derivIdeal R (tunedIdeal R J m (s + 1)) :=
        ih (n + 1) (by omega) (δ g) h5
      have hd1 : δ (x ^ (n + 1)) = ((n : A) + 1) * x ^ n := by
        have hpow := δ.leibniz_pow x (n + 1)
        rw [hδ] at hpow
        simpa using hpow
      have hkey : ((n : A) + 1) * (x ^ n * g)
          = δ (x ^ (n + 1) * g) - x ^ (n + 1) * δ g := by
        rw [Derivation.leibniz, hd1]
        simp only [smul_eq_mul]
        ring
      refine mem_of_natCast_add_one_mul_mem n (derivIdeal R (tunedIdeal R J m (s + 1)))
        (x ^ n * g) ?_
      rw [hkey]
      exact Submodule.sub_mem _ h4 h6
end
end
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
variable [Algebra ℚ S]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (J : Ideal S) (m : ℕ) (hm : 1 ≤ m) {x : S}
    (hx : x ∈ derivIdealIterate k (m - 1) J) (δ : Derivation k S S) (hδ : δ x = 1) (s : ℕ) :
    tunedIdeal k J m s ≤ derivIdeal k (tunedIdeal k J m (s + 1)) := by
  intro g hg
  have h := pow_mul_mem_derivIdeal_tunedIdeal_succ k J m hm hx δ hδ s (s + 1) 0 (by omega) g
    (by rw [derivIdealIterate_zero]; exact hg)
  rwa [pow_zero, one_mul] at h
end FunctorialResolution.EmbeddedResolution
