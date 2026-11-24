-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.unimodUnramUnique_quad
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:30.568118+00:00
-- url     : https://prove2.me/submissions/1dd284b5-c238-4884-a964-52e2e49a55a8

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementJac
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
import Theorems.Thm_Formalism_HermitianLatticesTheory_unimodUnramUnique_lift
import Theorems.Thm_Formalism_HermitianLatticesTheory_unimodUnramUnique_split
import Theorems.Thm_Formalism_HermitianLatticesTheory_unimodUnramUnique_ff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
open Polynomial IsLocalRing Matrix
variable {S : Type*} [CommRing S] [HenselianLocalRing S]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution [Finite (ResidueField S)] (T N d : S)
    (hD : IsUnit (T ^ 2 - 4 * N)) (hd : IsUnit d) :
    ∃ s t : S, s ^ 2 + T * s * t + N * t ^ 2 = d := by
  have hD' : residue S (T ^ 2 - 4 * N) ≠ 0 := (residue_ne_zero_iff_isUnit _).2 hD
  have h2 : residue S 2 = 2 := map_ofNat _ 2
  have h4 : residue S 4 = 4 := map_ofNat _ 4
  by_cases hroot : ∃ ρ : ResidueField S, ρ ^ 2 + residue S T * ρ + residue S N = 0
  · obtain ⟨ρ, hρ⟩ := hroot
    obtain ⟨r₀, rfl⟩ := residue_surjective ρ
    set g : S[X] := X ^ 2 + C T * X + C N with hgdef
    have hg : g.Monic := by rw [hgdef]; monicity!
    have he : g.eval r₀ = r₀ ^ 2 + T * r₀ + N := by rw [hgdef]; simp
    have hd1 : g.derivative.eval r₀ = 2 * r₀ + T := by rw [hgdef]; simp; ring
    have hsq : (2 * r₀ + T) ^ 2 = (T ^ 2 - 4 * N) + 4 * (r₀ ^ 2 + T * r₀ + N) := by ring
    have h0 : g.eval r₀ ∈ maximalIdeal S := by
      rw [he, ← residue_eq_zero_iff]; simpa using hρ
    have h1 : IsUnit (g.derivative.eval r₀) := by
      rw [hd1, ← residue_ne_zero_iff_isUnit]
      intro hz
      apply hD'
      have key : residue S (T ^ 2 - 4 * N) = (residue S (2 * r₀ + T)) ^ 2
          - 4 * residue S (r₀ ^ 2 + T * r₀ + N) := by
        rw [← map_pow, ← map_ofNat (residue S) 4, ← map_mul, ← map_sub]
        congr 1; linear_combination -hsq
      have hz2 : residue S (r₀ ^ 2 + T * r₀ + N) = 0 := (residue_eq_zero_iff _).2 (he ▸ h0)
      rw [key, hz, hz2]; ring
    obtain ⟨r, hr, -⟩ := HenselianLocalRing.is_henselian g hg r₀ h0 h1
    have hr' : r ^ 2 + T * r + N = 0 := by
      have h2 : g.eval r = 0 := hr
      rw [hgdef] at h2; simpa using h2
    apply unimodUnramUnique_split T N d r hr'
    have : (T + 2 * r) ^ 2 = T ^ 2 - 4 * N := by linear_combination 4 * hr'
    rw [← isUnit_pow_iff (two_ne_zero), this]; exact hD
  · push Not at hroot
    have hN : IsUnit N := by
      rw [← residue_ne_zero_iff_isUnit]
      intro h; exact hroot 0 (by simp [h])
    obtain ⟨a, b, hab⟩ := unimodUnramUnique_ff (residue S T) (residue S N) (residue S d)
      (by simpa [h4] using hD')
    obtain ⟨s₀, rfl⟩ := residue_surjective a
    obtain ⟨t₀, rfl⟩ := residue_surjective b
    have h0 : s₀ ^ 2 + T * s₀ * t₀ + N * t₀ ^ 2 - d ∈ maximalIdeal S := by
      rw [← residue_eq_zero_iff]; simp only [map_sub, map_add, map_mul, map_pow]
      rw [hab]; ring
    by_cases hs : IsUnit (2 * s₀ + T * t₀)
    · exact unimodUnramUnique_lift T N d s₀ t₀ h0 hs
    ·
      have ht : IsUnit (T * s₀ + 2 * N * t₀) := by
        rw [← residue_ne_zero_iff_isUnit]
        rw [← residue_ne_zero_iff_isUnit, not_not] at hs
        intro ht
        have hs' := hs
        simp only [map_add, map_mul, h2] at hs' ht
        have hdz : residue S d ≠ 0 := (residue_ne_zero_iff_isUnit _).2 hd
        apply hdz
        rw [← hab]
        have hDk : residue S T ^ 2 - 4 * residue S N ≠ 0 := by simpa [h4] using hD'
        have htz : residue S t₀ = 0 := by
          have : (residue S T ^ 2 - 4 * residue S N) * residue S t₀ = 0 := by
            linear_combination residue S T * hs' - 2 * ht
          rcases mul_eq_zero.1 this with h | h
          · exact absurd h hDk
          · exact h
        have hsz : residue S s₀ = 0 := by
          have : (residue S T ^ 2 - 4 * residue S N) * residue S s₀ = 0 := by
            linear_combination residue S T * ht - 2 * residue S N * hs'
          rcases mul_eq_zero.1 this with h | h
          · exact absurd h hDk
          · exact h
        simp [htz, hsz]
      obtain ⟨v, hv⟩ := hN.exists_right_inv
      obtain ⟨t, s, hts⟩ := unimodUnramUnique_lift (T * v) v (d * v) t₀ s₀
        (by
          have : t₀ ^ 2 + T * v * t₀ * s₀ + v * s₀ ^ 2 - d * v
              = v * (s₀ ^ 2 + T * s₀ * t₀ + N * t₀ ^ 2 - d) + (1 - N * v) * t₀ ^ 2 := by ring
          rw [this, hv, sub_self, zero_mul, add_zero]
          exact Ideal.mul_mem_left _ _ h0)
        (by
          have : 2 * t₀ + T * v * s₀ = v * (T * s₀ + 2 * N * t₀) + (1 - N * v) * (2 * t₀) := by ring
          rw [this, hv, sub_self, zero_mul, add_zero]
          exact (isUnit_iff_exists_inv.2 ⟨N, by rw [mul_comm]; exact hv⟩).mul ht)
      exact ⟨s, t, by linear_combination N * hts - (T * s * t + s ^ 2 - d) * hv⟩
end Formalism.HermitianLatticesTheory
