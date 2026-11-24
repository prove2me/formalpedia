-- Prove2me | solution 1 for Formalism.HC.Der.decomp_typeI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:19:43.021626+00:00
-- url     : https://prove2.me/submissions/5fda2ee1-9942-4e1e-a7b8-d7c3bd293956

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RootEqOfSubMem
import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycGrp
import Theorems.Thm_Formalism_HC_Der_sq_mod
import Theorems.Thm_Formalism_HC_Der_cop_QSq_d
import Theorems.Thm_Formalism_HC_Der_split_QSq
import Theorems.Thm_Formalism_FrobeniusOrbits_Decomp_omega_integral
import Theorems.Thm_Formalism_FrobeniusOrbits_Decomp_smul_mem_iff_of_stab
import Theorems.Thm_Formalism_FrobeniusOrbits_Inertia_omega_integral
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {φ : Frame} (H : HostRaw φ)
namespace Formalism.HC.Der
theorem _root_.solution : ∀ (l : ℕ), l.Prime → l ∣ H.QS * H.q →
    ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E),
      σ ∈ MulAction.stabilizer _ P → H.gal σ ∈ φ.Psi := by
  intro l hl hlN P _ _ σ hσ
  have hd4 : H.d % 4 = 3 := by have := H.hyp.2.2.2.1; omega
  show (H.gal σ).1.2 = 1
  rcases Int.units_eq_one_or ((H.gal σ).1.2) with hε | hε
  · exact hε
  exfalso
  have hσX : σ H.sqd = -H.sqd := by rw [H.gal_sqd σ, hε]; simp
  have hM0 : H.QS * H.q ≠ 0 := Nat.mul_ne_zero H.QS_pos.ne' H.hyp.1.ne_zero
  have hd8 : (H.d : ℤ) % 8 = 7 := by have := H.hyp.2.2.2.1; omega
  obtain ⟨s, hs⟩ := sq_mod hd8 (H.QS * H.q) hM0 (split_QSq H)
  have h16 : 2 ^ 4 ∣ H.QS * H.q :=
    ((pow_dvd_pow 2 (by have := H.two_le_e; omega)).trans H.tower_dvd).trans (dvd_mul_right _ _)
  obtain ⟨R, hR⟩ := h16
  obtain ⟨c, hc⟩ := hs
  have hc' : s ^ 2 + (H.d : ℤ) = 16 * ((R : ℤ) * c) := by rw [hc, hR]; push_cast; ring
  obtain ⟨a, rfl⟩ : ∃ a, s = 2 * a + 1 := by
    rcases Int.even_or_odd s with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · exfalso
      have h0 : (H.d : ℤ) = 2 * (8 * ((R : ℤ) * c) - 2 * a ^ 2) := by linear_combination hc'
      generalize 8 * ((R : ℤ) * c) - 2 * a ^ 2 = z at h0
      have := H.hyp.2.2.2.1
      omega
    · exact ⟨a, rfl⟩
  have hlP : ((l : ℤ) : 𝓞 H.E) ∈ P := by
    have h0 : (l : ℤ) ∈ P.under ℤ := by
      rw [← Ideal.over_def P (span {(l : ℤ)})]
      exact Ideal.mem_span_singleton_self _
    simpa [Ideal.under] using h0
  have hlR : l ∣ 4 * R := by
    rcases hl.eq_two_or_odd with rfl | hlo
    · exact Dvd.intro (2 * R) (by ring)
    · have h0 : l ∣ 2 ^ 4 * R := hR ▸ hlN
      have hco : Nat.Coprime l (2 ^ 4) :=
        Nat.Coprime.pow_right 4 ((Nat.coprime_primes hl Nat.prime_two).mpr (by omega))
      exact (hco.dvd_of_dvd_mul_left h0).mul_left 4
  obtain ⟨k, hk⟩ := hlR
  obtain ⟨ω, hωc⟩ : ∃ ω : 𝓞 H.E, (ω : H.E) = (1 + H.sqd) / 2 :=
    ⟨⟨(1 + H.sqd) / 2, Formalism.FrobeniusOrbits.Decomp.omega_integral hd4 H.sqd_sq⟩, rfl⟩
  have hσω : σ • ω = 1 - ω := by
    apply NumberField.RingOfIntegers.ext
    show σ (ω : H.E) = 1 - (ω : H.E)
    rw [hωc, map_div₀, map_add, map_one, hσX, show σ (2 : H.E) = 2 from map_ofNat σ 2]
    ring
  have hprod : (ω - ((a + 1 : ℤ) : 𝓞 H.E)) * (ω - (1 - ((a + 1 : ℤ) : 𝓞 H.E))) =
      -((l : ℤ) : 𝓞 H.E) * ((k * c : ℤ) : 𝓞 H.E) := by
    apply NumberField.RingOfIntegers.ext
    show ((ω : H.E) - ((a + 1 : ℤ) : H.E)) * ((ω : H.E) - (1 - ((a + 1 : ℤ) : H.E))) =
      -((l : ℤ) : H.E) * ((k * c : ℤ) : H.E)
    rw [hωc]
    push_cast
    have hcE : (((2 * a + 1) ^ 2 + (H.d : ℤ) : ℤ) : H.E) = ((16 * ((R : ℤ) * c) : ℤ) : H.E) := by
      rw [hc']
    push_cast at hcE
    have hkE : (4 * (R : H.E)) = (l : H.E) * (k : H.E) := by exact_mod_cast hk
    linear_combination (1 / 4 : H.E) * H.sqd_sq - (1 / 4 : H.E) * hcE - (c : H.E) * hkE
  have hprodP : (ω - ((a + 1 : ℤ) : 𝓞 H.E)) * (ω - (1 - ((a + 1 : ℤ) : 𝓞 H.E))) ∈ P := by
    rw [hprod]
    exact Ideal.mul_mem_right _ _ (neg_mem hlP)
  have hσt : σ • ((a + 1 : ℤ) : 𝓞 H.E) = ((a + 1 : ℤ) : 𝓞 H.E) :=
    map_intCast (MulSemiringAction.toRingHom (H.E ≃ₐ[ℚ] H.E) (𝓞 H.E) σ) (a + 1)
  have hA : ω - ((a + 1 : ℤ) : 𝓞 H.E) ∈ P → ω - (1 - ((a + 1 : ℤ) : 𝓞 H.E)) ∈ P := by
    intro h
    have h1 := (Formalism.FrobeniusOrbits.Decomp.smul_mem_iff_of_stab σ P hσ _).mpr h
    rw [smul_sub, hσω, hσt] at h1
    have h2 : ω - (1 - ((a + 1 : ℤ) : 𝓞 H.E)) = -(1 - ω - ((a + 1 : ℤ) : 𝓞 H.E)) := by ring
    rw [h2]
    exact neg_mem h1
  have hB : ω - (1 - ((a + 1 : ℤ) : 𝓞 H.E)) ∈ P → ω - ((a + 1 : ℤ) : 𝓞 H.E) ∈ P := by
    intro h
    have h1 := (Formalism.FrobeniusOrbits.Decomp.smul_mem_iff_of_stab σ P hσ _).mpr h
    rw [smul_sub, smul_sub, hσω, hσt, smul_one] at h1
    have h2 : ω - ((a + 1 : ℤ) : 𝓞 H.E) = -(1 - ω - (1 - ((a + 1 : ℤ) : 𝓞 H.E))) := by ring
    rw [h2]
    exact neg_mem h1
  have hboth : ω - ((a + 1 : ℤ) : 𝓞 H.E) ∈ P ∧ ω - (1 - ((a + 1 : ℤ) : 𝓞 H.E)) ∈ P := by
    rcases (inferInstance : P.IsPrime).mem_or_mem hprodP with h | h
    · exact ⟨h, hA h⟩
    · exact ⟨hB h, h⟩
  have hsP : ((2 * a + 1 : ℤ) : 𝓞 H.E) ∈ P := by
    have h0 := P.sub_mem hboth.2 hboth.1
    have h1 : ((2 * a + 1 : ℤ) : 𝓞 H.E) =
        ω - (1 - ((a + 1 : ℤ) : 𝓞 H.E)) - (ω - ((a + 1 : ℤ) : 𝓞 H.E)) := by
      push_cast
      ring
    rw [h1]
    exact h0
  have hls : (l : ℤ) ∣ 2 * a + 1 := by
    have h0 : (2 * a + 1 : ℤ) ∈ P.under ℤ := by simpa [Ideal.under] using hsP
    rw [← Ideal.over_def P (span {(l : ℤ)}), Ideal.mem_span_singleton] at h0
    exact h0
  have hlsd : (l : ℤ) ∣ (2 * a + 1) ^ 2 + H.d := by
    rw [hc]
    exact Dvd.dvd.mul_right (by exact_mod_cast hlN) c
  have hld : (l : ℤ) ∣ H.d := (dvd_add_right (dvd_pow hls two_ne_zero)).mp hlsd
  have hld' : l ∣ H.d := by exact_mod_cast hld
  exact hl.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hlN (cop_QSq_d H)) hld')
end Formalism.HC.Der
