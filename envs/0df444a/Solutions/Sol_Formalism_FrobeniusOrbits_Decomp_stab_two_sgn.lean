-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Decomp.stab_two_sgn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:37:21.234798+00:00
-- url     : https://prove2.me/submissions/bcdca608-58a0-4791-ac4d-f2278e24553b

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Theorems.Thm_Formalism_FrobeniusOrbits_Decomp_smul_mem_iff_of_stab
import Theorems.Thm_Formalism_FrobeniusOrbits_Decomp_two_mem
import Theorems.Thm_Formalism_FrobeniusOrbits_Decomp_omega_integral
import Theorems.Thm_P2M_Formalism_FrobeniusOrbits_Decomp_bE_sq__6a1d7841da62

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition Formalism.FrobeniusOrbits.Galois
open Formalism.FrobeniusOrbits.Decomp
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
namespace Formalism.FrobeniusOrbits.Decomp
theorem _root_.solution (hqd : HypOdd q d) (hd16 : d % 16 = 7) (h : IsLayer (e + 2) q d ζ a b)
    (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] [P.LiesOver (span {(2 : ℤ)})]
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b)
    (hσ : σ ∈ MulAction.stabilizer (hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) P) :
    (galE e ζ a b σ).1.2 = 1 := by
  have hbsq : bE ζ a b ^ 2 = -((d : ℕ) : hostE ζ a b) := by simpa using bE_sq' h
  have hfix : σ (bE ζ a b) = bE ζ a b := by
    by_contra hne
    have hsq : (σ (bE ζ a b)) ^ 2 = (bE ζ a b) ^ 2 := by
      rw [← map_pow, hbsq, map_neg, map_natCast]
    have hσb : σ (bE ζ a b) = -(bE ζ a b) := by
      have hm0 : (σ (bE ζ a b) - bE ζ a b) * (σ (bE ζ a b) + bE ζ a b) = 0 := by
        linear_combination hsq
      rcases mul_eq_zero.mp hm0 with h1 | h1
      · exact absurd (sub_eq_zero.mp h1) hne
      · exact eq_neg_of_add_eq_zero_left h1
    have hint : IsIntegral ℤ ((1 + bE ζ a b) / 2) := omega_integral (by omega) hbsq
    obtain ⟨ω, hωv⟩ : ∃ ω : 𝓞 (hostE ζ a b), (ω : hostE ζ a b) = (1 + bE ζ a b) / 2 :=
      ⟨⟨_, hint⟩, rfl⟩
    obtain ⟨m2, hm2⟩ : ∃ m2 : ℕ, d + 1 = 8 * m2 := ⟨(d + 1) / 8, by omega⟩
    have hm : (d : hostE ζ a b) + 1 = 8 * (m2 : hostE ζ a b) := by exact_mod_cast hm2
    have hprod : ω * (1 - ω) = 2 * (m2 : 𝓞 (hostE ζ a b)) := by
      ext1
      have e3 : ((ω * (1 - ω) : 𝓞 (hostE ζ a b)) : hostE ζ a b) =
          (ω : hostE ζ a b) * (1 - (ω : hostE ζ a b)) := by
        first
          | rfl
          | push_cast; rfl
          | simp
      have e4 : ((2 * (m2 : 𝓞 (hostE ζ a b)) : 𝓞 (hostE ζ a b)) : hostE ζ a b) =
          2 * (m2 : hostE ζ a b) := by
        first
          | rfl
          | push_cast; rfl
          | simp
      rw [e3, e4, hωv]
      have hb2 : bE ζ a b ^ 2 = 1 - 8 * (m2 : hostE ζ a b) := by
        rw [hbsq, ← hm]
        ring
      linear_combination (-1 / 4 : hostE ζ a b) * hb2
    have hsw : σ • ω = 1 - ω := by
      ext
      have e1 : ((σ • ω : 𝓞 (hostE ζ a b)) : hostE ζ a b) = σ (ω : hostE ζ a b) := by
        first
          | rfl
          | simp
      have e2 : ((1 - ω : 𝓞 (hostE ζ a b)) : hostE ζ a b) = 1 - (ω : hostE ζ a b) := by
        first
          | rfl
          | push_cast; rfl
          | simp
      rw [e1, e2, hωv, map_div₀, map_add, map_one, hσb, map_ofNat]
      ring
    have hsmul : ∀ z, σ • z ∈ P ↔ z ∈ P := smul_mem_iff_of_stab σ P hσ
    have hprodP : ω * (1 - ω) ∈ P := by
      rw [hprod]
      exact Ideal.mul_mem_right _ _ (two_mem P)
    have hboth : ω ∈ P ∧ 1 - ω ∈ P := by
      rcases (inferInstance : P.IsPrime).mem_or_mem hprodP with h1 | h1
      · exact ⟨h1, by rw [← hsw]; exact (hsmul ω).mpr h1⟩
      · refine ⟨?_, h1⟩
        have h3 := (hsmul (1 - ω)).mpr h1
        rwa [smul_sub, smul_one, hsw, sub_sub_cancel] at h3
    have h1P : (1 : 𝓞 (hostE ζ a b)) ∈ P := by
      simpa using P.add_mem hboth.1 hboth.2
    exact (inferInstance : P.IsPrime).ne_top ((Ideal.eq_top_iff_one P).mpr h1P)
  show sgn σ (bE ζ a b) = 1
  unfold sgn
  exact if_pos hfix
end Formalism.FrobeniusOrbits.Decomp
