-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.scalar_pair_common_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:58:09.693389+00:00
-- url     : https://prove2.me/submissions/6fffc25b-3e63-4e16-8922-0c70cf54e0a0

import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OmegaNormCofactorOfParts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C7.ScalarPairCommon := by
  intro V _ _ B V' _ _ ω₁ ω₂ ω₁' ω₂' D₁ D₂ Dr₁ Dr₂ T T' hD1 hD2 hT hT' h2 h2' hn1 hn2
  have hcD1 : (starRingEnd ℂ) D₁ ≠ 0 := (map_ne_zero _).2 hD1
  have hcD2 : (starRingEnd ℂ) D₂ ≠ 0 := (map_ne_zero _).2 hD2
  refine ⟨?_, ?_, ?_⟩
  · rw [h2, smul_smul]; congr 1; field_simp
  · rw [h2', smul_smul]; congr 1; rw [map_div₀]; field_simp
  · have hu : (D₂ / D₁) * (starRingEnd ℂ) (D₂ / D₁) = (Complex.normSq D₂ : ℂ) / Complex.normSq D₁ := by
      rw [map_div₀, div_mul_div_comm, Complex.mul_conj, Complex.mul_conj]
    rw [h2] at hn2
    simp only [map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul] at hn2
    have hN1 : (Complex.normSq D₁ : ℂ) ≠ 0 := by exact_mod_cast (Complex.normSq_pos.2 hD1).ne'
    have e : (T : ℂ) * ((starRingEnd ℂ) (D₂ / D₁) * (D₂ / D₁ * B ω₁ ω₁)) =
        ((D₂ / D₁) * (starRingEnd ℂ) (D₂ / D₁)) * (T * B ω₁ ω₁) := by ring
    rw [e, hu, hn1] at hn2
    have hTT : ((T : ℂ) * T') ≠ 0 := by
      have : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
      have : (T' : ℂ) ≠ 0 := by exact_mod_cast hT'.ne'
      exact mul_ne_zero (by assumption) (by assumption)
    have key : (Complex.normSq D₂ : ℂ) * Complex.normSq Dr₁ = Complex.normSq D₁ * Complex.normSq Dr₂ := by
      have h3 : ((T : ℂ) * T') * ((Complex.normSq D₂ : ℂ) * Complex.normSq Dr₁ -
          Complex.normSq D₁ * Complex.normSq Dr₂) = 0 := by
        field_simp at hn2
        linear_combination (-1 : ℂ) * hn2
      have := (mul_eq_zero.1 h3).resolve_left hTT
      linear_combination this
    have keyR : Complex.normSq D₂ * Complex.normSq Dr₁ = Complex.normSq D₁ * Complex.normSq Dr₂ := by
      exact_mod_cast key
    have p1 := Complex.normSq_pos.2 hD1
    have p2 := Complex.normSq_pos.2 hD2
    constructor
    · intro h; rw [h, Complex.normSq_zero, mul_zero] at keyR
      have : Complex.normSq Dr₂ = 0 := by
        rcases mul_eq_zero.1 keyR.symm with h' | h'
        · exact absurd h' p1.ne'
        · exact h'
      exact Complex.normSq_eq_zero.1 this
    · intro h; rw [h, Complex.normSq_zero, mul_zero] at keyR
      have : Complex.normSq Dr₁ = 0 := by
        rcases mul_eq_zero.1 keyR with h' | h'
        · exact absurd h' p2.ne'
        · exact h'
      exact Complex.normSq_eq_zero.1 this
end Formalism.FourierDecayAlt.P
