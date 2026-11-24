-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.sb_roots
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:44:06.197868+00:00
-- url     : https://prove2.me/submissions/2255bb62-30db-4dac-961b-c0befc0b6ebc

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_idx_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_ty_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_up_of_rho
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sb_xC_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sb_xC_root

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Polynomial
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFx2
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.NF
noncomputable section
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {L0 : PreLevel A P.r}
  {QQ : ℂ → Matrix (Fin 2) (Fin 2) A} {κ : (M.Ty P → ℂ) →ₐ[ℂ] A}
namespace Formalism.FourierDecayAlt.P.NFx2
theorem _root_.solution (hP : P.OK) {σ ρ : M.Ty P} (hne : σ ≠ ρ) {c : ℂ}
    (hc : ∀ u, M.xC P σ u * (u + c - 1) = M.xC P ρ u * (u + c)) :
    ∃ m ∈ Icc 1 (P.k - 1), M.Up P m ρ σ ∧ c = ((M.rho P ρ m : ℝ) : ℂ) + 1 := by
  have ha := hc (1 - c)
  have hxa : M.xC P ρ (1 - c) = 0 := by
    rw [show (1 - c + c - 1 : ℂ) = 0 by ring, show (1 - c + c : ℂ) = 1 by ring, mul_zero, mul_one] at ha
    exact ha.symm
  obtain ⟨m, hm, em⟩ := sb_xC_zero hxa
  have hcm : c = ((M.rho P ρ m : ℝ) : ℂ) + 1 := by linear_combination -em

  have hb : ∀ i ∈ Icc 1 (P.k - 1), i ≠ m → M.rho P σ i = M.rho P ρ i := by
    intro i hi him
    have e := hc (-((M.rho P ρ i : ℝ) : ℂ))
    rw [sb_xC_root ρ hi, zero_mul, mul_eq_zero] at e
    rcases e with e | e
    · obtain ⟨j, hj, ej⟩ := sb_xC_zero e
      have ej' : M.rho P ρ i = M.rho P σ j := by exact_mod_cast neg_injective ej
      have := idx_eq P hP ρ σ hi hj ej'
      subst this; exact ej'.symm
    · exfalso; apply him
      have : M.rho P ρ i = M.rho P ρ m := by
        have : ((M.rho P ρ i : ℝ) : ℂ) = ((M.rho P ρ m : ℝ) : ℂ) := by linear_combination -e + hcm
        exact_mod_cast this
      exact idx_eq P hP ρ ρ hi hm this
  have hmm : M.rho P σ m = M.rho P ρ m + 1 := by
    have e := hc (-((M.rho P σ m : ℝ) : ℂ))
    rw [sb_xC_root σ hm, zero_mul] at e
    rcases mul_eq_zero.1 e.symm with e | e
    · exfalso; apply hne
      obtain ⟨j, hj, ej⟩ := sb_xC_zero e
      have ej' : M.rho P σ m = M.rho P ρ j := by exact_mod_cast neg_injective ej
      have := idx_eq P hP σ ρ hm hj ej'
      subst this
      apply ty_ext P
      intro i hi
      by_cases him : i = m
      · subst him; exact ej'
      · exact hb i hi him
    · have : ((M.rho P σ m : ℝ) : ℂ) = ((M.rho P ρ m : ℝ) : ℂ) + 1 := by linear_combination -e + hcm
      exact_mod_cast this
  refine ⟨m, hm, up_of_rho P fun i hi => ?_, hcm⟩
  by_cases him : i = m
  · subst him; simp [hmm]
  · simp [him, hb i hi him]
end Formalism.FourierDecayAlt.P.NFx2
