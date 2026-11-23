-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.pf_abs
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:03.109018+00:00
-- url     : https://prove2.me/submissions/07cb1de8-b852-4a29-bb0a-0e71887c2f11

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_pa_eval
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_DD_eval
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_DD_quot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx7
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset Polynomial
noncomputable section
namespace Formalism.FourierDecayAlt.P.Mx7
theorem _root_.solution (s : Finset ℕ) (ρ : ℕ → ℂ) (hinj : ∀ i ∈ s, ∀ j ∈ s, ρ i = ρ j → i = j)
    (c : ℂ) (q1 : ℂ[X]) (N M : ℕ → ℂ)
    (H1 : ∀ l ∈ s, c * q1.eval (-ρ l) +
      M l * ((∏ j ∈ s.erase l, (-ρ l + ρ j)) * ∏ j ∈ s, (-ρ l + (ρ j + 1))) = 0)
    (H2 : ∀ l ∈ s, c * q1.eval (-(ρ l + 1)) -
      N l * ((∏ j ∈ s, (-(ρ l + 1) + ρ j)) * ∏ j ∈ s.erase l, (-(ρ l + 1) + (ρ j + 1))) = 0)
    (H3 : ∀ l ∈ s, ∀ m ∈ s, ρ m = ρ l + 1 →
      N l = 0 ∧ M m = 0 ∧ (X + C (ρ l + 1)) * (X + C (ρ l + 1)) ∣ q1)
    (hq1 : q1.Monic) (hdeg : q1.natDegree = 2 * s.card + 2) (e : ℂ)
    (he : e = q1.nextCoeff - ∑ i ∈ s, ρ i - ∑ i ∈ s, (ρ i + 1)) :
    ∃ r : ℂ, ∀ Y : ℂ, (∀ i ∈ s, Y + ρ i ≠ 0) → (∀ i ∈ s, Y + (ρ i + 1) ≠ 0) →
      c * q1.eval Y * ((∏ i ∈ s, (Y + ρ i))⁻¹ * (∏ i ∈ s, (Y + (ρ i + 1)))⁻¹) =
        c * (Y * (Y + e)) + r - (∑ l ∈ s, M l * (Y + ρ l)⁻¹) + (∑ l ∈ s, N l * (Y + (ρ l + 1))⁻¹) := by
  obtain ⟨r, hr⟩ := DD_quot s ρ hinj c q1 N M H1 H2 H3 hq1 hdeg e he
  refine ⟨r, fun Y ha hb => ?_⟩
  have hE := congrArg (eval Y) hr
  rw [DD_eval] at hE
  simp only [eval_mul, eval_add, eval_C, eval_X, pa_eval, add_zero] at hE
  have hA0 : (∏ i ∈ s, (Y + ρ i)) ≠ 0 := Finset.prod_ne_zero_iff.2 ha
  have hB0 : (∏ i ∈ s, (Y + (ρ i + 1))) ≠ 0 := Finset.prod_ne_zero_iff.2 hb
  have e1 : (∑ l ∈ s, M l * ((∏ j ∈ s.erase l, (Y + ρ j)) * ∏ j ∈ s, (Y + (ρ j + 1)))) =
      (∏ i ∈ s, (Y + ρ i)) * (∏ i ∈ s, (Y + (ρ i + 1))) * ∑ l ∈ s, M l * (Y + ρ l)⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l hl => ?_)
    rw [← Finset.mul_prod_erase s (fun i => Y + ρ i) hl]
    have hinv := mul_inv_cancel₀ (ha l hl)
    linear_combination (-(M l * ((∏ j ∈ s.erase l, (Y + ρ j)) * ∏ j ∈ s, (Y + (ρ j + 1))))) * hinv
  have e2 : (∑ l ∈ s, N l * ((∏ j ∈ s, (Y + ρ j)) * ∏ j ∈ s.erase l, (Y + (ρ j + 1)))) =
      (∏ i ∈ s, (Y + ρ i)) * (∏ i ∈ s, (Y + (ρ i + 1))) * ∑ l ∈ s, N l * (Y + (ρ l + 1))⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l hl => ?_)
    rw [← Finset.mul_prod_erase s (fun i => Y + (ρ i + 1)) hl]
    have hinv := mul_inv_cancel₀ (hb l hl)
    linear_combination (-(N l * ((∏ j ∈ s, (Y + ρ j)) * ∏ j ∈ s.erase l, (Y + (ρ j + 1))))) * hinv
  rw [e1, e2] at hE
  generalize (∏ i ∈ s, (Y + ρ i)) = A at hE hA0 ⊢
  generalize (∏ i ∈ s, (Y + (ρ i + 1))) = B at hE hB0 ⊢
  have hAB : A * B * (A⁻¹ * B⁻¹) = 1 := by
    rw [mul_mul_mul_comm, mul_inv_cancel₀ hA0, mul_inv_cancel₀ hB0, mul_one]
  have h5 : c * eval Y q1 = (c * (Y * (Y + e)) + r - (∑ l ∈ s, M l * (Y + ρ l)⁻¹) +
      (∑ l ∈ s, N l * (Y + (ρ l + 1))⁻¹)) * (A * B) := by linear_combination hE
  rw [h5, mul_assoc, hAB, mul_one]
end Formalism.FourierDecayAlt.P.Mx7
