-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.shear_finset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:01:21.963002+00:00
-- url     : https://prove2.me/submissions/31446b1d-a6e2-4882-bc3d-feec55912f5e

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_rank_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormFactor
variable {P Q : Type} [Fintype P] [Fintype Q] [DecidableEq Q]
namespace Formalism.FourierDecayAlt.P.HermitianFormFactor
theorem _root_.solution (B : Matrix P Q ℂ) (s : Finset P) :
    ∀ (G₀ : (Q → Q → ℂ) → ℝ≥0∞), Measurable G₀ → (∀ T : Matrix Q Q ℂ, ¬ T.PosDef → G₀ T = 0) →
    ∫⁻ X : Q → Q → ℂ, G₀ (gram X - ∑ i ∈ s, Matrix.vecMulVec (star (B i)) (B i)) = ∫⁻ X : Q → Q → ℂ, G₀ (gram X) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro G₀ _ _; simp
  | insert a s ha ih =>
    intro G₀ hG h0
    set C : Matrix Q Q ℂ := ∑ i ∈ s, Matrix.vecMulVec (star (B i)) (B i) with hC
    have hCpsd : C.PosSemidef := Matrix.posSemidef_sum _ fun i _ => Matrix.posSemidef_vecMulVec_star_self (B i)
    let G₁ : (Q → Q → ℂ) → ℝ≥0∞ := fun T => G₀ ((Matrix.of T : Matrix Q Q ℂ) - C)
    have hG₁ : Measurable G₁ := by
      refine hG.comp (Continuous.measurable ?_)
      exact (continuous_id (X := Matrix Q Q ℂ)).sub continuous_const
    have h0₁ : ∀ T : Matrix Q Q ℂ, ¬ T.PosDef → G₁ T = 0 := by
      intro T hT
      refine h0 _ fun hP => hT ?_
      have hP' : (T - C).PosDef := hP
      have := hP'.add_posSemidef hCpsd
      rwa [sub_add_cancel] at this
    have h1 := rank_one G₁ hG₁ h0₁ (B a)
    have h2 := ih G₀ hG h0
    rw [Finset.sum_insert ha]
    have e1 : ∀ X : Q → Q → ℂ, G₀ (gram X - (Matrix.vecMulVec (star (B a)) (B a) + C)) =
        G₁ (gram X - Matrix.vecMulVec (star (B a)) (B a)) := by
      intro X
      show _ = G₀ (gram X - Matrix.vecMulVec (star (B a)) (B a) - C)
      rw [sub_sub]
    exact (lintegral_congr e1).trans (h1.trans h2)
end Formalism.FourierDecayAlt.P.HermitianFormFactor
