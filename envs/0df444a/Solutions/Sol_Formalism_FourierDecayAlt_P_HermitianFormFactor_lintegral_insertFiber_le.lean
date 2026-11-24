-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.lintegral_insertFiber_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:01:50.690831+00:00
-- url     : https://prove2.me/submissions/7aea8225-a18d-45b0-b9f5-27852b70f494

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_polar_shift
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_dot_conj
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_gram_update
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_not_posDef_of_sing

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
variable {Q : Type} [Fintype Q] [DecidableEq Q]
namespace Formalism.FourierDecayAlt.P.HermitianFormFactor
theorem _root_.solution (G₀ : (Q → Q → ℂ) → ℝ≥0∞) (hG : Measurable G₀) (h0 : ∀ T : Matrix Q Q ℂ, ¬ T.PosDef → G₀ T = 0)
    (X : Q → Q → ℂ) (j₀ : Q) (n : Q → ℂ) (hn1 : star n ⬝ᵥ n = 1)
    (hnX : ∀ j, j ≠ j₀ → star n ⬝ᵥ X j = 0) (w : Q → ℂ) :
    ∫⁻ z : ℂ, G₀ (gram (Function.update X j₀ (w + z • n)) - Matrix.single j₀ j₀ (1 : ℂ)) =
      ∫⁻ z : ℂ, G₀ (gram (Function.update X j₀ (w + z • n))) := by
  set α : ℂ := star n ⬝ᵥ w with hα
  set x₀ : Q → ℂ := w - α • n with hx₀def
  have hx₀ : star n ⬝ᵥ x₀ = 0 := by
    rw [hx₀def, dotProduct_sub, dotProduct_smul, hn1, ← hα]; simp
  have hw : ∀ z : ℂ, w + z • n = x₀ + (z + α) • n := by
    intro z; rw [hx₀def, add_smul]; abel
  have hn0 : n ≠ 0 := by
    intro h; rw [h] at hn1; simp at hn1
  set M₀ : Matrix Q Q ℂ := gram (Function.update X j₀ x₀) with hM₀
  let φ : ℝ → ℝ≥0∞ := fun s => G₀ (M₀ + (s : ℂ) • Matrix.single j₀ j₀ (1 : ℂ))
  have hφm : Measurable φ := by
    refine hG.comp (Continuous.measurable ?_)
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    fun_prop
  have hφ0 : ∀ s ≤ 0, φ s = 0 := by
    intro s hs
    refine h0 _ ?_
    refine not_posDef_of_sing (cm (Function.update X j₀ x₀)) n hn0 ?_ j₀ s hs
    funext j
    show star (Function.update X j₀ x₀ j) ⬝ᵥ n = 0
    rw [dot_conj]
    by_cases hj : j = j₀
    · subst hj; rw [Function.update_self, hx₀, star_zero]
    · rw [Function.update_of_ne hj, hnX j hj, star_zero]
  have e1 : ∀ z : ℂ, G₀ (gram (Function.update X j₀ (w + z • n)) - Matrix.single j₀ j₀ (1 : ℂ)) =
      φ (Complex.normSq (z + α) - 1) := by
    intro z
    rw [hw z, gram_update X j₀ n x₀ hn1 hnX hx₀]
    show _ = G₀ (M₀ + ((Complex.normSq (z + α) - 1 : ℝ) : ℂ) • Matrix.single j₀ j₀ (1 : ℂ))
    congr 1
    rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
    abel
  have e2 : ∀ z : ℂ, G₀ (gram (Function.update X j₀ (w + z • n))) = φ (Complex.normSq (z + α)) := by
    intro z
    rw [hw z, gram_update X j₀ n x₀ hn1 hnX hx₀]
  simp_rw [e1, e2]
  rw [lintegral_add_right_eq_self (fun z : ℂ => φ (Complex.normSq z - 1)) α,
    lintegral_add_right_eq_self (fun z : ℂ => φ (Complex.normSq z)) α]
  exact polar_shift φ hφm hφ0
end Formalism.FourierDecayAlt.P.HermitianFormFactor
