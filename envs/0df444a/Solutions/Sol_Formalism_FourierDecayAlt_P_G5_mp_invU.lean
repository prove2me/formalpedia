-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G5.mp_invU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:13:28.535519+00:00
-- url     : https://prove2.me/submissions/809382b4-238e-4252-ad7e-ec72a3899238

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_mp_mulVec
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_inv_blk
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_det_inv_upper
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_continuous_inv_upper
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_continuous_coordU
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_coordU_blk
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_upper_joinU
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_mp_joinU
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_mp_of_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
set_option linter.unusedSimpArgs false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G5
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.G5
theorem _root_.solution (β : ℂ) : ∀ n : ℕ,
    MeasurePreserving (fun v : UT n → ℂ => coordU (upper v)⁻¹) (muPi β (UT n)) (muPi β (UT n)) := by
  intro n
  induction n with
  | zero =>
    have h : (fun v : UT 0 → ℂ => coordU (upper v)⁻¹) = id := by
      funext v p
      exact p.1.1.elim0
    rw [h]
    exact MeasurePreserving.id _
  | succ n ih =>
    have hF : Measurable (fun v : UT (n + 1) → ℂ => coordU (upper v)⁻¹) :=
      ((continuous_coordU _).comp (continuous_inv_upper _)).measurable
    refine mp_of_comp (mp_joinU β n) hF ?_
    have hm : Measurable (Function.uncurry fun (v : UT n → ℂ) (b : Fin n → ℂ) => (-(upper v)⁻¹) *ᵥ b) := by
      refine Continuous.measurable ?_
      exact Continuous.matrix_mulVec ((continuous_inv_upper n).comp continuous_fst).neg continuous_snd
    have hS := ih.skew_product (μc := muPi β (Fin n)) (μd := muPi β (Fin n)) hm
      (Filter.Eventually.of_forall fun v => (mp_mulVec β (-(upper v)⁻¹)
        (by rw [Matrix.det_neg, det_inv_upper]; simp)).map_eq)
    have he : (fun v : UT (n + 1) → ℂ => coordU (upper v)⁻¹) ∘ joinU =
        joinU ∘ fun p : (UT n → ℂ) × (Fin n → ℂ) => (coordU (upper p.1)⁻¹, (-(upper p.1)⁻¹) *ᵥ p.2) := by
      funext p
      obtain ⟨v, b⟩ := p
      simp only [Function.comp]
      rw [upper_joinU, inv_blk, coordU_blk]
    rw [he]
    exact (mp_joinU β n).comp hS
end Formalism.FourierDecayAlt.P.G5
