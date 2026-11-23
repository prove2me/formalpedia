-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G5.mp_lmulU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:13:28.873284+00:00
-- url     : https://prove2.me/submissions/fdc705a9-44be-41bb-807b-1294a60b092c

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_mp_mulVec
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_mp_add_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_det_upper
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_continuous_upper
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_blk_mul_upper
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_continuous_coordU
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_coordU_blk
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_joinU_surjective
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
theorem _root_.solution (β : ℂ) : ∀ (n : ℕ) (k : UT n → ℂ),
    MeasurePreserving (fun u : UT n → ℂ => coordU (upper k * upper u)) (muPi β (UT n)) (muPi β (UT n)) := by
  intro n
  induction n with
  | zero =>
    intro k
    have h : (fun u : UT 0 → ℂ => coordU (upper k * upper u)) = id := by
      funext v p
      exact p.1.1.elim0
    rw [h]
    exact MeasurePreserving.id _
  | succ n ih =>
    intro k
    obtain ⟨⟨k0, kb⟩, rfl⟩ := joinU_surjective n k
    have hF : Measurable (fun u : UT (n + 1) → ℂ => coordU (upper (joinU (k0, kb)) * upper u)) :=
      ((continuous_coordU _).comp (continuous_const.matrix_mul (continuous_upper _))).measurable
    refine mp_of_comp (mp_joinU β n) hF ?_
    have hS := (ih k0).prod ((mp_add_const β kb).comp (mp_mulVec β (upper k0) (by rw [det_upper]; simp)))
    have he : (fun u : UT (n + 1) → ℂ => coordU (upper (joinU (k0, kb)) * upper u)) ∘ joinU =
        joinU ∘ Prod.map (fun u : UT n → ℂ => coordU (upper k0 * upper u))
          ((fun x : Fin n → ℂ => x + kb) ∘ fun x : Fin n → ℂ => upper k0 *ᵥ x) := by
      funext p
      obtain ⟨v, b⟩ := p
      simp only [Function.comp, Prod.map]
      rw [upper_joinU, upper_joinU, blk_mul_upper, coordU_blk]
    rw [he]
    exact (mp_joinU β n).comp hS
end Formalism.FourierDecayAlt.P.G5
