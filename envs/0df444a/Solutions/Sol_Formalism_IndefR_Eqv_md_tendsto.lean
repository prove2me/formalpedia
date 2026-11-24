-- Prove2me | solution 1 for Formalism.IndefR.Eqv.md_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:55:27.711656+00:00
-- url     : https://prove2.me/submissions/05fb544b-a54a-42a1-a4b2-d33fa65e93e9

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_SobSym
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_NormIterFderivApplyLe
import Theorems.Thm_Formalism_IndefR_Eqv_iter_fderiv_apply
import Theorems.Thm_Formalism_IndefR_Eqv_contDiff_fderiv_apply
import Theorems.Thm_Formalism_IndefR_Eqv_md_succ_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IndefR Formalism.IndefR.Eqv
open scoped ContDiff
open Filter Topology
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace Formalism.IndefR.Eqv
theorem _root_.solution : ∀ (n : ℕ) (φ : V → ℂ), ContDiff ℝ ∞ φ → ∀ (v : Fin n → V) (a : V) (ε : ℝ), 0 < ε →
    ∃ δ > 0, ∀ h, 0 < h → h < δ → ∀ b, ‖b - a‖ < δ → ‖md φ n v h b - iteratedFDeriv ℝ n φ a v‖ ≤ ε
  | 0, φ, hφ, v, a, ε, hε => by
    obtain ⟨δ, hδ, hδε⟩ := Metric.continuous_iff.mp hφ.continuous a ε hε
    refine ⟨δ, hδ, fun h _ _ b hb => ?_⟩
    simp only [md, iteratedFDeriv_zero_apply]
    have := hδε b (by rw [dist_eq_norm]; exact hb)
    rw [dist_eq_norm] at this
    exact this.le
  | n + 1, φ, hφ, v, a, ε, hε => by
    obtain ⟨δ1, hδ1, hIH⟩ := solution n (fun y => fderiv ℝ φ y (v 0)) (contDiff_fderiv_apply hφ (v 0))
      (Fin.tail v) a ε hε
    have hw : 0 < ‖v 0‖ + 1 := by positivity
    refine ⟨δ1 / (2 * (‖v 0‖ + 1)), by positivity, fun h hh hhδ b hb => ?_⟩
    have hT : iteratedFDeriv ℝ (n + 1) φ a v =
        iteratedFDeriv ℝ n (fun y => fderiv ℝ φ y (v 0)) a (Fin.tail v) := by
      rw [iter_fderiv_apply hφ, Fin.cons_self_tail]
    rw [hT]
    refine md_succ_sub φ hφ n v hh b _ ε fun s hs => hIH h hh ?_ _ ?_
    · have : δ1 / (2 * (‖v 0‖ + 1)) ≤ δ1 := by
        rw [div_le_iff₀ (by positivity)]; nlinarith [norm_nonneg (v 0)]
      linarith
    · calc ‖b + s • v 0 - a‖ = ‖(b - a) + s • v 0‖ := by congr 1; abel
        _ ≤ ‖b - a‖ + s * ‖v 0‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, Real.norm_of_nonneg hs.1]
        _ < δ1 := by
          have h1 : s * ‖v 0‖ ≤ h * ‖v 0‖ := mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _)
          have h2 : h * ‖v 0‖ ≤ δ1 / (2 * (‖v 0‖ + 1)) * (‖v 0‖ + 1) :=
            mul_le_mul hhδ.le (by linarith) (norm_nonneg _) (by positivity)
          have h3 : δ1 / (2 * (‖v 0‖ + 1)) * (‖v 0‖ + 1) = δ1 / 2 := by field_simp
          have h4 : δ1 / (2 * (‖v 0‖ + 1)) ≤ δ1 / 2 := by
            apply div_le_div_of_nonneg_left hδ1.le (by norm_num); nlinarith [norm_nonneg (v 0)]
          linarith
end Formalism.IndefR.Eqv
