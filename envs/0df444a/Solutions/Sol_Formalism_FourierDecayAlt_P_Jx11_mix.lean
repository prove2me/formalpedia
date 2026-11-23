-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx11.mix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:49:38.453992+00:00
-- url     : https://prove2.me/submissions/0caa08b6-bf97-4120-8e33-b976761edbb0

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThresholdBelowOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx11
namespace Formalism.FourierDecayAlt.P.Jx11
theorem _root_.solution {L d : ℕ} (grid : Fin L → Fin (d + 1) → ℝ) (S : Fin L → ℝ)
    (hS : ∀ a, ∑ i, |F7.lagCo (grid a) i| = S a) (hpos : ∀ a, 0 < S a) (z : ℂ)
    (Fj : (Fin L → Fin (d + 1)) → ℂ)
    (hz : z = ∑ j : Fin L → Fin (d + 1), ((∏ a, F7.lagCo (grid a) (j a) : ℝ) : ℂ) * Fj j) (c : ℝ)
    (Mj : (Fin L → Fin (d + 1)) → ℝ) (hF : ∀ j, ‖Fj j‖ ≤ c * Mj j) :
    (∀ j, 0 ≤ F7.thGrid grid j) ∧ ∑ j, F7.thGrid grid j = 1 ∧
      ‖z‖ ≤ (∏ a, S a) * (c * ∑ j, F7.thGrid grid j * Mj j) := by
  have hth : ∀ j, F7.thGrid grid j = ∏ a, (|F7.lagCo (grid a) (j a)| / S a) := by
    intro j
    unfold F7.thGrid
    exact Finset.prod_congr rfl fun a _ => by rw [hS a]
  have hnn : ∀ j, 0 ≤ F7.thGrid grid j := by
    intro j
    rw [hth j]
    exact Finset.prod_nonneg fun a _ => div_nonneg (abs_nonneg _) (hpos a).le
  have hsum : ∑ j, F7.thGrid grid j = 1 := by
    have h1 : ∑ j : Fin L → Fin (d + 1), ∏ a, (|F7.lagCo (grid a) (j a)| / S a) =
        ∏ a, ∑ i, (|F7.lagCo (grid a) i| / S a) := by
      rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    rw [Finset.sum_congr rfl fun j _ => hth j, h1]
    apply Finset.prod_eq_one
    intro a _
    rw [← Finset.sum_div, hS a, div_self (hpos a).ne']
  have hP : 0 < ∏ a, S a := Finset.prod_pos fun a _ => hpos a
  have hco : ∀ j : Fin L → Fin (d + 1), |∏ a, F7.lagCo (grid a) (j a)| = (∏ a, S a) * F7.thGrid grid j := by
    intro j
    rw [hth j, Finset.prod_div_distrib, Finset.abs_prod, mul_div_cancel₀ _ hP.ne']
  refine ⟨hnn, hsum, ?_⟩
  rw [hz]
  calc ‖∑ j : Fin L → Fin (d + 1), ((∏ a, F7.lagCo (grid a) (j a) : ℝ) : ℂ) * Fj j‖
      ≤ ∑ j : Fin L → Fin (d + 1), ‖((∏ a, F7.lagCo (grid a) (j a) : ℝ) : ℂ) * Fj j‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin L → Fin (d + 1), (∏ a, S a) * F7.thGrid grid j * (c * Mj j) := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hco j]
        exact mul_le_mul_of_nonneg_left (hF j) (mul_nonneg hP.le (hnn j))
    _ = (∏ a, S a) * (c * ∑ j, F7.thGrid grid j * Mj j) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
end Formalism.FourierDecayAlt.P.Jx11
