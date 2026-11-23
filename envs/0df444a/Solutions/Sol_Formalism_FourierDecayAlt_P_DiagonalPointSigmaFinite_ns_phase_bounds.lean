-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.ns_phase_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:15:26.887659+00:00
-- url     : https://prove2.me/submissions/5fcaccc1-5c3c-4835-a820-aa136b509ed8

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseEstimates

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
open Formalism.FourierDecayAlt.G Matrix MeasureTheory Filter Topology
noncomputable section
namespace Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
theorem _root_.solution (m q : ℕ)
    (hRel1 : ∀ (D' : ℂ) (x : Fin (m + 1) → ℂ), (∀ k, x k ≠ 0) →
      ‖dg0 D' x‖ ≤ ‖fderiv ℂ (g0 D') x‖ ∧ ‖fderiv ℂ (g0 D') x‖ ≤ ((m : ℝ) + 1) * ‖dg0 D' x‖)
    (Cj : ℕ → ℝ)
    (hCj : ∀ j : ℕ, 1 ≤ j → ∀ (D' : ℂ) (x : Fin (m + 1) → ℂ) (r : ℝ), 0 < r → (∀ k, r ≤ ‖x k‖) →
      ‖iteratedFDeriv ℂ (j + 1) (g0 D') x‖ ≤ Cj j * (1 + ‖dg0 D' x‖) * (r ^ j)⁻¹)
    {cg : ℝ} (hcg : 0 < cg) {D' : ℂ} {x : Fin (m + 1) → ℂ} {r : ℝ} (hr : 0 < r) (hx : ∀ k, r ≤ ‖x k‖)
    (hg : cg ≤ ‖dg0 D' x‖) {j : ℕ} (hj1 : 1 ≤ j) (hjq : j ≤ q) :
    ‖iteratedFDeriv ℂ (j + 1) (g0 D') x‖ ≤
      ‖fderiv ℂ (g0 D') x‖ * ((1 + (∑ i ∈ Finset.range (q + 1), |Cj i|) * (1 + 1 / cg)) / r) ^ j := by
  set CR : ℝ := ∑ i ∈ Finset.range (q + 1), |Cj i| with hCRdef
  have hCR : Cj j ≤ CR := (le_abs_self _).trans
    (Finset.single_le_sum (f := fun i => |Cj i|) (fun i _ => abs_nonneg _) (Finset.mem_range.mpr (by omega)))
  have hCR0 : 0 ≤ CR := Finset.sum_nonneg fun i _ => abs_nonneg _
  have h1 := hCj j hj1 D' x r hr hx
  have hne : ∀ k, x k ≠ 0 := fun k => norm_pos_iff.mp (hr.trans_le (hx k))
  have hf := (hRel1 D' x hne).1
  set dn : ℝ := ‖dg0 D' x‖
  set F : ℝ := ‖fderiv ℂ (g0 D') x‖
  have hdn : 0 ≤ dn := norm_nonneg _
  have hF : 0 ≤ F := norm_nonneg _
  have hcg1 : 0 ≤ 1 + 1 / cg := by positivity
  have h2 : 1 + dn ≤ (1 + 1 / cg) * F := by
    have h3 : 1 ≤ dn / cg := (one_le_div hcg).mpr hg
    calc 1 + dn ≤ dn / cg + dn := by linarith
      _ = (1 + 1 / cg) * dn := by ring
      _ ≤ (1 + 1 / cg) * F := by gcongr
  set M : ℝ := 1 + CR * (1 + 1 / cg)
  have hM : 1 ≤ M := by
    have : 0 ≤ CR * (1 + 1 / cg) := by positivity
    linarith
  have hrj : 0 ≤ (r ^ j)⁻¹ := by positivity
  calc ‖iteratedFDeriv ℂ (j + 1) (g0 D') x‖ ≤ Cj j * (1 + dn) * (r ^ j)⁻¹ := h1
    _ ≤ CR * ((1 + 1 / cg) * F) * (r ^ j)⁻¹ := by
        apply mul_le_mul_of_nonneg_right _ hrj
        exact mul_le_mul hCR h2 (by linarith) hCR0
    _ ≤ F * M * (r ^ j)⁻¹ := by
        apply mul_le_mul_of_nonneg_right _ hrj
        have : F * M = F + CR * ((1 + 1 / cg) * F) := by simp only [M]; ring
        linarith
    _ ≤ F * M ^ j * (r ^ j)⁻¹ := by
        apply mul_le_mul_of_nonneg_right _ hrj
        exact mul_le_mul_of_nonneg_left (le_self_pow₀ hM (by omega)) hF
    _ = F * (M / r) ^ j := by rw [div_pow]; ring
end Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
