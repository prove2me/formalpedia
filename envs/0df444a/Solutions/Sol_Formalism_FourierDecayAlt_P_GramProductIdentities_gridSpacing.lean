-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GramProductIdentities.gridSpacing
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:08:49.216087+00:00
-- url     : https://prove2.me/submissions/7999e1c8-2679-45e4-b2bc-2ed1e02ab1f3

import Definitions.Def_Formalism_HermitianCurvature_PositionExpansionTopCoefficients
import Definitions.Def_Lemmata_HermitianSesquilinear_ConjEqOfNonnegReal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramProductIdentities

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GramProductIdentities
open Finset Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace Formalism.FourierDecayAlt.P.GramProductIdentities
theorem _root_.solution : GridSpacing := by
  intro α β N hab hN
  have hN' : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0:ℝ) < N := by linarith
  have hI : 0 < β - α := by linarith
  have hL : 0 < (β - α) / (6 * N) := by positivity
  have h2NL : 2 * (N:ℝ) * ((β - α) / (6 * N)) = (β - α) / 3 := by field_simp; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have e : (β - α) / (6 * N) - (β - α) / (7 * N) = (β - α) / (42 * N) := by field_simp; ring
    have : 1 ≤ (β - α) / (42 * N) := by rw [le_div_iff₀ (by positivity)]; linarith
    linarith
  · intro a ha y h1 h2
    rw [Finset.mem_Icc] at ha
    have ha1 : (1:ℝ) ≤ a := by exact_mod_cast ha.1
    have ha2 : (a:ℝ) ≤ N := by exact_mod_cast ha.2
    unfold gl at h1 h2
    have : (2 * (a:ℝ) - 2) * ((β - α) / (6 * N)) ≥ 0 := mul_nonneg (by linarith) hL.le
    have : (2 * (a:ℝ) - 1) * ((β - α) / (6 * N)) ≤ 2 * N * ((β - α) / (6 * N)) :=
      mul_le_mul_of_nonneg_right (by linarith) hL.le
    constructor
    · linarith
    · nlinarith
  · intro a ha b hb hab' y y' h1 h2 h3 h4 e he e' he'
    rw [Finset.mem_Icc] at ha hb
    unfold gl at h1 h2 h3 h4
    have he2 : 0 ≤ e ∧ e ≤ 1 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl <;> norm_num
    have he2' : 0 ≤ e' ∧ e' ≤ 1 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at he'
      rcases he' with rfl | rfl <;> norm_num
    rcases Nat.lt_or_gt_of_ne hab' with hlt | hlt
    · have hc : (a:ℝ) + 1 ≤ b := by exact_mod_cast hlt
      have : 2 * ((b:ℝ) - a) * ((β - α) / (6 * N)) ≥ 2 * ((β - α) / (6 * N)) := by
        nlinarith
      rw [abs_sub_comm]
      refine le_trans ?_ (le_abs_self _)
      nlinarith
    · have hc : (b:ℝ) + 1 ≤ a := by exact_mod_cast hlt
      have : 2 * ((a:ℝ) - b) * ((β - α) / (6 * N)) ≥ 2 * ((β - α) / (6 * N)) := by
        nlinarith
      refine le_trans ?_ (le_abs_self _)
      nlinarith
  · intro h
    rw [le_div_iff₀ (by positivity)]
    nlinarith
end Formalism.FourierDecayAlt.P.GramProductIdentities
