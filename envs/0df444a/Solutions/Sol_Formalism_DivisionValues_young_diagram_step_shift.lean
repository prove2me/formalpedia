-- Prove2me | solution 1 for Formalism.DivisionValues.young_diagram_step_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:04:01.746285+00:00
-- url     : https://prove2.me/submissions/57e7c061-80a4-41fd-bf13-3fd03eb97335

import Definitions.Def_Formalism_QuotientMetricDivisors_TheoremDivIneqRowsShift
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_YoungDiagramHook
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_YoungDiagramTopExact
import Theorems.Thm_Formalism_DivisionValues_young_diagram_step


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.DivisionValues
namespace Formalism.DivisionValues
theorem _root_.solution : RowsStepEShift := by
  intro J Pl _ _ TT _ n aT w wr ν ap fa a rd La k N S Sc t η m b' cs C1 C0
    hLa h1 hk hkN hb' hcs hS hC2 hCcs hSc hC0 hle hsh hwA hBlA hBl0 haA hfa hoff htop
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hk0 : 0 ≤ k := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hcast : ∀ j ρ, (wr j ρ : ℝ) ≤ (w j ρ : ℝ) := fun j ρ => by exact_mod_cast hle j ρ
  obtain ⟨eE, δ, hE1, hE2, hE3, hE4⟩ := young_diagram_step J Pl TT n aT wr ν ap fa a rd La k N S Sc t η
    m b' cs C1 hLa h1 hk hkN hb' hcs hC2 hCcs hSc (fun j ρ => by linarith [hwA j ρ, hcast j ρ]) hBlA
    (fun j ρ hρ => by linarith [haA j ρ hρ, hcast j ρ]) hfa hoff htop
  refine ⟨eE, fun j ρ => δ j ρ - k * ((w j ρ : ℝ) - (wr j ρ : ℝ)), hE1, ?_, ?_, ?_⟩
  · intro j ρ
    have := hE2 j ρ
    simp only
    linarith
  · intro j ρ
    have hw0 : (0 : ℝ) ≤ (wr j ρ : ℝ) := Nat.cast_nonneg _
    have hX : (wr j ρ : ℝ) + S + N ^ 2 + m * (t + 1) * η ≤ (w j ρ : ℝ) + S + N ^ 2 + m * (t + 1) * η := by
      linarith [hcast j ρ]
    have hX0 : 0 ≤ (wr j ρ : ℝ) + S + N ^ 2 + m * (t + 1) * η := by positivity
    have s1 : C1 * ((wr j ρ : ℝ) + S + N ^ 2 + m * (t + 1) * η) ≤
        C0 * ((w j ρ : ℝ) + S + N ^ 2 + m * (t + 1) * η) :=
      mul_le_mul (by linarith) hX hX0 (by linarith)
    exact le_trans (hE3 j ρ) (mul_le_mul_of_nonneg_right s1 (by linarith))
  · intro j ρ
    have hw0 : (0 : ℝ) ≤ (wr j ρ : ℝ) := Nat.cast_nonneg _
    have hT0 : 0 ≤ (if ρ ∈ TT then k * b' else 0) := by
      split_ifs
      · exact mul_nonneg hk0 hb'
      · exact le_rfl
    set T := (if ρ ∈ TT then k * b' else 0) with hT
    have hd : 0 ≤ (w j ρ : ℝ) - (wr j ρ : ℝ) := by linarith [hcast j ρ]
    have a1 : |δ j ρ - k * ((w j ρ : ℝ) - (wr j ρ : ℝ))| ≤ |δ j ρ| + k * ((w j ρ : ℝ) - (wr j ρ : ℝ)) := by
      have := abs_sub (δ j ρ) (k * ((w j ρ : ℝ) - (wr j ρ : ℝ)))
      rwa [abs_of_nonneg (mul_nonneg hk0 hd)] at this
    have a2 : k * ((w j ρ : ℝ) - (wr j ρ : ℝ)) ≤ k * (cs * N) := mul_le_mul_of_nonneg_left (hsh j ρ) hk0
    have a3 : C1 * ((wr j ρ : ℝ) + k * (N + S) + m * (t + 1) * η + T) ≤
        C1 * ((w j ρ : ℝ) + k * (N + S) + m * (t + 1) * η + T) :=
      mul_le_mul_of_nonneg_left (by linarith [hcast j ρ]) (by linarith)
    have hkS : 0 ≤ k * S := mul_nonneg hk0 hS
    have a4 : k * (cs * N) ≤ cs * ((w j ρ : ℝ) + k * (N + S) + m * (t + 1) * η + T) := by
      have : k * N ≤ (w j ρ : ℝ) + k * (N + S) + m * (t + 1) * η + T := by nlinarith [hcast j ρ]
      calc k * (cs * N) = cs * (k * N) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left this hcs
    have hY0 : 0 ≤ (w j ρ : ℝ) + k * (N + S) + m * (t + 1) * η + T := by
      have : 0 ≤ k * N := mul_nonneg hk0 hN0
      nlinarith [hcast j ρ]
    have a5 : (C1 + cs) * ((w j ρ : ℝ) + k * (N + S) + m * (t + 1) * η + T) ≤
        C0 * ((w j ρ : ℝ) + k * (N + S) + m * (t + 1) * η + T) := mul_le_mul_of_nonneg_right hC0 hY0
    have := hE4 j ρ
    simp only
    nlinarith
end Formalism.DivisionValues
