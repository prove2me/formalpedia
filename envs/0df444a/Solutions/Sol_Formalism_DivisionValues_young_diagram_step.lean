-- Prove2me | solution 1 for Formalism.DivisionValues.young_diagram_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:57:11.891943+00:00
-- url     : https://prove2.me/submissions/34f60a9c-9cb6-4f53-a0d7-47071a90dacd

import Definitions.Def_Formalism_QuotientMetricDivisors_TheoremDivIneqRows
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SumInterlacedBoundFails
import Definitions.Def_Formalism_LogFactorialIndices_SubspaceIndexSigned
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_YoungDiagramHook
import Theorems.Thm_Formalism_DivisionValues_young_diagram_factorial
import Theorems.Thm_Formalism_DivisionValues_young_diagram_period
import Theorems.Thm_Formalism_DivisionValues_W8_arith_fact_top
import Theorems.Thm_Formalism_DivisionValues_W8_arith_fact_off
import Theorems.Thm_Formalism_DivisionValues_W8_arith_per
import Theorems.Thm_Formalism_DivisionValues_W8_off_nonneg
import Theorems.Thm_Formalism_DivisionValues_W8_top_nonneg

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
open Formalism.LatticeIndexTer (ph)
open W8
namespace Formalism.DivisionValues
theorem _root_.solution : RowsStepE := by
  intro J Pl _ _ TT _ n aT w ν ap fa a rd La k N S Sc t η m b' cs C0 hLa hLa1 hk hkN hb' hcs hC2
    hCcs hSc hwA hBlA haTA hfa hoff htop
  have hk0 : 0 ≤ k := by
    rw [hk]
    positivity
  refine ⟨fun j ρ => phRows (ν j ρ) - fa j ρ - (if ρ ∈ TT then ph (aT ρ : ℝ) else 0),
    fun j ρ => ((ν j ρ).sum : ℝ) - (if ρ ∈ TT then (aT ρ : ℝ) else 0) - k * (w j ρ : ℝ),
    fun j ρ => by dsimp only; linarith, fun j ρ => by dsimp only; ring, fun j ρ => ?_, fun j ρ => ?_⟩
  · dsimp only
    by_cases hρ : ρ ∈ TT
    · rw [if_pos hρ]
      have hT := htop j ρ hρ
      have h0 := top_nonneg hT
      have hF := (young_diagram_factorial n (w j ρ) Sc (m * (t + 1) * η) (cs * N) (a * rd) La (fa j ρ)
        (ν j ρ) (ap j ρ) hLa hLa1 (hwA j ρ) hBlA (hfa j ρ)).2 (aT ρ) (haTA j ρ hρ) hT
      have hA := arith_fact_top (w := (w j ρ : ℝ)) (n := (n : ℝ)) (Nat.cast_nonneg _) h0.1 h0.2
        (Nat.cast_nonneg _) hk hkN hcs hC2 hCcs hSc hLa1
      linarith
    · rw [if_neg hρ]
      have hO := hoff j ρ hρ
      have h0 := off_nonneg hO
      have hF := (young_diagram_factorial (n + 1) (w j ρ) Sc (m * (t + 1) * η) (cs * N) (a * rd) La
        (fa j ρ) (ν j ρ) (ap j ρ) hLa hLa1 (hwA j ρ) hBlA (hfa j ρ)).1 hO
      have hA := arith_fact_off (w := (w j ρ : ℝ)) (n := ((n + 1 : ℕ) : ℝ)) (k := k)
        (Nat.cast_nonneg _) h0.1 h0.2 (Nat.cast_nonneg _) (by push_cast; linarith) hkN hcs hC2
        hCcs hSc hLa1
      linarith
  · dsimp only
    by_cases hρ : ρ ∈ TT
    · rw [if_pos hρ, if_pos hρ]
      have hT := htop j ρ hρ
      have h0 := top_nonneg hT
      have hP := (young_diagram_period n (w j ρ) Sc (m * (t + 1) * η) (cs * N) (ν j ρ) (ap j ρ)).2
        (aT ρ) hT
      have hX : 0 ≤ k * b' := mul_nonneg hk0 hb'
      have e1 : k * (w j ρ : ℝ) = ((n : ℝ) + 2) * (w j ρ : ℝ) := by rw [hk]
      obtain ⟨hP1, hP2⟩ := hP
      exact arith_per (n := (n : ℝ)) (k := k) (Nat.cast_nonneg _) h0.1 h0.2 (Nat.cast_nonneg _)
        (by rw [hk]; linarith) hkN hC2 hSc hX (by linarith) (by linarith)
    · rw [if_neg hρ, if_neg hρ]
      have hO := hoff j ρ hρ
      have h0 := off_nonneg hO
      have hP := (young_diagram_period (n + 1) (w j ρ) Sc (m * (t + 1) * η) (cs * N) (ν j ρ)
        (ap j ρ)).1 hO
      have e1 : k * (w j ρ : ℝ) = (((n + 1 : ℕ) : ℝ) + 1) * (w j ρ : ℝ) := by
        rw [hk]
        push_cast
        ring
      have e2 : k * Sc = (((n + 1 : ℕ) : ℝ) + 1) * Sc := by
        rw [hk]
        push_cast
        ring
      have hw0 : (0 : ℝ) ≤ w j ρ := Nat.cast_nonneg _
      obtain ⟨hP1, hP2⟩ := hP
      exact arith_per (n := k) (k := k) (Nat.cast_nonneg _) h0.1 h0.2 hk0 le_rfl hkN hC2 hSc le_rfl
        (by linarith) (by linarith)
end Formalism.DivisionValues
