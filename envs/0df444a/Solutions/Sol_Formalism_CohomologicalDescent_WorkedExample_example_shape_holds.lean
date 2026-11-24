-- Prove2me | solution 1 for Formalism.CohomologicalDescent.WorkedExample.example_shape_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:16:16.329889+00:00
-- url     : https://prove2.me/submissions/8ecc21c9-ae38-40aa-81a8-c5db5553bc4d

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_MultiplicityZeroThickEmbedding
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample
import Theorems.Thm_Formalism_CohomologicalDescent_WorkedExample_example_parameters_holds
import Theorems.Thm_Formalism_CohomologicalDescent_WorkedExample_example_run_entry_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.WorkedExample
open Formalism.CohomologicalDescent
namespace Formalism.CohomologicalDescent.WorkedExample
theorem _root_.solution : ParameterShapeBounds := by
  intro P kc j q' cloud bu bd e c σ z bot hσ hcl hbu hbd hz hbot
  have hσ2 : (σ : ℝ) * (σ : ℝ) = 1 := by
    rcases hσ with rfl | rfl <;> norm_num
  have hv : ∀ a, (σ : ℝ) * ((z a : ℝ) - c) =
      exampleParameterVector (kc + j) q' P.t (Fin.append cloud fun i => -bu i) bd e a := by
    intro a
    rw [hz a, example_parameters_holds]
    linear_combination
      (exampleParameterVector (kc + j) q' P.t (Fin.append cloud fun i => -bu i) bd e a) * hσ2
  have hblk : ∀ s : Fin P.t, (σ : ℝ) * ((z (Fin.castAdd q' (Fin.natAdd (kc + j) s)) : ℝ) - c) =
      -e + ((P.t : ℝ) - 1) / 2 - ((s : ℕ) : ℝ) := by
    intro s; rw [hv, example_run_entry_eq]
  obtain ⟨⟨s0, hs0⟩, hmin⟩ := hbot
  have hmin' : ∀ s : Fin P.t, (bot : ℝ) ≤ (z (Fin.castAdd q' (Fin.natAdd (kc + j) s)) : ℝ) := by
    intro s
    have : bot ≤ z (Fin.castAdd q' (Fin.natAdd (kc + j) s)) := hmin ⟨s, rfl⟩
    exact_mod_cast this
  have hs0' : (z (Fin.castAdd q' (Fin.natAdd (kc + j) s0)) : ℝ) = (bot : ℝ) := by
    have : z (Fin.castAdd q' (Fin.natAdd (kc + j) s0)) = bot := hs0
    exact_mod_cast this
  have ht : 0 < P.t := lt_of_le_of_lt (Nat.zero_le _) s0.isLt
  have hle : ∀ s : Fin P.t, ((s : ℕ) : ℝ) + 1 ≤ (P.t : ℝ) := fun s => by exact_mod_cast s.isLt
  have hge : ∀ s : Fin P.t, (0 : ℝ) ≤ ((s : ℕ) : ℝ) := fun s => Nat.cast_nonneg _

  have main : (σ : ℝ) * ((bot : ℝ) + ((P.t : ℝ) - 1) / 2 - c) = -e ∧
      ∀ s : Fin P.t, (z (Fin.castAdd q' (Fin.natAdd (kc + j) s)) : ℝ) ≤ (bot : ℝ) + (P.t : ℝ) - 1 := by
    rcases hσ with rfl | rfl
    · let sl : Fin P.t := ⟨P.t - 1, by omega⟩
      have hsl : ((sl : ℕ) : ℝ) = (P.t : ℝ) - 1 := by
        show ((P.t - 1 : ℕ) : ℝ) = _
        rw [Nat.cast_sub (by omega)]; simp
      have a1 := hblk s0
      have a2 := hblk sl
      have a3 := hmin' sl
      have a4 := hle s0
      rw [hs0'] at a1
      rw [hsl] at a2
      push_cast at a1 a2 ⊢
      have hs : ((s0 : ℕ) : ℝ) = (P.t : ℝ) - 1 := by linarith
      refine ⟨by linarith, fun s => ?_⟩
      have a5 := hblk s
      have a6 := hge s
      push_cast at a5
      linarith
    · let sf : Fin P.t := ⟨0, ht⟩
      have hsf : ((sf : ℕ) : ℝ) = 0 := by simp [sf]
      have a1 := hblk s0
      have a2 := hblk sf
      have a3 := hmin' sf
      have a4 := hge s0
      rw [hs0'] at a1
      rw [hsf] at a2
      push_cast at a1 a2 ⊢
      have hs : ((s0 : ℕ) : ℝ) = 0 := by linarith
      refine ⟨by linarith, fun s => ?_⟩
      have a5 := hblk s
      have a6 := hle s
      push_cast at a5
      linarith
  refine ⟨hσ, main.1, ?_⟩
  intro u hu hnot
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hu
  rw [hv a]
  induction a using Fin.addCases with
  | left a =>
    induction a using Fin.addCases with
    | left a =>
      induction a using Fin.addCases with
      | left i =>
        left
        simp only [exampleParameterVector, Fin.append_left]
        exact hcl i
      | right i =>
        right
        simp only [exampleParameterVector, Fin.append_left, Fin.append_right]
        have : -bu i + e = -(bu i - e) := by ring
        rw [this, abs_neg]
        exact hbu i
    | right s =>
      exfalso
      apply hnot
      rw [Finset.mem_Icc]
      constructor
      · exact hmin ⟨s, rfl⟩
      · have := main.2 s
        have h2 : (z (Fin.castAdd q' (Fin.natAdd (kc + j) s)) : ℝ) ≤
            ((bot + (P.t : ℤ) - 1 : ℤ) : ℝ) := by push_cast; exact this
        exact_mod_cast h2
  | right i =>
    right
    simp only [exampleParameterVector, Fin.append_right]
    have : -bd i + e = -(bd i - e) := by ring
    rw [this, abs_neg]
    exact hbd i
end Formalism.CohomologicalDescent.WorkedExample
