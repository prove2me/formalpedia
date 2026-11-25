-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.space_side
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:04:05.171525+00:00
-- url     : https://prove2.me/submissions/06668f13-2d5c-4364-85d9-3360a34da4fb

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensSpace
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_space_harm
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_floor_eq_close

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
theorem _root_.solution (Q : Finset ℝ) (f : ℝ → ℝ) (T : ℝ) (hT : 0 ≤ T) (h1 : ∀ x ∈ Q, 1 ≤ f x)
    (h2 : ∀ x ∈ Q, f x ≤ 2 * T) (hsp : ∀ x ∈ Q, ∀ y ∈ Q, x ≠ y → 1 ≤ |f x - f y|) :
    ∑ x ∈ Q, 1 / f x ≤ 1 + Real.log (2 * T + 1) := by
  have hinj : Set.InjOn (fun x => ⌊f x⌋₊) Q := by
    intro x hx y hy hxy
    by_contra hne
    have := floor_eq_close (by linarith [h1 x hx]) (by linarith [h1 y hy]) hxy
    have := hsp x hx y hy hne
    linarith
  have step1 : ∑ x ∈ Q, 1 / f x ≤ ∑ x ∈ Q, ((⌊f x⌋₊ : ℕ) : ℝ)⁻¹ := by
    refine sum_le_sum (fun x hx => ?_)
    have hf1 := h1 x hx
    have hfl : (1 : ℝ) ≤ (⌊f x⌋₊ : ℝ) := by
      have : 1 ≤ ⌊f x⌋₊ := Nat.le_floor (by exact_mod_cast hf1)
      exact_mod_cast this
    rw [one_div]
    exact inv_anti₀ (by linarith) (Nat.floor_le (by linarith))
  have step2 : ∑ x ∈ Q, ((⌊f x⌋₊ : ℕ) : ℝ)⁻¹ = ∑ k ∈ Q.image (fun x => ⌊f x⌋₊), ((k : ℕ) : ℝ)⁻¹ := by
    rw [sum_image hinj]
  have hsub : Q.image (fun x => ⌊f x⌋₊) ⊆ Icc 1 ⌊2 * T⌋₊ := by
    intro k hk
    rw [mem_image] at hk
    obtain ⟨x, hx, rfl⟩ := hk
    rw [mem_Icc]
    exact ⟨Nat.le_floor (by exact_mod_cast h1 x hx), Nat.floor_le_floor (h2 x hx)⟩
  have step3 : ∑ k ∈ Q.image (fun x => ⌊f x⌋₊), ((k : ℕ) : ℝ)⁻¹ ≤ ∑ k ∈ Icc 1 ⌊2 * T⌋₊, ((k : ℕ) : ℝ)⁻¹ :=
    sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  have step4 : Real.log (⌊2 * T⌋₊ : ℝ) ≤ Real.log (2 * T + 1) := by
    rcases Nat.eq_zero_or_pos ⌊2 * T⌋₊ with h0 | h0
    · rw [h0, Nat.cast_zero, Real.log_zero]; exact Real.log_nonneg (by linarith)
    · exact Real.log_le_log (by exact_mod_cast h0) (by linarith [Nat.floor_le (by linarith : (0 : ℝ) ≤ 2 * T)])
  linarith [space_harm ⌊2 * T⌋₊]
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
