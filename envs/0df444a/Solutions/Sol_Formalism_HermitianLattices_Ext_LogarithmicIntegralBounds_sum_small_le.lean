-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.sum_small_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:28:24.957623+00:00
-- url     : https://prove2.me/submissions/084e3f73-686a-4b01-bebd-86bc4887aaae

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqCount
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqOrth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqTwistA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset Classical
noncomputable section
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open Formalism.HermitianLattices.ZeroFreeRegionGL2
private theorem sum_card_filter_mod_le_card (T B : Finset ℕ) (M : ℕ) :
    ∑ b ∈ B, (T.filter (fun p => p % M = b)).card ≤ T.card := by
  calc ∑ b ∈ B, (T.filter (fun p => p % M = b)).card
      = ∑ b ∈ B, ∑ p ∈ T, if p % M = b then 1 else 0 := by simp only [Finset.card_filter]
    _ = ∑ p ∈ T, ∑ b ∈ B, if p % M = b then 1 else 0 := Finset.sum_comm
    _ = ∑ p ∈ T, if p % M ∈ B then 1 else 0 := by simp only [Finset.sum_ite_eq]
    _ ≤ ∑ p ∈ T, 1 := Finset.sum_le_sum (fun p _ => by split_ifs <;> simp)
    _ = T.card := by simp
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
end
end

set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open Formalism.HermitianLattices.ZeroFreeRegionGL2
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
theorem _root_.solution (m₀ s a₀ : ℕ) (X : ℝ) (hX : 0 ≤ X) :
    (∑ b ∈ clsB m₀ s a₀, (smallCnt X (m₀ * s) b : ℝ)) ≤ X ^ (1 / 2 : ℝ) := by
  have h1 : ∑ b ∈ clsB m₀ s a₀, smallCnt X (m₀ * s) b ≤
      ((Finset.Icc (1 : ℕ) ⌊X⌋₊).filter (fun p : ℕ => p.Prime ∧ (p : ℝ) ≤ X ^ (1 / 2 : ℝ))).card :=
    sum_card_filter_mod_le_card _ _ _
  have h2 : ((Finset.Icc (1 : ℕ) ⌊X⌋₊).filter
      (fun p : ℕ => p.Prime ∧ (p : ℝ) ≤ X ^ (1 / 2 : ℝ))).card ≤ ⌊X ^ (1 / 2 : ℝ)⌋₊ := by
    calc _ ≤ (Finset.Icc (1 : ℕ) ⌊X ^ (1 / 2 : ℝ)⌋₊).card := by
          apply Finset.card_le_card
          intro p hp
          simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
          exact ⟨hp.1.1, Nat.le_floor hp.2.2⟩
      _ = ⌊X ^ (1 / 2 : ℝ)⌋₊ := by simp
  have h3 : (⌊X ^ (1 / 2 : ℝ)⌋₊ : ℝ) ≤ X ^ (1 / 2 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg hX _)
  have h4 : ((∑ b ∈ clsB m₀ s a₀, smallCnt X (m₀ * s) b : ℕ) : ℝ) ≤ (⌊X ^ (1 / 2 : ℝ)⌋₊ : ℝ) := by
    exact_mod_cast h1.trans h2
  push_cast at h4
  linarith
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
