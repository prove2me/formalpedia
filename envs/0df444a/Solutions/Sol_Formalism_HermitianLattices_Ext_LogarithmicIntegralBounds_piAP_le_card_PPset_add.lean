-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.piAP_le_card_PPset_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:28:22.458871+00:00
-- url     : https://prove2.me/submissions/4dc4b496-53c0-4618-9867-7f3ef1825533

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open Formalism.HermitianLattices.ZeroFreeRegionGL2
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
theorem _root_.solution (X : ℝ) (m₀ a₀ : ℕ) (hX : 1 ≤ X) :
    (piAP X m₀ a₀ : ℝ) ≤ ((PPset m₀ a₀ X).card : ℝ) + X ^ (1 / 2 : ℝ) := by
  have hs : (0:ℝ) ≤ X ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
  have key : piAP X m₀ a₀ ≤ (PPset m₀ a₀ X).card + ⌊X ^ (1 / 2 : ℝ)⌋₊ := by
    unfold piAP
    calc _ ≤ (PPset m₀ a₀ X ∪ Icc 1 ⌊X ^ (1 / 2 : ℝ)⌋₊).card := by
          apply Finset.card_le_card
          intro q hq
          simp only [PPset, Finset.mem_union, Finset.mem_filter, Finset.mem_Icc] at hq ⊢
          by_cases h : X ^ (1 / 2 : ℝ) < (q : ℝ)
          · exact Or.inl ⟨hq.1, hq.2.1, hq.2.2, h⟩
          · exact Or.inr ⟨hq.1.1, Nat.le_floor (not_lt.mp h)⟩
      _ ≤ (PPset m₀ a₀ X).card + (Icc 1 ⌊X ^ (1 / 2 : ℝ)⌋₊).card := Finset.card_union_le _ _
      _ = (PPset m₀ a₀ X).card + ⌊X ^ (1 / 2 : ℝ)⌋₊ := by simp
  have h3 : ((⌊X ^ (1 / 2 : ℝ)⌋₊ : ℕ) : ℝ) ≤ X ^ (1 / 2 : ℝ) := Nat.floor_le hs
  have key' : (piAP X m₀ a₀ : ℝ) ≤ ((PPset m₀ a₀ X).card : ℝ) + (⌊X ^ (1 / 2 : ℝ)⌋₊ : ℝ) := by
    exact_mod_cast key
  linarith
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
