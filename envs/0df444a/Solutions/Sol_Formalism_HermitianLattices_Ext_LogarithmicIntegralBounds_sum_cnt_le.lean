-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.sum_cnt_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:39:46.249984+00:00
-- url     : https://prove2.me/submissions/bd311bfd-0aa3-4cf2-94c5-d98ccc8baaf3

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
theorem _root_.solution (m₀ s a₀ : ℕ) (X : ℝ) :
    (∑ b ∈ clsB m₀ s a₀, (((PPset m₀ a₀ X).filter (fun q => q % (m₀ * s) = b)).card : ℝ)) ≤
      ((PPset m₀ a₀ X).card : ℝ) := by
  exact_mod_cast sum_card_filter_mod_le_card (PPset m₀ a₀ X) (clsB m₀ s a₀) (m₀ * s)
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
