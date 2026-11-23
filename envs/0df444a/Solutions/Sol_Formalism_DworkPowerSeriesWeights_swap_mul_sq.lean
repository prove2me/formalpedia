-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.swap_mul_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:09:05.395477+00:00
-- url     : https://prove2.me/submissions/7eb2352e-c1b6-4e30-ac50-4a72a4487adb

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffQuadSer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
open Formalism Formalism.DworkPowerSeriesWeights
variable {n : ℕ}
variable {R : Type u} [CommRing R]
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {a b : Fin n} {τ : Equiv.Perm (Fin n)} (hτ : τ * τ = 1)
    (h : Equiv.swap (τ a) (τ b) = Equiv.swap a b) :
    (Equiv.swap a b * τ) * (Equiv.swap a b * τ) = 1 := by
  have hc : τ * Equiv.swap a b = Equiv.swap a b * τ := by
    rw [Equiv.mul_swap_eq_swap_mul, h]
  calc (Equiv.swap a b * τ) * (Equiv.swap a b * τ)
      = Equiv.swap a b * (τ * Equiv.swap a b) * τ := by simp only [mul_assoc]
    _ = (Equiv.swap a b * Equiv.swap a b) * (τ * τ) := by rw [hc]; simp only [mul_assoc]
    _ = 1 := by rw [hτ, Equiv.swap_mul_self, one_mul]
end Formalism.DworkPowerSeriesWeights
