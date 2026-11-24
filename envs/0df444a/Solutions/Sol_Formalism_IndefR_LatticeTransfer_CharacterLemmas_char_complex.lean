-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.CharacterLemmas.char_complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:48:32.802109+00:00
-- url     : https://prove2.me/submissions/f3aba74f-9429-4a46-a44d-3699f9f8db05

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransfer
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_TraceOfDiag
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_CharacterLemmas_eigen_data

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.LatticeTransfer
open Formalism.IndefR.TransferLatticeStatement
open Formalism.IndefR.LatticeTransfer.CharacterLemmas
namespace Formalism.IndefR.LatticeTransfer.CharacterLemmas
theorem _root_.solution {G V : Type} [Group G] [Finite G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (g : G) :
    IsIntegral ℤ (LinearMap.trace ℂ V (ρ g)) ∧
      LinearMap.trace ℂ V (ρ g⁻¹) = star (LinearMap.trace ℂ V (ρ g)) ∧
      ‖LinearMap.trace ℂ V (ρ g)‖ ≤ (finrank ℂ V : ℝ) := by
  obtain ⟨I, hI, μ, hcard, hμ, htr, htr'⟩ := eigen_data ρ g
  have hn : orderOf g ≠ 0 := (orderOf_pos g).ne'
  refine ⟨?_, ?_, ?_⟩
  · rw [htr]
    refine IsIntegral.sum _ fun i _ => ?_
    refine IsIntegral.of_pow (orderOf_pos g) ?_
    rw [hμ i]
    exact isIntegral_one
  · rw [htr', htr, star_sum]
    rfl
  · rw [htr]
    calc ‖∑ i, μ i‖ ≤ ∑ i, ‖μ i‖ := norm_sum_le _ _
      _ = ∑ _i : I, (1 : ℝ) := Finset.sum_congr rfl fun i _ => by
          have h1 : ‖μ i‖ ^ orderOf g = 1 := by rw [← norm_pow, hμ i, norm_one]
          exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 h1
      _ = (finrank ℂ V : ℝ) := by simp [hcard]
end Formalism.IndefR.LatticeTransfer.CharacterLemmas
