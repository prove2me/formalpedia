-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.TW.UnitBall.ballRing_pid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:59:33.250805+00:00
-- url     : https://prove2.me/submissions/16231661-f566-4f57-8230-095d9b5471a7

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_CentralIdempotentIntegral
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_TWUnitBallLattice
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_UnitBall_mem_ballRing
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_UnitBall_norm_unif_pos
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_UnitBall_exists_nat_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.TW
open Formalism.IrreducibleCountingLemmas.TW.UnitBall
variable {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K]
namespace Formalism.IrreducibleCountingLemmas.TW.UnitBall
theorem _root_.solution (ϖ : K) (h1 : ‖ϖ‖ < 1) (hd : ∀ x : K, x ≠ 0 → ∃ n : ℤ, ‖x‖ = ‖ϖ‖ ^ n) :
    IsPrincipalIdealRing (ballRing K) := by
  classical
  have h0 := norm_unif_pos ϖ hd
  refine ⟨fun I => ?_⟩
  by_cases hI : I = ⊥
  · subst hI; exact bot_isPrincipal
  obtain ⟨y, hyI, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hex : ∃ n : ℕ, ∃ x ∈ I, ‖(x : K)‖ = ‖ϖ‖ ^ n := by
    obtain ⟨n, hn⟩ := exists_nat_pow ϖ h1 hd (y : K) (by simpa using hy0) ((mem_ballRing _).mp y.2)
    exact ⟨n, y, hyI, hn⟩
  obtain ⟨x0, hx0I, hx0⟩ := Nat.find_spec hex
  have hx00 : (x0 : K) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hx0
    exact absurd hx0 (pow_pos h0 _).ne
  refine ⟨⟨x0, le_antisymm ?_ ?_⟩⟩
  · intro z hz
    rw [Submodule.mem_span_singleton]
    by_cases hz0 : z = 0
    · exact ⟨0, by simp [hz0]⟩
    obtain ⟨m, hm⟩ := exists_nat_pow ϖ h1 hd (z : K) (by simpa using hz0) ((mem_ballRing _).mp z.2)
    have hle : Nat.find hex ≤ m := Nat.find_min' hex ⟨z, hz, hm⟩
    have hq : (z : K) / x0 ∈ ballRing K := by
      rw [mem_ballRing, norm_div, hm, hx0, div_le_one (pow_pos h0 _)]
      exact pow_le_pow_of_le_one h0.le h1.le hle
    refine ⟨⟨_, hq⟩, ?_⟩
    apply Subtype.ext
    simp [div_mul_cancel₀ _ hx00]
  · rw [Submodule.span_singleton_le_iff_mem]
    exact hx0I
end Formalism.IrreducibleCountingLemmas.TW.UnitBall
