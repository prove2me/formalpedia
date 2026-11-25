-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.divSq_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:24:07.681801+00:00
-- url     : https://prove2.me/submissions/163b7a0f-1c40-4c9c-aff0-e81993c6c3c4

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZMoll
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensDiv

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
theorem _root_.solution (x : ℕ) : ∑ n ∈ Icc 1 x, ((n.divisors.card : ℕ) : ℝ) ^ 2 =
    ∑ p ∈ Icc 1 x ×ˢ Icc 1 x, ((x / Nat.lcm p.1 p.2 : ℕ) : ℝ) := by
  have h1 : ∀ n ∈ Icc 1 x, ((n.divisors.card : ℕ) : ℝ) ^ 2 =
      ∑ p ∈ Icc 1 x ×ˢ Icc 1 x, if Nat.lcm p.1 p.2 ∣ n then (1 : ℝ) else 0 := by
    intro n hn
    rw [mem_Icc] at hn
    have hd : n.divisors = (Icc 1 x).filter (· ∣ n) := by
      ext a
      simp only [Nat.mem_divisors, mem_filter, mem_Icc]
      constructor
      · rintro ⟨h, h0⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos h (by omega), (Nat.le_of_dvd (by omega) h).trans hn.2⟩, h⟩
      · rintro ⟨_, h⟩
        exact ⟨h, by omega⟩
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, sq, ← Nat.cast_mul,
      ← card_product, hd, ← filter_product]
    congr 2
    ext p
    simp [Nat.lcm_dvd_iff]
  rw [sum_congr rfl h1, sum_comm]
  refine sum_congr rfl fun p _ => ?_
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one, ← Nat.Ioc_filter_dvd_card_eq_div]
  rfl
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
