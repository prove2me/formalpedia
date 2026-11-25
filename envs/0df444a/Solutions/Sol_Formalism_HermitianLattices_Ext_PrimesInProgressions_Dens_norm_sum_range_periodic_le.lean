-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.norm_sum_range_periodic_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:37:14.264603+00:00
-- url     : https://prove2.me/submissions/4ccddda1-25ca-43b8-afee-e6a6f7f67b09

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensSt
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LGrowth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensPair

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
theorem _root_.solution {M : ℕ} [NeZero M] (h : ZMod M → ℂ) {K : ℝ} (hK : ∀ a, ‖h a‖ ≤ K)
    (h0 : ∑ a : ZMod M, h a = 0) (k : ℕ) : ‖∑ n ∈ range k, h (n : ZMod M)‖ ≤ K * M := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  have hq : ∑ n ∈ range M, h (n : ZMod M) = 0 := by
    rw [← h0]
    refine Finset.sum_bij' (fun n _ => (n : ZMod M)) (fun a _ => a.val) ?_ ?_ ?_ ?_ ?_
    · intro n _; exact Finset.mem_univ _
    · intro a _; exact Finset.mem_range.mpr (ZMod.val_lt a)
    · intro n hn; exact ZMod.val_cast_of_lt (Finset.mem_range.mp hn)
    · intro a _; exact ZMod.natCast_zmod_val a
    · intro n _; rfl
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hM : M ≤ k
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hM
      have : ∑ n ∈ range (M + j), h (n : ZMod M) = ∑ n ∈ range j, h (n : ZMod M) := by
        rw [Finset.sum_range_add, hq, zero_add]
        refine Finset.sum_congr rfl ?_
        intro x _
        congr 1
        push_cast
        simp
      rw [this]
      exact ih j (by have := NeZero.pos M; omega)
    · push Not at hM
      calc ‖∑ n ∈ range k, h (n : ZMod M)‖ ≤ ∑ n ∈ range k, ‖h (n : ZMod M)‖ := norm_sum_le _ _
        _ ≤ ∑ n ∈ range k, K := Finset.sum_le_sum (fun n _ => hK _)
        _ = K * k := by simp [mul_comm]
        _ ≤ K * M := mul_le_mul_of_nonneg_left (by exact_mod_cast hM.le) hK0
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
