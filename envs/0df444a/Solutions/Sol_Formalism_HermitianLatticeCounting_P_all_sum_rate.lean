-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.all_sum_rate
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:44.971865+00:00
-- url     : https://prove2.me/submissions/57828eb3-fc05-427a-82d3-2a8d25bfc410

import Definitions.Def_Formalism_FlagUnipotentLattices_CoveringRadius2
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_NuclearNormBoundHolds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_NearFarVolumeBounds
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_layer_sum_b
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_geom_partial_le_b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset MeasureTheory NumberField Matrix
open scoped ComplexOrder
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.S7
open Formalism.NuclearRankWeightBounds.D (lead hs q0)
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : AllSumRate := by
  intro ι Γ _ _ S d A B h q hq hA hB hh hd hcount
  have hq' : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hs1 : 1 ≤ Real.sqrt (2 * (q:ℝ)) := by
    rw [Real.one_le_sqrt]; linarith
  have hs0 : 0 < Real.sqrt (2 * (q:ℝ)) := by linarith
  have hh0 : 0 ≤ h := le_trans (by positivity) hh
  have hx1 : Real.exp (-B) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  refine layer_sum_b ι Γ S d A B _ (fun t => Real.exp (-(decExp h q t))) (fun i => (i:ℝ) + 1)
    (fun i => Real.exp (-(2 * B * i))) hA (fun i => by positivity) (fun i => (Real.exp_pos _).le)
    (fun t => (Real.exp_pos _).le) ?_ hd hcount ?_
  · intro t ht
    refine ⟨⌈t⌉₊ - 1, ?_, ?_⟩
    · have h1 := Nat.le_ceil t
      have h2 : (⌈t⌉₊ : ℝ) ≤ ((⌈t⌉₊ - 1 : ℕ) : ℝ) + 1 := by
        have : ⌈t⌉₊ ≤ (⌈t⌉₊ - 1) + 1 := by omega
        exact_mod_cast this
      linarith
    · rw [Real.exp_le_exp, neg_le_neg_iff]
      unfold decExp
      rcases Nat.eq_zero_or_pos (⌈t⌉₊ - 1) with h0 | h0
      · rw [h0]
        simp only [Nat.cast_zero, mul_zero]
        have : 0 ≤ min (t ^ 2) (t / Real.sqrt (2 * (q:ℝ))) := le_min (by positivity) (by positivity)
        positivity
      · have hlt : ((⌈t⌉₊ - 1 : ℕ) : ℝ) < t := by
          rw [← Nat.lt_ceil]; omega
        have hi1 : (1:ℝ) ≤ ((⌈t⌉₊ - 1 : ℕ) : ℝ) := by exact_mod_cast h0
        set i : ℝ := ((⌈t⌉₊ - 1 : ℕ) : ℝ) with hi
        have ht1 : 1 ≤ t := by linarith
        have hmin : i / Real.sqrt (2 * (q:ℝ)) ≤ min (t ^ 2) (t / Real.sqrt (2 * (q:ℝ))) := by
          apply le_min
          · calc i / Real.sqrt (2 * (q:ℝ)) ≤ i := div_le_self (by linarith) hs1
              _ ≤ t ^ 2 := by nlinarith
          · gcongr
        calc 2 * B * i = (16 * B * Real.sqrt (2 * (q:ℝ))) / 8 * (i / Real.sqrt (2 * (q:ℝ))) := by
              field_simp; ring
          _ ≤ h / 8 * (i / Real.sqrt (2 * (q:ℝ))) := by gcongr
          _ ≤ _ := by gcongr
  · intro M
    have e : ∀ i : ℕ, Real.exp (-(2 * B * i)) * Real.exp (B * ((i:ℝ) + 1)) = Real.exp B * Real.exp (-B) ^ i := by
      intro i
      rw [← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
    simp_rw [e]
    rw [← Finset.mul_sum, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left (geom_partial_le_b _ (Real.exp_pos _).le hx1 M) (Real.exp_pos _).le
end Formalism.HermitianLatticeCounting.P
