-- Prove2me | solution 1 for Deduction.CharacterBalance.lunram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:12:05.451266+00:00
-- url     : https://prove2.me/submissions/eb09e057-c446-4e64-841a-fa39195e89c9

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_SplitInertia
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_ChBalance
import Theorems.Thm_Deduction_CharacterBalance_ounram

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Deduction
open Deduction.CH Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
open Deduction.CharacterBalance
open ArithmeticFunction Formalism.LFunctionChainParameters.characterSumData.PB
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Deduction.CharacterBalance
theorem _root_.solution (D : ArithData H) {S0 : Finset ℕ} (hD : HostFactsS D S0) (N : ℕ) (a : ℝ) (t : H) (w : E0 × H → ℝ)
    {p : ℕ} (hp : p.Prime) (h2 : p ∉ S0) (hd : p ≠ D.d) :
    ∑ i ∈ Icc 1 N, (Real.log p : ℂ) * ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g), Kc D (p ^ i) g * Fc a t w (p ^ i) g
      = ((2 * Real.log p * askP D N a t w p : ℝ) : ℂ) := by
  have hR : ((2 * Real.log p * askP D N a t w p : ℝ) : ℂ) = ∑ i ∈ Icc 1 N,
      (if ¬ InPhi (i • D.frob p) then 2 * (Real.log p : ℂ) * ((max (a / (p : ℝ) ^ i - w (partner t (i • D.frob p))) 0 : ℝ) : ℂ)
        else 0) := by
    unfold askP
    rw [Finset.sum_filter, Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl (fun i _ => ?_)
    split_ifs <;> simp
  rw [hR]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi1 : 1 ≤ i := (Finset.mem_Icc.1 hi).1
  have e : ∀ g, Kc D (p ^ i) g = if i • D.frob p = g then 2 else 0 :=
    fun g => ounram D hD p i hp h2 hd hi1 g
  simp only [e, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs with h <;> simp only [Fc, Nat.cast_pow, mul_zero] <;> ring
end Deduction.CharacterBalance
