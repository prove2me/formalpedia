-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.characterSumData.local_unram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:12:07.429901+00:00
-- url     : https://prove2.me/submissions/e0a9ddbf-9338-4b61-b08f-92db66507c42

import Definitions.Def_Formalism_SizeWindowBrackets_FirstPrimeNeSecondPrime
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_orthogonality_unramified

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.characterSumData
open Formalism Formalism.D5
open PB
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Formalism.LFunctionChainParameters.characterSumData
theorem _root_.solution (D : ArithData H) (hD : HostFacts D) (N : ℕ) (a : ℝ) (t : H) (w : E0 × H → ℝ)
    {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (hq : p ≠ D.q1) (hd : p ≠ D.d) :
    ∑ i ∈ Icc 1 N, (Real.log p : ℂ) * ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g), Kc D (p ^ i) g * Fc a t w (p ^ i) g
      = ((2 * Real.log p * askP D N a t w p : ℝ) : ℂ) := by
  have hK : ∀ i, 1 ≤ i → ∀ g, Kc D (p ^ i) g = if i • D.frob p = g then 2 else 0 :=
    fun i hi g => orthogonality_unramified D hD p i hp h2 hq hd hi g
  have hin : ∀ i ∈ Icc 1 N, (Real.log p : ℂ) * ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g),
        Kc D (p ^ i) g * Fc a t w (p ^ i) g
      = (((if ¬ InPhi (i • D.frob p) then
          2 * Real.log p * max (a / (p : ℝ) ^ i - w (partner t (i • D.frob p))) 0 else 0) : ℝ) : ℂ) := by
    intro i hi
    simp_rw [hK i (Finset.mem_Icc.1 hi).1, ite_mul, zero_mul]
    simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs <;> first
      | (simp; done)
      | (simp only [Fc]; push_cast; ring)
  rw [Finset.sum_congr rfl hin, ← Complex.ofReal_sum]
  congr 1
  unfold askP
  rw [Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  split_ifs <;> ring
end Formalism.LFunctionChainParameters.characterSumData
