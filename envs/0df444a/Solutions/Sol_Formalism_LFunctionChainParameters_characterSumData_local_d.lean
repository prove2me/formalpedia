-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.characterSumData.local_d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:56:39.13409+00:00
-- url     : https://prove2.me/submissions/980d05e8-6fc8-41f2-9263-3a98133146bc

import Definitions.Def_Formalism_SizeWindowBrackets_FirstPrimeNeSecondPrime
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_orthogonality_ramified
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_card_inertia_d

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
theorem _root_.solution (D : ArithData H) (hD : HostFacts D) (N : ℕ) (a : ℝ) (t : H) (w : E0 × H → ℝ) :
    ∑ i ∈ Icc 1 N, (Real.log D.d : ℂ) * ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g),
        Kc D (D.d ^ i) g * Fc a t w (D.d ^ i) g
      = ((Real.log D.d * askD D N a t w : ℝ) : ℂ) := by
  classical
  have hc := card_inertia_d D hD
  have hK : ∀ i, 1 ≤ i → ∀ g, Kc D (D.d ^ i) g
      = if g - i • D.frob D.d ∈ D.inertia D.d then 1 else 0 := by
    intro i hi g
    refine (orthogonality_ramified D D.d i hD.d_prime hi g).trans ?_
    rw [hc]
    split_ifs <;> norm_num
  unfold askD
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  congr 1
  simp_rw [hK i (Finset.mem_Icc.1 hi).1, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  by_cases h1 : InPhi g <;> by_cases h2 : g - i • D.frob D.d ∈ D.inertia D.d <;> simp [h1, h2, Fc]
end Formalism.LFunctionChainParameters.characterSumData
