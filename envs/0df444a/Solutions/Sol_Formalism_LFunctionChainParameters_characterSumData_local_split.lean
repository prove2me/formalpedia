-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.characterSumData.local_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:56:39.794968+00:00
-- url     : https://prove2.me/submissions/c39e2de3-1814-4540-8f37-a9bdafea36dd

import Definitions.Def_Formalism_SizeWindowBrackets_FirstPrimeNeSecondPrime
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_PB_inPhi_add
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_PB_inPhi_nsmul
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_orthogonality_ramified

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
    {p : ℕ} (hp : p.Prime) (h2 : p = 2 ∨ p = D.q1) :
    ∑ i ∈ Icc 1 N, (Real.log p : ℂ) * ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g), Kc D (p ^ i) g * Fc a t w (p ^ i) g
      = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  have hi1 : 1 ≤ i := (Finset.mem_Icc.1 hi).1
  rw [Finset.sum_eq_zero, mul_zero]
  intro g hg
  have hg' : ¬ InPhi g := (Finset.mem_filter.1 hg).2
  have hK : Kc D (p ^ i) g = 0 := by
    refine (orthogonality_ramified D p i hp hi1 g).trans ?_
    rw [if_neg]
    intro hm
    apply hg'
    have h1 := hD.split_inertia p h2 _ hm
    have h3 := inPhi_nsmul (hD.split_frob p h2) i
    have h4 := inPhi_add h1 h3
    rwa [sub_add_cancel] at h4
  rw [hK, zero_mul]
end Formalism.LFunctionChainParameters.characterSumData
