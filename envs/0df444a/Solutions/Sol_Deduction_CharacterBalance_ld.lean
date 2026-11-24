-- Prove2me | solution 1 for Deduction.CharacterBalance.ld
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:56:40.832849+00:00
-- url     : https://prove2.me/submissions/faa861cc-b0aa-40a1-bef7-7e09bd5cc9df

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_SplitInertia
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_ChBalance
import Theorems.Thm_Deduction_CharacterBalance_cardI
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_orthogonality_ramified


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
theorem _root_.solution (D : ArithData H) {S0 : Finset ℕ} (hD : HostFactsS D S0) (N : ℕ) (a : ℝ) (t : H) (w : E0 × H → ℝ) :
    ∑ i ∈ Icc 1 N, (Real.log D.d : ℂ) * ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g),
        Kc D (D.d ^ i) g * Fc a t w (D.d ^ i) g
      = ((Real.log D.d * askD D N a t w : ℝ) : ℂ) := by
  classical
  unfold askD
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi1 : 1 ≤ i := (Finset.mem_Icc.1 hi).1
  congr 1
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  have e := orthogonality_ramified D D.d i hD.d_prime hi1 g
  unfold Kc
  rw [e, cardI D hD]
  unfold Fc
  by_cases hφ : InPhi g
  · simp [hφ]
  · by_cases hm : g - i • D.frob D.d ∈ D.inertia D.d
    · simp [hφ, hm]
    · simp [hφ, hm]
end Deduction.CharacterBalance
