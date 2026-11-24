-- Prove2me | solution 1 for Deduction.CharacterBalance.lsplit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:56:34.830316+00:00
-- url     : https://prove2.me/submissions/396b70bd-a077-44d8-abcd-ce82594141e6

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_SplitInertia
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_ChBalance
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
open Finset
noncomputable section
open Deduction
open Deduction.CH Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
open Deduction.CharacterBalance
open ArithmeticFunction Formalism.LFunctionChainParameters.characterSumData.PB
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Deduction.CharacterBalance
theorem _root_.solution (D : ArithData H) {S0 : Finset ℕ} (hD : HostFactsS D S0) (N : ℕ) (a : ℝ) (t : H) (w : E0 × H → ℝ)
    {p : ℕ} (hp : p.Prime) (h2 : p ∈ S0) :
    ∑ i ∈ Icc 1 N, (Real.log p : ℂ) * ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g), Kc D (p ^ i) g * Fc a t w (p ^ i) g
      = 0 := by
  classical
  refine Finset.sum_eq_zero (fun i hi => ?_)
  have hi1 : 1 ≤ i := (Finset.mem_Icc.1 hi).1
  rw [Finset.sum_eq_zero, mul_zero]
  intro g hg
  have hg' := (Finset.mem_filter.1 hg).2
  have e := orthogonality_ramified D p i hp hi1 g
  unfold Kc
  rw [e]
  have : ¬ (g - i • D.frob p ∈ D.inertia p) := by
    intro hm
    apply hg'
    have hx := hD.split_inertia p h2 _ hm
    have hf := inPhi_nsmul (hD.split_frob p h2) i
    have := inPhi_add hx hf
    simpa using this
  simp [this]
end Deduction.CharacterBalance
