-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.characterSumData.card_inertia_d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:30:45.221606+00:00
-- url     : https://prove2.me/submissions/f8b016b9-85d9-4cc7-bc97-f0e52150f389

import Definitions.Def_Formalism_SizeWindowBrackets_FirstPrimeNeSecondPrime
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_natCard_eq_filter

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
theorem _root_.solution (D : ArithData H) (hD : HostFacts D) : (Nat.card (D.inertia D.d) : ℂ) = 2 := by
  classical
  have h0 : (0 : E0 × H) ≠ sgc0 := by
    intro h
    have h' : (0 : E0 × H).1.1 = (sgc0 : E0 × H).1.1 := by rw [h]
    simp [sgc0] at h'
  have hs : (univ.filter (fun x : E0 × H => x ∈ D.inertia D.d)) = {0, sgc0} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    exact hD.inertia_d x
  have hc : Nat.card (D.inertia D.d) = 2 := by
    rw [natCard_eq_filter, hs, Finset.card_pair h0]
  exact_mod_cast hc
end Formalism.LFunctionChainParameters.characterSumData
