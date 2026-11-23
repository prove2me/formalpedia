-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.capacity_le_reachCapacity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:58:10.875987+00:00
-- url     : https://prove2.me/submissions/a90b6878-7972-4284-a4a7-7b794d67db7f

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementA
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_PadicValFactorialRatioProd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_CapacityLeReachCapacity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (l d : ℕ) [NeZero d] (TT : Finset (ZMod d)) (nu1 nu2 size : ZMod d → ℕ)
    (s : ZMod d) (j : ℤ) (hj : j < 0) (hodd : Odd j)
    (hsz : l ^ (-j).toNat ≤ size (s + (j : ZMod d))) :
    capL d TT nu1 nu2 (s + (j : ZMod d)) ≤ Wcap l d TT nu1 nu2 size s := by
  have hnn : ((-j).toNat : ℤ) = -j := Int.toNat_of_nonneg (by omega)
  have hi : Odd (-j).toNat := by
    have ho : Odd (((-j).toNat : ℕ) : ℤ) := by rw [hnn]; exact hodd.neg
    exact (Int.odd_coe_nat _).mp ho
  have hsj : s - (((-j).toNat : ℕ) : ZMod d) = s + (j : ZMod d) := by
    rw [show (((-j).toNat : ℕ) : ZMod d) = ((((-j).toNat : ℕ) : ℤ) : ZMod d) from
      (Int.cast_natCast _).symm, hnn, Int.cast_neg, sub_neg_eq_add]
  unfold Wcap
  apply le_csSup
  · refine (Set.finite_range (fun t : ZMod d => capL d TT nu1 nu2 t)).bddAbove.mono ?_
    rintro _ ⟨i, _, rfl⟩
    exact ⟨_, rfl⟩
  · refine ⟨(-j).toNat, ⟨hi, ?_⟩, ?_⟩
    · show l ^ (-j).toNat ≤ size (s - (((-j).toNat : ℕ) : ZMod d))
      rw [hsj]
      exact hsz
    · simp only [hsj]
end Formalism.DworkPowerSeriesWeights
