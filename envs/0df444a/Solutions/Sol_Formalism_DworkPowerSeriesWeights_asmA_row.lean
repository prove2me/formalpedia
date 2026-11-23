-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.asmA_row
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:00:09.731797+00:00
-- url     : https://prove2.me/submissions/028cf3d3-7bc5-4ed5-b8aa-9fe2c29e415d

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
theorem _root_.solution {d : ℕ} {ι : Type} (l : ℕ) (sig eps : ZMod d → ℝ) (hsig : ∀ s, 0 ≤ sig s)
    (lt : ι → ZMod d) (isTop : ι → Bool) (spec : ι → Option (ZMod d × ℤ)) (κ : ι → ℕ) (i : ι)
    (htop : isTop i = true → spec i = none) :
    (if isTop i = true then (κ i : ℝ) * (gam l - eps (lt i))
      else (κ i : ℝ) * (gam l - sig (lt i))) - (κ i : ℝ) * asmA_cost l eps (spec i) ≤
      (κ i : ℝ) * (gam l - rowRad l sig eps lt isTop spec i) := by
  have hk : (0 : ℝ) ≤ κ i := Nat.cast_nonneg _
  by_cases ht : isTop i = true
  · rw [if_pos ht, htop ht]
    simp [rowRad, ht, asmA_cost]
  · rw [if_neg ht]
    have hrr : rowRad l sig eps lt isTop spec i ≤ sig (lt i) + asmA_cost l eps (spec i) := by
      unfold rowRad
      rw [if_neg ht]
      rcases hsp : spec i with _ | ⟨s, j⟩
      · simp [asmA_cost]
      · simp only [asmA_cost]
        split_ifs with hj
        · exact max_le (le_add_of_nonneg_right (le_max_right _ _))
            (by linarith [le_max_left (1 - (l : ℝ) ^ j.toNat * eps s) 0, hsig (lt i)])
        · exact max_le (le_add_of_nonneg_right (by positivity)) (le_add_of_nonneg_left (hsig _))
    nlinarith [mul_le_mul_of_nonneg_left hrr hk]
end Formalism.DworkPowerSeriesWeights
