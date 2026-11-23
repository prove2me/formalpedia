-- Prove2me | solution 1 for Formalism.ELL.MultiplicativeWeight.W_E
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:58.006802+00:00
-- url     : https://prove2.me/submissions/bf9d5e2c-5ef4-4da1-a817-8ee8d3f29bda

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_CompExpWeight
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CompExp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries IsUltrametricDist
universe u
open Formalism Formalism.ELL Formalism.ELL.MultiplicativeWeight
variable {K : Type*} [NormedField K] [IsUltrametricDist K] {σ : Type} (c : ℝ)
variable {c}
namespace Formalism.ELL.MultiplicativeWeight
theorem _root_.solution (E : PowerSeries K) (hE : constantCoeff E = 0)
    (hb : ∀ n : ℕ, 1 ≤ n → ‖coeff n E‖ ≤ c ^ (1 - (n : ℤ))) (hc : 0 < c) (i : σ) :
    W c 1 (E.subst (MvPowerSeries.X i : MvPowerSeries σ K)) := by
  classical
  intro e
  rw [PowerSeries.coeff_subst_single]
  split_ifs with h
  · rcases Nat.eq_zero_or_pos (e i) with h0 | h0
    · rw [h0, coeff_zero_eq_constantCoeff_apply, hE, norm_zero]; positivity
    · conv_rhs => rw [h, Finsupp.degree_single]
      exact hb _ h0
  · rw [norm_zero]; positivity
end Formalism.ELL.MultiplicativeWeight
