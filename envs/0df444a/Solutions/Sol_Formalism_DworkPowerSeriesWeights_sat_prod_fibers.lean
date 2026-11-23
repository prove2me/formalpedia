-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.sat_prod_fibers
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:55.589847+00:00
-- url     : https://prove2.me/submissions/ada74b21-bd04-4f53-989d-4baa74d6abb1

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementS
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SlopeBoundSaturation
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MvPolynomial
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.GradedWeylDivisibility
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {A : Type} [CommMonoid A] {n k : ℕ} (sz : Fin k → ℕ) (hsz : ∀ i, sz i ≤ n) (G : Fin k → A)
    (hG : ∀ i, sz i = 0 → G i = 1) :
    ∏ i, G i = ∏ j ∈ Finset.range n, ∏ i : {i // sz i = j + 1}, G i.1 := by
  classical
  rw [← Finset.prod_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.range (n + 1)) (g := sz)
    (fun i _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (hsz i))), Finset.prod_range_succ']
  rw [Finset.prod_eq_one (s := Finset.univ.filter fun i => sz i = 0)
    (fun i hi => hG i (Finset.mem_filter.mp hi).2), mul_one]
  refine Finset.prod_congr rfl fun j _ => ?_
  exact Finset.prod_subtype _ (fun i => by simp) _
end Formalism.DworkPowerSeriesWeights
