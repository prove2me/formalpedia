-- Prove2me | solution 1 for Formalism.G.LogCR.pderiv_aeval
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:09:33.513082+00:00
-- url     : https://prove2.me/submissions/6df4b8a2-8745-4f44-8352-5f9876c46cc1

import Mathlib
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open Formalism Formalism.G Formalism.G.LogCR
variable {R : Type*} [CommRing R] {σ τ : Type*}
namespace Formalism.G.LogCR
theorem _root_.solution [Fintype σ] (p : MvPolynomial σ R) (A : σ → MvPowerSeries τ R) (i : τ) :
    MvPowerSeries.pderiv R i (MvPolynomial.aeval A p) =
      ∑ j, MvPolynomial.aeval A (MvPolynomial.pderiv j p) * MvPowerSeries.pderiv R i (A j) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p j hp =>
    simp only [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X, map_add, map_mul,
      MvPolynomial.aeval_X, add_mul, Finset.sum_add_distrib]
    rw [Derivation.leibniz, hp, smul_eq_mul, smul_eq_mul]
    rw [add_comm]
    congr 1
    · rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    · simp [Pi.single_apply, apply_ite (MvPolynomial.aeval A), mul_ite, ite_mul]
end Formalism.G.LogCR
