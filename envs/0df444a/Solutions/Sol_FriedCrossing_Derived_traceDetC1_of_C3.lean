-- Prove2me | solution 1 for FriedCrossing.Derived.traceDetC1_of_C3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:08:18.429091+00:00
-- url     : https://prove2.me/submissions/59320fc4-ebb6-4f06-80b5-0b6a6578be26

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Theorems.Thm_FriedCrossing_Derived_hasDerivAt_trace_Ndiv
import Theorems.Thm_FriedCrossing_Derived_hasDerivAt_det_Ndiv
import Theorems.Thm_P2M_FriedCrossing_Derived_continuousAt_a__6cdfbca45661
import Theorems.Thm_P2M_FriedCrossing_Derived_continuousAt_b__01d39ee2131f

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Derived
open Regularity HQuot Hadamard ClusterMatrix Ledger
variable {M : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ} {A : ℝ → ℝ → Matrix (Fin 4) (Fin 4) ℝ}
  {sStar : ℝ → ℝ}
namespace FriedCrossing.Derived
theorem _root_.solution (h : ClusterC3 M A)
    (hsemi : ∀ θ, M θ 0 = sStar θ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) :
    TraceDetC1 M (Mτ M) sStar (aτ M) (bτ M sStar) where
  deriv_a := hasDerivAt_trace_Ndiv h hsemi
  deriv_b := hasDerivAt_det_Ndiv h hsemi
  cont_a' := continuousAt_aτ h
  cont_b' := continuousAt_bτ h hsemi
end FriedCrossing.Derived
