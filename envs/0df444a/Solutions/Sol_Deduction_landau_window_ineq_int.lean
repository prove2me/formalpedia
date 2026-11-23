-- Prove2me | solution 1 for Deduction.landau_window_ineq_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:37:20.628795+00:00
-- url     : https://prove2.me/submissions/f9db5f70-14aa-465e-91c3-9c1ac986af7c

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauZeroFreeCriterion
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_LandauKernelMax
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_landauWindowIneq
import Theorems.Thm_Deduction_landau_kernel_max


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Deduction
namespace Deduction
theorem _root_.solution (k : ℕ) {σ : ℝ} (hσ : 2 < σ) :
    IntegrableOn (fun u : ℝ => u ^ k * Real.exp ((2 - σ) * u) / (k.factorial : ℝ)) (Ioi 0) := by
  have ha : 0 < (σ - 2) / 2 := by linarith
  have h1 : IntegrableOn (fun u : ℝ => (1 / ((σ - 2) / 2) ^ k) * Real.exp (-((σ - 2) / 2) * u)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 ha).const_mul _
  refine Integrable.mono' h1 (by fun_prop) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
  have hu0 : 0 ≤ u := le_of_lt hu
  rw [Real.norm_of_nonneg (by positivity)]
  have h2 := landau_kernel_max k ha hu0
  have h3 : u ^ k * Real.exp ((2 - σ) * u) / (k.factorial : ℝ)
      = (u ^ k * Real.exp (-((σ - 2) / 2) * u) / (k.factorial : ℝ)) * Real.exp (-((σ - 2) / 2) * u) := by
    have : (2 - σ) * u = -((σ - 2) / 2) * u + -((σ - 2) / 2) * u := by ring
    rw [this, Real.exp_add]; ring
  rw [h3]
  exact mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
end Deduction
