-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.gauss_sum_share
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:49:04.70507+00:00
-- url     : https://prove2.me/submissions/55740ab2-c5e6-427a-a72d-91e1f5b40675

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_y_facts
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_gauss_core
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_cast
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_cast
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_last



set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution : GaussShare := by
  refine ⟨3, ?_⟩
  intro U T _ _ _ _ Q χ cond q a ρ hq hρ hT hc0 hcnt hχ hS1 hS2
  obtain ⟨hy, hy0, hy8⟩ := y_facts q ρ hq hρ
  have c1 := gauss_core Q (fun _ => 1) cond q a ρ hq hρ hT hc0 hcnt (by simpa using hS2)
  have c2 := gauss_core Q χ cond q a ρ hq hρ hT hc0 hcnt hS1
  set y : ℝ := (q : ℝ) ^ (1 - (ρ : ℤ))
  set u0 : ℝ := (Fintype.card U : ℝ) / (q : ℝ) ^ a with hu0
  have hu00 : 0 ≤ u0 := by positivity
  rw [hχ, zero_div, sub_zero] at c2
  have e1 : (∑ u ∈ univ.filter (fun u => Q u = 0), (1 : ℂ)) - (∑ u : U, (1 : ℂ)) / ((q : ℂ) ^ a)
      = ((((univ.filter fun u => Q u = 0).card : ℝ) - u0 : ℝ) : ℂ) := by
    simp [hu0]
  rw [e1, Complex.norm_real, Real.norm_eq_abs] at c1
  have hyu : 0 ≤ y * u0 := mul_nonneg hy0 hu00
  refine ⟨c1.trans (by nlinarith), c2.trans ?_⟩
  have := (abs_le.1 c1).1
  have h3 : y * u0 ≤ u0 / 8 := by nlinarith
  have h4 : (3 / 4) * u0 ≤ ((univ.filter fun u => Q u = 0).card : ℝ) := by nlinarith
  have h5 : y * ((3 / 4) * u0) ≤ y * ((univ.filter fun u => Q u = 0).card : ℝ) :=
    mul_le_mul_of_nonneg_left h4 hy0
  nlinarith
end Formalism.HermitianLatticeCounting.P.S4aux
