-- Prove2me | solution 1 for BirkhoffGlobalSection.hamiltonian_radial_contact_continuousAt
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:28:11.367975+00:00
-- url     : https://prove2.me/submissions/cdcc21c5-2d26-4896-8ccc-58e6a4112386

import Theorems.Thm_BirkhoffGlobalSection_convex_model_boundary_contact_positive
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Order.Hom.Set
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.MeanValue
import Theorems.Thm_BirkhoffGlobalSection_hamiltonian_radial_characteristic_normalization

open Set
open scoped Topology ContDiff



set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution
    (F : BirkhoffGlobalSection.Phase → ℝ) (y : BirkhoffGlobalSection.Phase)
    (hF : ContDiffAt ℝ ∞ F y) :
    ContinuousAt (fun x => BirkhoffGlobalSection.phaseRadialContact x
      (BirkhoffGlobalSection.hamiltonianVectorField F x)) y := by
  have hD := (hF.fderiv_right (m := 0) (by simp)).continuousAt
  have hcoord (i : Fin 4) :
      ContinuousAt (fun x => BirkhoffGlobalSection.partialDerivative F x i) y :=
    hD.clm_apply continuousAt_const
  have hX : ContinuousAt (BirkhoffGlobalSection.hamiltonianVectorField F) y := by
    apply continuousAt_pi.mpr
    intro i
    fin_cases i <;> simp [BirkhoffGlobalSection.hamiltonianVectorField] <;>
      first | exact hcoord 2 | exact hcoord 3 | exact (hcoord 0).neg | exact (hcoord 1).neg
  have hAlpha : Continuous (fun p : BirkhoffGlobalSection.Phase × BirkhoffGlobalSection.Phase =>
      BirkhoffGlobalSection.phaseRadialContact p.1 p.2) := by
    unfold BirkhoffGlobalSection.phaseRadialContact BirkhoffGlobalSection.phaseSymplecticForm
    fun_prop
  exact hAlpha.continuousAt.comp (continuousAt_id.prodMk hX)
