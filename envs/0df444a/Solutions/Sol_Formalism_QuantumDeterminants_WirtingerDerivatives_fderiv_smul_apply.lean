-- Prove2me | solution 1 for Formalism.QuantumDeterminants.WirtingerDerivatives.fderiv_smul_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:59.578795+00:00
-- url     : https://prove2.me/submissions/6bfa6a6d-df37-46b6-92b8-d97ab9d476de

import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_WRWeyl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff Topology
open Filter
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.QuantumDeterminants.WirtingerDerivatives
variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.QuantumDeterminants.WirtingerDerivatives
theorem _root_.solution {a : (Fin m → ℂ) → ℂ} {h : (Fin m → ℂ) → E} {x : Fin m → ℂ}
    (ha : DifferentiableAt ℝ a x) (hh : DifferentiableAt ℝ h x) (v : Fin m → ℂ) :
    fderiv ℝ (fun y => a y • h y) x v = a x • fderiv ℝ h x v + fderiv ℝ a x v • h x := by
  have H : HasFDerivAt (fun y => a y • h y)
      (a x • fderiv ℝ h x + (fderiv ℝ a x).smulRight (h x)) x :=
    ha.hasFDerivAt.smul hh.hasFDerivAt
  rw [H.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    ContinuousLinearMap.smulRight_apply]
end Formalism.QuantumDeterminants.WirtingerDerivatives
