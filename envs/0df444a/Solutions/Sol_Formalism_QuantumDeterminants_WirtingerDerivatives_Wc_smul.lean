-- Prove2me | solution 1 for Formalism.QuantumDeterminants.WirtingerDerivatives.Wc_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:00.993926+00:00
-- url     : https://prove2.me/submissions/2bd39433-075d-4d4f-b022-8a4a45ab747c

import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_WRWeyl
import Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_Wc_apply
import Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_fderiv_smul_apply

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
    (ha : DifferentiableAt ℝ a x) (hh : DifferentiableAt ℝ h x) (u w : Fin m → ℂ) (s : ℂ) :
    Wc u w s (fderiv ℝ (fun y => a y • h y) x) =
      Wc u w s (fderiv ℝ a x) • h x + a x • Wc u w s (fderiv ℝ h x) := by
  rw [Wc_apply, Wc_apply, Wc_apply, fderiv_smul_apply ha hh, fderiv_smul_apply ha hh]
  simp only [smul_eq_mul]
  module
end Formalism.QuantumDeterminants.WirtingerDerivatives
