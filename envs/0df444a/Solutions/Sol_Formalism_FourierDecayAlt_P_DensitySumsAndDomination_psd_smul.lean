-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DensitySumsAndDomination.psd_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:31:44.906281+00:00
-- url     : https://prove2.me/submissions/25bdb846-2af8-44c5-b16c-156362fe18b0

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DensitySumsAndDomination

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TC
open scoped ComplexInnerProductSpace ComplexOrder ComplexConjugate
noncomputable section
open Classical
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DensitySumsAndDomination
namespace Formalism.FourierDecayAlt.P.DensitySumsAndDomination
theorem _root_.solution {α : Type} {Y : Finset α} {k : α → α → ℂ} (c : ℝ) (hc : 0 ≤ c) (h : TB.PSDOn Y k) :
    TB.PSDOn Y (fun x y => (c : ℂ) * k x y) := by
  unfold TB.PSDOn at *
  first
    | (have e : (Matrix.of fun x y : Y => (c : ℂ) * k x y) = c • Matrix.of fun x y : Y => k x y := by
         ext x y
         simp [Complex.real_smul]
       rw [e]
       exact h.smul hc)
    | (have e : (Matrix.of fun x y : Y => (c : ℂ) * k x y) = (c : ℂ) • Matrix.of fun x y : Y => k x y := by
         ext x y
         simp
       rw [e]
       exact h.smul (Complex.zero_le_real.mpr hc))
end Formalism.FourierDecayAlt.P.DensitySumsAndDomination
