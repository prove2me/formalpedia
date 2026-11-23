-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx6.sum_nonneg_of_psd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:15.216864+00:00
-- url     : https://prove2.me/submissions/9d43d38c-abaa-4d4d-a8b6-35b9ee31cbb3

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionGivesUniformBoundsForm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx6_quadM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate ComplexOrder Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx6
namespace Formalism.FourierDecayAlt.P.Jx6
theorem _root_.solution {α : Type} {F : Finset α} {k : α → α → ℂ} (hk : TB.PSDOn F k) :
    0 ≤ (∑ x ∈ F, ∑ y ∈ F, k x y).re := by
  unfold TB.PSDOn at hk
  rw [Matrix.posSemidef_iff_dotProduct_mulVec] at hk
  have h := hk.2 (fun x : F => (fun _ : α => (1 : ℂ)) x)
  rw [quadM F k (fun _ => 1)] at h
  have h2 := (Complex.le_def.1 h).1
  simpa using h2
end Formalism.FourierDecayAlt.P.Jx6
