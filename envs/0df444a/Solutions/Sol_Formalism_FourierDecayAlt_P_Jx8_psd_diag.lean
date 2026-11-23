-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx8.psd_diag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:30:19.024297+00:00
-- url     : https://prove2.me/submissions/5211d7ed-dd96-4534-9092-dc9aa5dba4f2

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_quad1
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_psdOn_iff_isPSD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexOrder ComplexConjugate Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx8
variable {α : Type}
namespace Formalism.FourierDecayAlt.P.Jx8
theorem _root_.solution {F : Finset α} {k : α → α → ℂ} (hk : TB.PSDOn F k) {x : α} (hx : x ∈ F) :
    (k x x).im = 0 ∧ 0 ≤ (k x x).re := by
  classical
  have h2 := (psdOn_iff_isPSD F k).1 hk (fun u => if u = x then 1 else 0)
  have h1 := quad1 F k x hx
  beta_reduce at h2
  rw [h1] at h2
  exact h2
end Formalism.FourierDecayAlt.P.Jx8
