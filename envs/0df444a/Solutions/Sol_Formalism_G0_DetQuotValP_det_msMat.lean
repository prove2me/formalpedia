-- Prove2me | solution 1 for Formalism.G0.DetQuotValP.det_msMat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:25.915044+00:00
-- url     : https://prove2.me/submissions/c89be13c-df0b-4482-bde3-0f8a14f854ef

import Definitions.Def_Formalism_SubspaceCounting_DetQuotVal
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetVal
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetQuotVal
import Theorems.Thm_Formalism_G0_DetValP_prod_last


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0 Formalism.G0.DetQuotValP
open Formalism.G0 Formalism.G0.DetValP
variable {K ι : Type} [Field K] [DecidableEq ι]
namespace Formalism.G0.DetQuotValP
theorem _root_.solution {L : Type} [Field L] {r : ℕ} (hr : 1 ≤ r) (g : GL (Fin r) L) :
    (msMat g).det = Polynomial.X := by
  unfold msMat
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, prod_last hr]
  have h1 : (g.1.map Polynomial.C).det * ((g⁻¹ : GL (Fin r) L).1.map Polynomial.C).det = 1 := by
    rw [← Matrix.det_mul, ← Matrix.map_mul, Units.mul_inv]
    simp
  calc (g.1.map Polynomial.C).det * Polynomial.X * ((g⁻¹ : GL (Fin r) L).1.map Polynomial.C).det
      = Polynomial.X * ((g.1.map Polynomial.C).det *
          ((g⁻¹ : GL (Fin r) L).1.map Polynomial.C).det) := by ring
    _ = Polynomial.X := by rw [h1, mul_one]
end Formalism.G0.DetQuotValP
