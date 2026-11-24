-- Prove2me | solution 1 for Formalism.G0.DetQuotValP.msMat_eval_zero_mul_eq_mul_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:36.498026+00:00
-- url     : https://prove2.me/submissions/3cb7d778-65b3-47c4-ad22-52c1411cb5e8

import Definitions.Def_Formalism_SubspaceCounting_DetQuotVal
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetVal
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetQuotVal

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
theorem _root_.solution {L : Type} [Field L] {r : ℕ} (g : GL (Fin r) L) :
    (msMat g).map (Polynomial.evalRingHom (0 : L)) * g.1 =
      g.1 * Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then (0 : L) else 1) := by
  unfold msMat
  rw [Matrix.map_mul, Matrix.map_mul]
  have e1 : (g.1.map Polynomial.C).map (Polynomial.evalRingHom (0 : L)) = g.1 := by
    ext i j; simp
  have e2 : ((g⁻¹ : GL (Fin r) L).1.map Polynomial.C).map (Polynomial.evalRingHom (0 : L)) =
      (g⁻¹ : GL (Fin r) L).1 := by
    ext i j; simp
  have e3 : (Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then Polynomial.X else 1)).map
      (Polynomial.evalRingHom (0 : L)) =
      Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then (0 : L) else 1) := by
    ext i j
    by_cases h : i = j
    · subst h; by_cases h' : i.val + 1 = r <;> simp [h']
    · simp [h]
  rw [e1, e2, e3, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
end Formalism.G0.DetQuotValP
