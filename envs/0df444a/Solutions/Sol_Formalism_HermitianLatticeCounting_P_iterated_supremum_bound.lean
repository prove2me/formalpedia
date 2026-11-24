-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.iterated_supremum_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:37.187737+00:00
-- url     : https://prove2.me/submissions/4a81a8a7-4203-4b81-a541-ccdd55e2de41

import Definitions.Def_Formalism_FlagUnipotentLattices_HalfDifferenceL1Bound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : IterSup := by
  intro a θ Θ P₀ hθ ha hstep
  induction P₀ with
  | zero => simp
  | succ P ih =>
    have h1 := ih (fun Q hQ => hθ Q (by omega)) (fun Q hQ => hstep Q (by omega))
    have h2 := hstep P (by omega)
    have h3 := hθ P (by omega)
    have hΘ : 0 ≤ Θ := h3.1.trans h3.2
    calc a 0 ≤ Θ ^ P * a P := h1
      _ ≤ Θ ^ P * (Θ * a (P + 1)) := by
          gcongr
          exact h2.trans (mul_le_mul_of_nonneg_right h3.2 (ha _))
      _ = _ := by ring
end Formalism.HermitianLatticeCounting.P
