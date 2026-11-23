-- Prove2me | solution 1 for Formalism.CyclotomicNorms.NewtonPolygonValuation.val_term
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:38.928959+00:00
-- url     : https://prove2.me/submissions/3cff7bc3-639d-41b5-adb3-d75a3c2fc6d6

import Definitions.Def_Formalism_CyclotomicNorms_StatementA
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_Newton

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.CyclotomicNorms
open Formalism.CyclotomicNorms.NewtonPolygonValuation
variable {L : Type} [Field L] (v : AddValuation L (WithTop ℝ))
namespace Formalism.CyclotomicNorms.NewtonPolygonValuation
theorem _root_.solution {x : L} {s : ℝ} (hx : v x = wt s) (a : L) (i : ℕ) :
    v (a * x ^ i) = v a + wt (i * s) := by
  rw [AddValuation.map_mul, AddValuation.map_pow, hx, ← WithTop.coe_nsmul, nsmul_eq_mul]
end Formalism.CyclotomicNorms.NewtonPolygonValuation
