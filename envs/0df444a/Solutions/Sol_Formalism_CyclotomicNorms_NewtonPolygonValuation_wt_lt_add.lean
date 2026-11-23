-- Prove2me | solution 1 for Formalism.CyclotomicNorms.NewtonPolygonValuation.wt_lt_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:39.199009+00:00
-- url     : https://prove2.me/submissions/ac3c7b9a-0a6e-484d-b2d4-45bb52fdf8f2

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
theorem _root_.solution {a : WithTop ℝ} {x y : ℝ} (h : ∀ r : ℝ, a = r → x < r + y) :
    (x : WithTop ℝ) < a + y := by
  induction a using WithTop.recTopCoe with
  | top => simp
  | coe r =>
    rw [← WithTop.coe_add]
    exact WithTop.coe_lt_coe.2 (h r rfl)
end Formalism.CyclotomicNorms.NewtonPolygonValuation
