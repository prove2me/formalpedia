-- Prove2me | solution 1 for Formalism.ofReal_ne_ofReal_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:16:11.553264+00:00
-- url     : https://prove2.me/submissions/e7186793-1236-429d-a34e-77266a41239f

import Definitions.Def_Formalism_ZetaNonvanishing_RiemannZetaOneNeZeroOfRealMemIoo
import Definitions.Def_Formalism_ZetaNonvanishing_OfRealNeOfRealOfLt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Formalism
variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ι → ℕ} [∀ i, NeZero (N i)]
  (χ : (i : ι) → DirichletCharacter ℂ (N i)) (w : ι → ℝ)
namespace Formalism
theorem _root_.solution {a b : ℝ} (h : a < b) : (b : ℂ) ≠ (a : ℂ) := by
  intro h'
  have := congrArg Complex.re h'
  simp at this
  linarith
end Formalism
