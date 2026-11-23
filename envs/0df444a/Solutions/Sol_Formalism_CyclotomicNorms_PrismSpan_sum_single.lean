-- Prove2me | solution 1 for Formalism.CyclotomicNorms.PrismSpan.sum_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:51:21.740662+00:00
-- url     : https://prove2.me/submissions/358f6038-f4ba-457d-afed-dd8cd722acca

import Definitions.Def_Formalism_CyclotomicNorms_StatementA
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_SpanQuadraticOfImage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module
open Formalism Formalism.CyclotomicNorms
open Formalism.CyclotomicNorms.PrismSpan
namespace Formalism.CyclotomicNorms.PrismSpan
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type}
    [∀ i, AddCommMonoid (X i)] (v : ∀ i, X i) : ∑ i, Pi.single i (v i) = v := by
  ext; simp
end Formalism.CyclotomicNorms.PrismSpan
