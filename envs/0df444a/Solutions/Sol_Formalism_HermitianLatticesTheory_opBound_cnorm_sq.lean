-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.opBound_cnorm_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:54:00.744642+00:00
-- url     : https://prove2.me/submissions/e8a5d87e-14bf-484f-a977-b0a3e32b8e31

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMaj
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_OpBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {K V ι : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (u : ι → ℂ) : cnorm u ^ 2 = ∑ i, ‖u i‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)
end Formalism.HermitianLatticesTheory
