-- Prove2me | solution 1 for Formalism.L2.Pj.finitePlace_eq_zpow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:03:47.555984+00:00
-- url     : https://prove2.me/submissions/43884303-8d3d-4e5e-9f17-020ce0a84ff1

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField
open scoped WithZero
open Formalism Formalism.L2 Formalism.L2.Pj
attribute [instance] CDVR.cr CDVR.dom CDVR.dvr CDVR.cpl CDVR.ch0
variable {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))
namespace Formalism.L2.Pj
theorem _root_.solution {a : K} (ha : a ≠ 0) :
    FinitePlace.mk la a = (Ideal.absNorm la.asIdeal : ℝ) ^ (-(vLa la a)) := by
  rw [FinitePlace.mk_apply, FinitePlace.norm_embedding',
    WithZeroMulInt.toNNReal_neg_apply _ ((la.valuation K).ne_zero_iff.2 ha)]
  simp [vLa, WithZero.toAdd_unzero_eq_log]
end Formalism.L2.Pj
