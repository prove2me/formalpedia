-- Prove2me | solution 1 for Formalism.MainNotions.MassRatioZetaBound.absNorm_nat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:45:00.496858+00:00
-- url     : https://prove2.me/submissions/508b36a2-3dfa-4e33-9074-04bd7d18fc8f

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_MassRatioBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.MassRatioZetaBound
open NumberField
variable {K : Type*} [Field K] [NumberField K]
namespace Formalism.MainNotions.MassRatioZetaBound
theorem _root_.solution (l : ℕ) : Ideal.absNorm (Ideal.span {(l : 𝓞 K)}) = l ^ Module.finrank ℚ K := by
  rw [Ideal.absNorm_span_singleton]
  have : ((l : 𝓞 K)) = algebraMap ℤ (𝓞 K) (l : ℤ) := by simp
  rw [this, Algebra.norm_algebraMap, RingOfIntegers.rank]
  simp
end Formalism.MainNotions.MassRatioZetaBound
