-- Prove2me | solution 1 for Formalism.L2.Col.exists_isUnifW
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:09:38.396799+00:00
-- url     : https://prove2.me/submissions/dbb2a421-87fc-4cbf-8674-1a679e147a74

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_LocalToGlobal_Columns_AlgebraMapMemMaximalIdealPowIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Col
variable {K : Type} [Field K] [NumberField K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.L2.Col
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) : ∃ ϖ : 𝓞 K, IsUnifW w ϖ := by
  obtain ⟨x, hx, hx'⟩ := Ideal.exists_mem_pow_notMem_pow_succ w.asIdeal w.ne_bot w.isPrime.ne_top 1
  exact ⟨x, by simpa using hx, hx'⟩
end Formalism.L2.Col
