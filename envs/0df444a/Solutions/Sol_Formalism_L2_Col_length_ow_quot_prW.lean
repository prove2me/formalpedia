-- Prove2me | solution 1 for Formalism.L2.Col.length_ow_quot_prW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:21:18.887124+00:00
-- url     : https://prove2.me/submissions/66348198-4a0e-4613-80df-6ca4e9c77d12

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_LocalToGlobal_Columns_AlgebraMapMemMaximalIdealPowIff
import Theorems.Thm_Formalism_L2_Col_span_prW_ow

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
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) :
    Module.length (Ow w) (Ow w ⧸ Ideal.span {((prW w : ℕ) : Ow w)}) = eW w := by
  rw [span_prW_ow, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]
end Formalism.L2.Col
