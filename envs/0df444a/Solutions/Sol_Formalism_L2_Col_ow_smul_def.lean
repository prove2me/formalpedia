-- Prove2me | solution 1 for Formalism.L2.Col.ow_smul_def
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:11:14.98252+00:00
-- url     : https://prove2.me/submissions/7740b12e-189d-4c88-bf6c-eef9c30c0ceb

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
variable (w : HeightOneSpectrum (𝓞 K)) (V : Type) [AddCommGroup V] [Module K V]
variable {V}
namespace Formalism.L2.Col
theorem _root_.solution (r : Ow w) (x : V) : r • x = algebraMap (Ow w) K r • x := rfl
end Formalism.L2.Col
