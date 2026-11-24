-- Prove2me | solution 1 for Formalism.L2.Col.length_ow_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:54:19.342016+00:00
-- url     : https://prove2.me/submissions/cf6513d8-4244-4b1c-9db3-344a1e95e6bd

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
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) : Module.length (Ow w) (Ow w) = ⊤ := by
  rw [ENat.eq_top_iff_forall_ge]
  intro n
  rw [← IsDiscreteValuationRing.length_quotient_pow_maximalIdeal (R := Ow w) n]
  exact Module.length_le_of_surjective (Submodule.mkQ _) (Submodule.mkQ_surjective _)
end Formalism.L2.Col
