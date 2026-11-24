-- Prove2me | solution 1 for Formalism.L2.Col.lenW_toNat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:31:40.934606+00:00
-- url     : https://prove2.me/submissions/2a214d26-dfaf-4a40-b457-b5a84f19e312

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_LocalToGlobal_Columns_AlgebraMapMemMaximalIdealPowIff
import Theorems.Thm_Formalism_L2_Col_lenW_eq_length

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
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V) :
    (lenW w A B).toNat = Formalism.HermitianLatticesTheory.locLen w.asIdeal A B := by
  rw [lenW_eq_length]; rfl
end Formalism.L2.Col
