-- Prove2me | solution 1 for Formalism.L2.Col.lenUW_mul_eW
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:38.56448+00:00
-- url     : https://prove2.me/submissions/b8416ac0-db35-4cef-a0f3-39b7eadc8afa

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_LocalToGlobal_Columns_AlgebraMapMemMaximalIdealPowIff
import Theorems.Thm_Formalism_L2_Col_eW_ne_zero_rat

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
omit [IsScalarTower (𝓞 K) K V]
namespace Formalism.L2.Col
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V) :
    lenUW w A B * (eW w : ℚ) = ((lenW w A B).toNat : ℚ) :=
  div_mul_cancel₀ _ (eW_ne_zero_rat w)
end Formalism.L2.Col
