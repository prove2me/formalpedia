-- Prove2me | solution 1 for Formalism.L2.Col.lambdaAtPrime_eq_of_residueCharacter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:18:37.748129+00:00
-- url     : https://prove2.me/submissions/4b712af0-ec3e-447a-a385-5506242c410b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DimensionMassJointBound
import Definitions.Def_Formalism_LocalToGlobal_Columns_LevGCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset IsDedekindDomain NumberField
open Formalism Formalism.L2 Formalism.L2.Col
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]
namespace Formalism.L2.Col
theorem _root_.solution (ξ : Formalism.L2.DIV.Chr F E L) (P : HeightOneSpectrum (𝓞 E)) (n a b : ℕ) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Lˣ)
    (hχ : Formalism.L2.DIV.IsResChar ξ P χ) (huniq : ∀ χ', Formalism.L2.DIV.IsResChar ξ P χ' → χ' = χ) :
    lamQP ξ P n a b = lamQ χ n a b := by
  unfold lamQP
  congr 1
  unfold Formalism.L2.DIV.resChar
  rw [dif_pos ⟨χ, hχ⟩]
  exact huniq _ (Exists.choose_spec _)
end Formalism.L2.Col
