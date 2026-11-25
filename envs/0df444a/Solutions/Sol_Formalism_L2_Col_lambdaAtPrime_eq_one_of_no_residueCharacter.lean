-- Prove2me | solution 1 for Formalism.L2.Col.lambdaAtPrime_eq_one_of_no_residueCharacter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:07:46.940166+00:00
-- url     : https://prove2.me/submissions/416a8ed0-de2d-4828-82c6-7091553e58c8

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
theorem _root_.solution (ξ : Formalism.L2.DIV.Chr F E L) (P : HeightOneSpectrum (𝓞 E)) (n a b : ℕ)
    (hno : ¬ ∃ χ, Formalism.L2.DIV.IsResChar ξ P χ) : lamQP ξ P n a b = 1 := by
  unfold lamQP
  have h1 : Formalism.L2.DIV.resChar ξ P = 1 := by
    unfold Formalism.L2.DIV.resChar
    rw [dif_neg hno]
  rw [h1]
  unfold lamQ detChar
  simp
end Formalism.L2.Col
