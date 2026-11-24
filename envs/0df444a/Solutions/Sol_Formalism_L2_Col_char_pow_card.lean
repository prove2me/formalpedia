-- Prove2me | solution 1 for Formalism.L2.Col.char_pow_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:54:12.766864+00:00
-- url     : https://prove2.me/submissions/d324597b-7e64-4770-8cd6-91200d2ce4e5

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
namespace Formalism.L2.Col
theorem _root_.solution {G K : Type} [Group G] [Finite G] [Field K] (lam : G →* Kˣ) (x : G) : lam x ^ Nat.card G = 1 := by
  rw [← map_pow, pow_card_eq_one', map_one]
end Formalism.L2.Col
