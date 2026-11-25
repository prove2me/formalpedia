-- Prove2me | solution 1 for Formalism.L2.Col.char_norm_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:10:01.596466+00:00
-- url     : https://prove2.me/submissions/71e24735-1917-460b-956b-aebf18c68fb4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DimensionMassJointBound
import Definitions.Def_Formalism_LocalToGlobal_Columns_LevGCount
import Theorems.Thm_Formalism_L2_Col_char_pow_card

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
theorem _root_.solution {G K : Type} [Group G] [Finite G] [Field K] (lam : G →* Kˣ) (x : G) (φ : K →+* ℂ) :
    ‖φ (lam x : K)‖ = 1 := by
  have h1 : (φ (lam x : K)) ^ Nat.card G = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, char_pow_card, Units.val_one, map_one]
  have hpos : 0 < Nat.card G := Nat.card_pos
  have h2 : ‖φ (lam x : K)‖ ^ Nat.card G = 1 := by rw [← norm_pow, h1, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hpos.ne').mp h2
end Formalism.L2.Col
