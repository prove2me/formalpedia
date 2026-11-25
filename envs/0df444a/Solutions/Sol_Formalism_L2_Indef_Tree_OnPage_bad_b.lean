-- Prove2me | solution 1 for Formalism.L2.Indef.Tree.OnPage.bad_b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:36:07.860254+00:00
-- url     : https://prove2.me/submissions/60c4b26e-dbad-4e18-9e49-aedf53521043

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ExampleSatisfiesConditionsAtFive
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ONPage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.L2.Indef.Tree.OnPage
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {c : OnConst}
namespace Formalism.L2.Indef.Tree.OnPage
theorem _root_.solution (w fSe T fkb lq f m b C1 : ℝ) (hw : w ≤ 2 * f * b) (hfS : fSe ≤ f * b) (hT : T ≤ b)
    (hfk : fkb ≤ f * b) (hlq0 : 0 ≤ lq) (hlq : lq ≤ m) (hf : 8 ≤ f) (hm : 44 ≤ m) (hb : 1 ≤ b)
    (hC1 : 14 ≤ C1) : (2 * (w + fSe + T + 1) + 4 * fkb) * lq ≤ C1 * (f * m * b) := by
  have hfb : 0 ≤ f * b := mul_nonneg (by linarith) (by linarith)
  have hB : 2 * (w + fSe + T + 1) + 4 * fkb ≤ 10 * (f * b) + 2 * b + 2 := by linarith
  have hB0 : 0 ≤ 10 * (f * b) + 2 * b + 2 := by linarith
  have hbm0 : 0 ≤ b * m := mul_nonneg (by linarith) (by linarith)
  have h1 : b * m ≤ f * m * b := by
    calc b * m = 1 * (b * m) := by ring
      _ ≤ f * (b * m) := mul_le_mul_of_nonneg_right (by linarith) hbm0
      _ = f * m * b := by ring
  have h2 : m ≤ b * m := by
    calc m = 1 * m := by ring
      _ ≤ b * m := mul_le_mul_of_nonneg_right hb (by linarith)
  have hfmb : 0 ≤ f * m * b := by linarith
  calc (2 * (w + fSe + T + 1) + 4 * fkb) * lq ≤ (10 * (f * b) + 2 * b + 2) * lq :=
        mul_le_mul_of_nonneg_right hB hlq0
    _ ≤ (10 * (f * b) + 2 * b + 2) * m := mul_le_mul_of_nonneg_left hlq hB0
    _ = 10 * (f * m * b) + 2 * (b * m) + 2 * m := by ring
    _ ≤ 14 * (f * m * b) := by linarith
    _ ≤ C1 * (f * m * b) := mul_le_mul_of_nonneg_right hC1 hfmb
end Formalism.L2.Indef.Tree.OnPage
