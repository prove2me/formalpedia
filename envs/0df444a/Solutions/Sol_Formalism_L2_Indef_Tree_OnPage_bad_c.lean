-- Prove2me | solution 1 for Formalism.L2.Indef.Tree.OnPage.bad_c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:48:09.337066+00:00
-- url     : https://prove2.me/submissions/927dc76a-7472-419a-8bda-5517c8cf10b4

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
theorem _root_.solution (C m v w fSe T f b s L C2 : ℝ) (hC : 0 ≤ C) (hv0 : 0 ≤ v) (hs : 0 ≤ s) (hv1 : s * (2 + v) ≤ 11 * L)
    (hw0 : 0 ≤ w + fSe) (hw : w ≤ 2 * f * b) (hfS : fSe ≤ f * b) (hT : T ≤ b) (hf : 8 ≤ f) (hm : 44 ≤ m) (hb : 1 ≤ b)
    (hC2 : 66 * C + 4 ≤ C2) :
    s * (2 * (C * m * (2 + v) * (w + fSe)) + 2 * T + 2) ≤ C2 * (f * m * b * L) := by
  have hfb : 0 ≤ f * b := mul_nonneg (by linarith) (by linarith)
  have hm0 : 0 ≤ m := by linarith
  have hsv : 0 ≤ s * v := mul_nonneg hs hv0
  have hL : 0 ≤ L := by nlinarith
  have hs2 : 2 * s ≤ 11 * L := by nlinarith
  have hwS : w + fSe ≤ 3 * (f * b) := by linarith
  have hA : s * (2 + v) * (w + fSe) ≤ 11 * L * (3 * (f * b)) :=
    mul_le_mul hv1 hwS hw0 (by linarith)
  have hB : C * m * (s * (2 + v) * (w + fSe)) ≤ C * m * (11 * L * (3 * (f * b))) :=
    mul_le_mul_of_nonneg_left hA (mul_nonneg hC hm0)
  have hfm : 352 ≤ f * m := by nlinarith
  have hbL : 0 ≤ b * L := mul_nonneg (by linarith) hL
  have h1 : s * (2 * T + 2) ≤ s * (4 * b) := mul_le_mul_of_nonneg_left (by linarith) hs
  have h2 : 2 * s * b ≤ 11 * L * b := mul_le_mul_of_nonneg_right hs2 (by linarith)
  have h3 : 352 * (b * L) ≤ f * m * (b * L) := mul_le_mul_of_nonneg_right hfm hbL
  have hU : 0 ≤ f * m * b * L := by nlinarith
  have h4 : (66 * C + 4) * (f * m * b * L) ≤ C2 * (f * m * b * L) := mul_le_mul_of_nonneg_right hC2 hU
  nlinarith
end Formalism.L2.Indef.Tree.OnPage
