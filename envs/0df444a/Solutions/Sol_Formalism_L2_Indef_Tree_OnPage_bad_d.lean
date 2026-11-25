-- Prove2me | solution 1 for Formalism.L2.Indef.Tree.OnPage.bad_d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:22:29.476489+00:00
-- url     : https://prove2.me/submissions/af10fb42-ff6b-4e2b-8ddf-6f0f9fe4faee

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ExampleSatisfiesConditionsAtFive
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ONPage
import Theorems.Thm_P2M_Formalism_L2_Indef_Tree_OnPage_le_of_sq_le_sq__77aaafc898aa

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
theorem _root_.solution (T f r L b lg : ℝ) (hT0 : 0 ≤ T) (hT2 : T ^ 2 ≤ b) (hf : 8 ≤ f) (hr : 9 ≤ r) (hL : 10 ≤ L)
    (hZ : (f * r * L) ^ 12 ≤ b) (hlg0 : 0 ≤ lg) (hlg1 : lg ≤ 18 * L) : (4 * T + 4 * f * r ^ 2) * lg ≤ 4 * b := by
  have hb0 : 0 ≤ b := le_trans (sq_nonneg T) hT2
  have hfr : 1 ≤ f * r := by nlinarith
  have hL0 : 0 ≤ L := by linarith
  have hLZ : L ≤ f * r * L := by
    calc L = 1 * L := by ring
      _ ≤ f * r * L := mul_le_mul_of_nonneg_right hfr hL0
  have hL12 : L ^ 12 ≤ b := le_trans (pow_le_pow_left₀ hL0 hLZ 12) hZ
  have hL2 : 1296 * L ^ 2 ≤ b := by
    have h10 : (10 : ℝ) ^ 10 ≤ L ^ 10 := pow_le_pow_left₀ (by norm_num) hL 10
    have e : L ^ 12 = L ^ 10 * L ^ 2 := by ring
    have hL20 : 0 ≤ L ^ 2 := sq_nonneg _
    have h1296 : (1296 : ℝ) ≤ L ^ 10 := le_trans (by norm_num) h10
    have : 1296 * L ^ 2 ≤ L ^ 10 * L ^ 2 := mul_le_mul_of_nonneg_right h1296 hL20
    linarith
  have hTL : 36 * (T * L) ≤ b := by
    have hsq : (36 * (T * L)) ^ 2 ≤ b ^ 2 := by
      have e : (36 * (T * L)) ^ 2 = T ^ 2 * (1296 * L ^ 2) := by ring
      rw [e, sq b]
      exact mul_le_mul hT2 hL2 (by positivity) hb0
    exact le_of_sq_le_sq' _ _ (by positivity) hb0 hsq
  have hZ0 : 720 ≤ f * r * L := by
    have h72 : 72 ≤ f * r := by nlinarith
    nlinarith
  have hZsq : f * r ^ 2 * L ≤ (f * r * L) ^ 2 := by
    have e : (f * r * L) ^ 2 = (f * r ^ 2 * L) * (f * L) := by ring
    have h1' : 1 ≤ f * L := by nlinarith
    have h0' : 0 ≤ f * r ^ 2 * L := mul_nonneg (mul_nonneg (by linarith) (sq_nonneg r)) hL0
    rw [e]
    calc f * r ^ 2 * L = (f * r ^ 2 * L) * 1 := by ring
      _ ≤ (f * r ^ 2 * L) * (f * L) := mul_le_mul_of_nonneg_left h1' h0'
  have h36 : 36 * (f * r * L) ^ 2 ≤ (f * r * L) ^ 12 := by
    have h10 : (720 : ℝ) ^ 10 ≤ (f * r * L) ^ 10 := pow_le_pow_left₀ (by norm_num) hZ0 10
    have h36' : (36 : ℝ) ≤ (f * r * L) ^ 10 := le_trans (by norm_num) h10
    have e : (f * r * L) ^ 12 = (f * r * L) ^ 10 * (f * r * L) ^ 2 := by ring
    have hz0 : 0 ≤ (f * r * L) ^ 2 := sq_nonneg _
    rw [e]
    exact mul_le_mul_of_nonneg_right h36' hz0
  have hfr2 : 36 * (f * r ^ 2 * L) ≤ b := by linarith
  have hfr20 : 0 ≤ f * r ^ 2 := mul_nonneg (by linarith) (sq_nonneg r)
  calc (4 * T + 4 * f * r ^ 2) * lg = 4 * T * lg + 4 * (f * r ^ 2) * lg := by ring
    _ ≤ 4 * T * (18 * L) + 4 * (f * r ^ 2) * (18 * L) := by
        have a1 : 4 * T * lg ≤ 4 * T * (18 * L) := mul_le_mul_of_nonneg_left hlg1 (by linarith)
        have a2 : 4 * (f * r ^ 2) * lg ≤ 4 * (f * r ^ 2) * (18 * L) :=
          mul_le_mul_of_nonneg_left hlg1 (by linarith)
        linarith
    _ = 2 * (36 * (T * L)) + 2 * (36 * (f * r ^ 2 * L)) := by ring
    _ ≤ 4 * b := by linarith
end Formalism.L2.Indef.Tree.OnPage
