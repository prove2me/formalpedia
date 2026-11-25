-- Prove2me | solution 1 for Formalism.L2.Indef.Tree.OnPage.leafPage_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:12:48.874534+00:00
-- url     : https://prove2.me/submissions/72665fbe-f35e-4fda-a742-161d2f927480

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ExampleSatisfiesConditionsAtFive
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ONPage
import Theorems.Thm_Formalism_L2_Indef_Tree_OnPage_one_le_b
import Theorems.Thm_Formalism_L2_Indef_Tree_OnPage_ne_of_mod_dvd

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
theorem _root_.solution (O : OnObj S P c) (hC : ConstC c) (hx : 3 ≤ O.x) (hN4 : HalfDegreeAtLeastFour O) (h12 : PrimeCongruenceConditions O)
    (h1246 : DegreeAtLeastFortyFour O) (h29 : DimensionExceedsDegreeByThree O) (h1 : LeafSZ1 O) (hSg : LeafSign O) (h75 : ConductorCongruentPrimePair O)
    (tVd : TieVd O) (tBp : TieBp O) (tNc : TieNc O) : LeafPage O := by
  obtain ⟨hq, hd, hq8, hd16⟩ := h12
  obtain ⟨hg1, hg2, -, -, hne, n, ⟨dq, dd', hsm⟩, hm1, hm2⟩ := h75
  have hx0 : 0 ≤ O.x := by linarith
  have hb : 1 ≤ O.b := one_le_b O hx0
  have hn4 : 4 ≤ nH O := hN4
  have hnp : 0 < nH O := by linarith
  have hf : 8 ≤ O.f := by have : nH O = O.f / 2 := rfl; linarith
  have hm : 44 ≤ O.m := h1246.1
  have hk : O.m + 3 ≤ O.k := h29
  have hbp : 0 ≤ O.bp := by
    rw [tBp]; unfold aa Xp
    exact div_nonneg (mul_nonneg hx0 (by linarith)) (Real.exp_pos _).le
  have hvd : 0 ≤ O.vd := tVd.1
  have hNc : 0 ≤ O.Nc := by
    rw [tNc]; unfold dl2
    have : 0 ≤ (O.T2 : ℝ) / nH O := div_nonneg (Nat.cast_nonneg _) hnp.le
    have : 0 ≤ O.x ^ (2 * O.eps) := Real.rpow_nonneg hx0 _
    have : 0 ≤ (O.T2 : ℝ) / nH O * O.k * O.b := by
      apply mul_nonneg (mul_nonneg (by assumption) (by linarith)) (by linarith)
    exact div_nonneg (mul_nonneg (by assumption) (by assumption)) hnp.le
  refine ⟨hC, by linarith, by linarith, hf, h1.1, hSg.1, hSg.2, hbp, hvd, hNc, hg1, hg2, hq, hd, hne, by omega,
    ne_of_mod_dvd hm1 dq hq.one_lt, ne_of_mod_dvd hm2 dq hq.one_lt, ne_of_mod_dvd hm1 dd' hd.one_lt,
    ne_of_mod_dvd hm2 dd' hd.one_lt, fun h => ne_of_mod_dvd hm1 (hsm _ h).2 (hsm _ h).1 rfl,
    fun h => ne_of_mod_dvd hm2 (hsm _ h).2 (hsm _ h).1 rfl, tVd.2.2.1, tVd.2.2.2, by linarith⟩
end Formalism.L2.Indef.Tree.OnPage
