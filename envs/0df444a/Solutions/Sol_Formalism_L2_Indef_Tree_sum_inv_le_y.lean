-- Prove2me | solution 1 for Formalism.L2.Indef.Tree.sum_inv_le_y
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:08:31.864562+00:00
-- url     : https://prove2.me/submissions/95b99264-f547-460b-80c2-0613ff6e8171

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ExampleSatisfiesConditionsAtFive
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_CharIdem
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_IndexUBound
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_MirabIndex
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IsMackeyPiUpperUnipotentProdCharacter
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_RamBasic
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_UnipVal
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ONLeaves

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain CategoryTheory
open Formalism Formalism.L2 Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {c : OnConst}
variable {ι : Type} [Fintype ι] [DecidableEq ι] {kf : ι → Type} [∀ v, Field (kf v)] [∀ v, Fintype (kf v)] {n : ℕ}
variable {Pm : ∀ v, Subgroup (GL (Fin (n + 1)) (kf v))} {Uv : ∀ v, Subgroup (Pm v)}
namespace Formalism.L2.Indef.Tree
theorem _root_.solution {P : Type} [Group P] [Finite P] (O : OnObj S P c) (fN : ℕ) (hSq : LeafLevelSq O kf fN)
    (hf : O.f = (fN : ℝ)) (hY : LeafYBound O) :
    ∑ v, 1 / ((Fintype.card (kf v) : ℝ) - 1) ≤ O.y := by
  classical
  obtain ⟨hp1, hp2, h12, hor, hc1, hc2⟩ := hSq
  have hY2 : (2 : ℝ) ≤ ((min O.g1 O.g2 : ℕ) : ℝ) := by
    have : 2 ≤ min O.g1 O.g2 := le_min hp1.two_le hp2.two_le
    exact_mod_cast this
  have hle : ∀ v, 1 / ((Fintype.card (kf v) : ℝ) - 1) ≤ 1 / (((min O.g1 O.g2 : ℕ) : ℝ) - 1) := by
    intro v
    have hYv : ((min O.g1 O.g2 : ℕ) : ℝ) ≤ (Fintype.card (kf v) : ℝ) := by
      have : min O.g1 O.g2 ≤ Fintype.card (kf v) := by
        rcases hor v with h | h <;> rw [h]
        · exact min_le_left _ _
        · exact min_le_right _ _
      exact_mod_cast this
    exact one_div_le_one_div_of_le (by linarith) (by linarith)
  have hcard : (Finset.univ : Finset ι).card = 2 * fN := by
    have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset ι))
      (fun v => Fintype.card (kf v) = O.g1)
    have hfilt : (Finset.univ.filter fun v => ¬ Fintype.card (kf v) = O.g1) =
        (Finset.univ.filter fun v => Fintype.card (kf v) = O.g2) := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h; exact (hor v).resolve_left h
      · intro h h'; exact h12 (h'.symm.trans h)
    rw [hfilt, hc1, hc2] at hsplit
    omega
  calc ∑ v, 1 / ((Fintype.card (kf v) : ℝ) - 1) ≤ ∑ _v : ι, 1 / (((min O.g1 O.g2 : ℕ) : ℝ) - 1) :=
        Finset.sum_le_sum fun v _ => hle v
    _ = 2 * O.f / (((min O.g1 O.g2 : ℕ) : ℝ) - 1) := by
      rw [Finset.sum_const, nsmul_eq_mul, hcard, hf]
      push_cast
      ring
    _ ≤ O.y := hY
end Formalism.L2.Indef.Tree
