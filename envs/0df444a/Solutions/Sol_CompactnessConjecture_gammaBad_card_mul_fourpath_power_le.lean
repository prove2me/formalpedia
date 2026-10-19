-- Prove2me | solution 1 for CompactnessConjecture.gammaBad_card_mul_fourpath_power_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.811989+00:00
-- url     : https://prove2.me/submissions/c3480444-9778-4402-95fe-5f73c54815e6

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_orderedThetaTripleCount_mul_degree_le
import Theorems.Thm_CompactnessConjecture_gammaBad_card_mul_heavyTripleLower_le_two_orderedTheta

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace CompactnessConjecture
theorem _root_.solution
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (d : ℕ) (hdegree : ∀ v : Fin n, d ≤ host.degree v)
    (hthreshold : (3 : ℝ) ≤
      fourPathHeavyThreshold n (d * (d - 1) ^ 3)) :
    (gammaBadVertices host).card *
      (d * (d - 1) ^ 3) ^ 3 * d ≤ 432 * n ^ 5 := by
  have hn : 0 < n := by
    by_contra hzero
    have hnzero : n = 0 := Nat.eq_zero_of_not_pos hzero
    subst n
    norm_num [fourPathHeavyThreshold] at hthreshold
  have hnReal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  let p : ℕ := d * (d - 1) ^ 3
  let bad : ℕ := (gammaBadVertices host).card
  let theta : ℕ := orderedThetaTripleCount host
  have hmass :
      (bad : ℝ) *
        (fourPathHeavyThreshold n p ^ 2 *
          (p : ℝ) / 54) ≤ 2 * (theta : ℝ) := by
    exact gammaBad_card_mul_heavyTripleLower_le_two_orderedTheta
      host hfree hbip d hdegree hthreshold
  have hnormalized :
      ((bad : ℝ) * (p : ℝ) ^ 3) /
          (216 * (n : ℝ) ^ 2) ≤ 2 * (theta : ℝ) := by
    calc
      ((bad : ℝ) * (p : ℝ) ^ 3) /
          (216 * (n : ℝ) ^ 2) =
        (bad : ℝ) *
          (fourPathHeavyThreshold n p ^ 2 * (p : ℝ) / 54) := by
            unfold fourPathHeavyThreshold
            field_simp [ne_of_gt hnReal]
            ring
      _ ≤ 2 * (theta : ℝ) := hmass
  have hden : 0 < (216 : ℝ) * (n : ℝ) ^ 2 := by
    positivity
  have hclear := (div_le_iff₀ hden).mp hnormalized
  have hbadpoly :
      (bad : ℝ) * (p : ℝ) ^ 3 ≤
        432 * (theta : ℝ) * (n : ℝ) ^ 2 := by
    nlinarith
  have htheta :
      (theta : ℝ) * (d : ℝ) ≤ (n : ℝ) ^ 3 := by
    exact_mod_cast
      (orderedThetaTripleCount_mul_degree_le
        host hfree hbip d hdegree)
  have hfinal :
      (bad : ℝ) * (p : ℝ) ^ 3 * (d : ℝ) ≤
        432 * (n : ℝ) ^ 5 := by
    calc
      (bad : ℝ) * (p : ℝ) ^ 3 * (d : ℝ) ≤
          (432 * (theta : ℝ) * (n : ℝ) ^ 2) * (d : ℝ) :=
        mul_le_mul_of_nonneg_right hbadpoly (Nat.cast_nonneg d)
      _ = 432 * ((theta : ℝ) * (d : ℝ)) * (n : ℝ) ^ 2 := by ring
      _ ≤ 432 * (n : ℝ) ^ 3 * (n : ℝ) ^ 2 := by
        gcongr
      _ = 432 * (n : ℝ) ^ 5 := by ring
  exact_mod_cast hfinal
end CompactnessConjecture
