-- Prove2me | solution 1 for Formalism.CG.balanceG
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:31:18.151467+00:00
-- url     : https://prove2.me/submissions/e9f22768-a5fc-44ca-89bd-245cad775162

import Definitions.Def_Formalism_TranslateCocycles_Statement
import Definitions.Def_Formalism_TranslateCocycles_TranslateCocycleProofs_TranslateScale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.CG
open Finset
namespace Formalism.CG
theorem _root_.solution : BalanceG := by
  intro J T P D del hD hdel colL colLb aL aLb Dpi Dp Dm eta etab top k w e1 e2 Ecol CA rL rLb Etw
    h1 hA h4 h5
  have hD0 : D ≠ 0 := hD.ne'
  have hdel0 : del ≠ 0 := hdel.ne'
  have E1 : ∑ j ∈ J, ∑ τ ∈ P, (w j τ + e1 j τ + e2 j τ) =
      ∑ j ∈ J, ∑ τ ∈ P, (k * w j τ + e1 j τ) - ∑ j ∈ J, ∑ τ ∈ P, ((k - 1) * w j τ - e2 j τ) := by
    rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun τ _ => ?_; ring
  have S4 : ∑ j ∈ J, Dpi j ≤ (J.card : ℝ) * ∑ t ∈ T, top t + ∑ j ∈ J, ∑ τ ∈ P, (k * w j τ + e1 j τ) := by
    calc ∑ j ∈ J, Dpi j ≤ ∑ j ∈ J, (∑ t ∈ T, top t + ∑ τ ∈ P, (k * w j τ + e1 j τ)) :=
          Finset.sum_le_sum h4
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  have S5 : ∑ j ∈ J, ∑ τ ∈ P, ((k - 1) * w j τ - e2 j τ) ≤ ∑ j ∈ J, (Dp j + Dm j) :=
    Finset.sum_le_sum h5
  have Ea : ∑ j ∈ J, (aL j + aLb j) / D = (∑ j ∈ J, (aL j + aLb j)) / D := (Finset.sum_div ..).symm
  have Ee : ∑ j ∈ J, (eta j + etab j) / (2 * D) = (∑ j ∈ J, (eta j + etab j)) / (2 * D) :=
    (Finset.sum_div ..).symm
  have Er : ∑ j ∈ J, (-2 * (Dp j + Dm j) * D + eta j + etab j)
      = -2 * D * ∑ j ∈ J, (Dp j + Dm j) + ∑ j ∈ J, (eta j + etab j) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun j _ => ?_; ring
  rw [Er] at hA
  rw [E1, Ea, Ee]
  have key : (∑ j ∈ J, (aL j + aLb j)) / D / 2 ≤ (-2 * D * ∑ j ∈ J, (Dp j + Dm j)
      + ∑ j ∈ J, (eta j + etab j) + 2 * (J.card : ℝ) * (CA * D + (rL + rLb) / del) + Etw) / D / 2 := by
    gcongr
  have key2 : (-2 * D * ∑ j ∈ J, (Dp j + Dm j) + ∑ j ∈ J, (eta j + etab j)
      + 2 * (J.card : ℝ) * (CA * D + (rL + rLb) / del) + Etw) / D / 2
      = -∑ j ∈ J, (Dp j + Dm j) + (∑ j ∈ J, (eta j + etab j)) / (2 * D)
        + (J.card : ℝ) * (CA + (rL + rLb) / (del * D)) + Etw / (2 * D) := by
    field_simp
  linarith
end Formalism.CG
