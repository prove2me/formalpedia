-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.oneRowBasis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:28:02.554019+00:00
-- url     : https://prove2.me/submissions/ae554c8b-da8b-43b7-8685-7854eb7d9ea1

import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffQuadSer
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_MfactEqProdUniv
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneRow
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FirstRowMinorDegreeLeOne
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_IntegralOperatorsOnJets
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_GaussB
import Definitions.Def_Formalism_GaussJetBounds_FinalB
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qi22_homW_prod__0e07eaea3260
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk29_wtGe_prod__77285e911b46


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open Formalism Formalism.DworkPowerSeriesWeights
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution : OneRowBasis.{u} := by
  unfold OneRowBasis
  intro K _ _ N0 h0 x1 hx hx1
  obtain ⟨a0, ha0⟩ := hx1
  set z : Fin N0 := ⟨0, h0⟩ with hz
  have hu0 : x1 a0 ≠ 0 := by
    intro h
    rw [h, norm_zero] at ha0
    exact zero_ne_one ha0
  have huinv : ‖(x1 a0)⁻¹‖ = 1 := by rw [norm_inv, ha0, inv_one]
  let σ : Equiv.Perm (Fin N0) := Equiv.swap z a0
  have hσz : σ z = a0 := Equiv.swap_apply_left z a0
  let d : Fin N0 → K := fun a => if a = z then (x1 a0)⁻¹ else 1
  let e : Fin N0 → K := fun a => if a = z then 0 else -(x1 (σ a) * (x1 a0)⁻¹)
  let g : Matrix (Fin N0) (Fin N0) K :=
    fun a b => (if a = b then d a else 0) + (if z = b then e a else 0)
  have hd : ∀ a, ‖d a‖ ≤ 1 := by
    intro a
    show ‖(if a = z then (x1 a0)⁻¹ else 1)‖ ≤ 1
    split_ifs
    · exact huinv.le
    · simp
  have he : ∀ a, ‖e a‖ ≤ 1 := by
    intro a
    show ‖(if a = z then 0 else -(x1 (σ a) * (x1 a0)⁻¹))‖ ≤ 1
    split_ifs
    · simp
    · rw [norm_neg, norm_mul, huinv, mul_one]
      exact hx _
  have hg : ∀ a b, ‖g a b‖ ≤ 1 := by
    intro a b
    show ‖(if a = b then d a else 0) + (if z = b then e a else 0)‖ ≤ 1
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · split_ifs
      · exact hd a
      · simp
    · split_ifs
      · exact he a
      · simp
  have htri : g.BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hij' : i < j := OrderDual.toDual_lt_toDual.mp hij
    have h2 : ¬ z = j := by
      intro h
      have h3 : (z : ℕ) = (j : ℕ) := congrArg Fin.val h
      have h4 : (z : ℕ) = 0 := by rw [hz]
      have h5 : (i : ℕ) < (j : ℕ) := hij'
      omega
    show (if i = j then d i else 0) + (if z = j then e i else 0) = 0
    rw [if_neg (ne_of_lt hij'), if_neg h2, add_zero]
  have hdet : ‖g.det‖ = 1 := by
    rw [Matrix.det_of_lowerTriangular g htri, norm_prod]
    refine Finset.prod_eq_one (fun i _ => ?_)
    show ‖(if i = i then d i else 0) + (if z = i then e i else 0)‖ = 1
    rw [if_pos (rfl : i = i)]
    by_cases hi : z = i
    · subst hi
      show ‖(if z = z then (x1 a0)⁻¹ else 1) +
          (if z = z then 0 else -(x1 (σ z) * (x1 a0)⁻¹))‖ = 1
      rw [if_pos (rfl : z = z), if_pos (rfl : z = z), add_zero]
      exact huinv
    · rw [if_neg hi, add_zero]
      show ‖(if i = z then (x1 a0)⁻¹ else 1)‖ = 1
      rw [if_neg (fun h => hi h.symm)]
      simp
  refine ⟨g.submatrix id σ, fun a a' => hg a (σ a'), ?_, ?_⟩
  · rw [Matrix.det_permute', norm_mul, hdet, mul_one]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  · intro a
    have hsum : (∑ a', x1 a' * (g.submatrix id σ) a a') = ∑ b, x1 (σ b) * g a b :=
      Fintype.sum_equiv σ _ _ (fun a' => by simp [σ, Matrix.submatrix_apply])
    rw [hsum]
    show (∑ b, x1 (σ b) * ((if a = b then d a else 0) + (if z = b then e a else 0))) = _
    simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    by_cases ha : a = z
    · rw [if_pos ha, ha, hσz]
      show x1 a0 * (if z = z then (x1 a0)⁻¹ else 1) +
          x1 a0 * (if z = z then 0 else -(x1 (σ z) * (x1 a0)⁻¹)) = 1
      rw [if_pos (rfl : z = z), if_pos (rfl : z = z)]
      linear_combination mul_inv_cancel₀ hu0
    · rw [if_neg ha, hσz]
      show x1 (σ a) * (if a = z then (x1 a0)⁻¹ else 1) +
          x1 a0 * (if a = z then 0 else -(x1 (σ a) * (x1 a0)⁻¹)) = 0
      rw [if_neg ha, if_neg ha]
      linear_combination (-x1 (σ a)) * mul_inv_cancel₀ hu0
end Formalism.DworkPowerSeriesWeights
