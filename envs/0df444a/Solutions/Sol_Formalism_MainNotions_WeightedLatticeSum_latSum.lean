-- Prove2me | solution 1 for Formalism.MainNotions.WeightedLatticeSum.latSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:06:59.241826+00:00
-- url     : https://prove2.me/submissions/193dd3d3-62cf-41e9-afb0-0f0a755fbce4

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_WeightedLatticeSum
import Theorems.Thm_Formalism_MainNotions_WeightedLatticeSum_wt_nonneg
import Theorems.Thm_Formalism_MainNotions_WeightedLatticeSum_sum_wt_int_le
import Theorems.Thm_Formalism_MainNotions_WeightedLatticeSum_floor_bound
import Theorems.Thm_Formalism_MainNotions_WeightedLatticeSum_cplx_bound
import Theorems.Thm_Formalism_MainNotions_WeightedLatticeSum_norm_lt_one_of_cell

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.WeightedLatticeSum
open Finset
namespace Formalism.MainNotions.WeightedLatticeSum
theorem _root_.solution (ι : Type) [Fintype ι] (P : Finset (ι → ℂ)) (R : ℝ) (hR : 1 ≤ R)
    (hsep : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → 1 ≤ ∏ i, ‖p i - q i‖) :
    ∑ p ∈ P, ∏ i, (max 1 (‖p i‖ / R)) ^ (-(3 : ℝ)) ≤ (64 * R) ^ (2 * Fintype.card ι) := by
  classical
  have hR0 : 0 < R := by linarith
  let cell : (ι → ℂ) → (ι → ℤ × ℤ) := fun p i => (⌊2 * (p i).re⌋, ⌊2 * (p i).im⌋)
  have hf0 : ∀ x : ℤ × ℤ, 0 ≤ wt R x.1.natAbs * wt R x.2.natAbs :=
    fun x => mul_nonneg (wt_nonneg _ _) (wt_nonneg _ _)
  have hpt : ∀ p : ι → ℂ, ∏ i, (max 1 (‖p i‖ / R)) ^ (-(3 : ℝ)) ≤
      ∏ i, wt R (cell p i).1.natAbs * wt R (cell p i).2.natAbs := by
    intro p
    apply Finset.prod_le_prod
    · intro i _
      exact Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _
    · intro i _
      calc (max 1 (‖p i‖ / R)) ^ (-(3 : ℝ))
          ≤ (max 1 (|(p i).re| / R)) ^ (-(3 / 2 : ℝ)) * (max 1 (|(p i).im| / R)) ^ (-(3 / 2 : ℝ)) :=
            cplx_bound R hR0 (p i)
        _ ≤ wt R (cell p i).1.natAbs * wt R (cell p i).2.natAbs :=
            mul_le_mul (floor_bound R hR _) (floor_bound R hR _)
              (Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _) (wt_nonneg _ _)
  have hinj : ∀ p ∈ P, ∀ q ∈ P, cell p = cell q → p = q := by
    intro p hp q hq hpq
    by_contra hne
    have hs := hsep p hp q hq hne
    have hlt : ∀ i, ‖p i - q i‖ < 1 := by
      intro i
      have e := congrFun hpq i
      exact norm_lt_one_of_cell (p i) (q i) (congrArg Prod.fst e) (congrArg Prod.snd e)
    rcases isEmpty_or_nonempty ι with hι | hι
    · exact hne (funext fun i => hι.elim i)
    · obtain ⟨i0⟩ := hι
      have hE : ∏ i ∈ Finset.univ.erase i0, ‖p i - q i‖ ≤ 1 :=
        Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => (hlt i).le)
      have hE0 : 0 ≤ ∏ i ∈ Finset.univ.erase i0, ‖p i - q i‖ :=
        Finset.prod_nonneg (fun i _ => norm_nonneg _)
      have hsplit : ‖p i0 - q i0‖ * ∏ i ∈ Finset.univ.erase i0, ‖p i - q i‖ = ∏ i, ‖p i - q i‖ :=
        Finset.mul_prod_erase Finset.univ (fun i => ‖p i - q i‖) (Finset.mem_univ i0)
      nlinarith [hlt i0, norm_nonneg (p i0 - q i0)]
  obtain ⟨S, hS⟩ : ∃ S : Finset (ℤ × ℤ), ∀ c ∈ P.image cell, ∀ i, c i ∈ S :=
    ⟨(P.image cell).biUnion (fun c => Finset.univ.image c), fun c hc i =>
      Finset.mem_biUnion.mpr ⟨c, hc, Finset.mem_image_of_mem c (Finset.mem_univ i)⟩⟩
  have hSf : ∑ x ∈ S, wt R x.1.natAbs * wt R x.2.natAbs ≤ (18 * R) * (18 * R) := by
    calc ∑ x ∈ S, wt R x.1.natAbs * wt R x.2.natAbs
        ≤ ∑ x ∈ (S.image Prod.fst) ×ˢ (S.image Prod.snd), wt R x.1.natAbs * wt R x.2.natAbs := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro x hx
            exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hx, Finset.mem_image_of_mem _ hx⟩
          · intro x _ _
            exact hf0 x
      _ = (∑ a ∈ S.image Prod.fst, wt R a.natAbs) * (∑ b ∈ S.image Prod.snd, wt R b.natAbs) := by
          rw [Finset.sum_product, Finset.sum_mul_sum]
      _ ≤ (18 * R) * (18 * R) :=
          mul_le_mul (sum_wt_int_le R hR _) (sum_wt_int_le R hR _)
            (Finset.sum_nonneg (fun b _ => wt_nonneg _ _)) (by linarith)
  calc ∑ p ∈ P, ∏ i, (max 1 (‖p i‖ / R)) ^ (-(3 : ℝ))
      ≤ ∑ p ∈ P, ∏ i, wt R (cell p i).1.natAbs * wt R (cell p i).2.natAbs :=
        Finset.sum_le_sum (fun p _ => hpt p)
    _ = ∑ c ∈ P.image cell, ∏ i, wt R (c i).1.natAbs * wt R (c i).2.natAbs := by
        rw [Finset.sum_image hinj]
    _ ≤ ∑ c ∈ Fintype.piFinset (fun _ : ι => S), ∏ i, wt R (c i).1.natAbs * wt R (c i).2.natAbs := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro c hc
          exact Fintype.mem_piFinset.mpr (fun i => hS c hc i)
        · intro c _ _
          exact Finset.prod_nonneg (fun i _ => hf0 _)
    _ = ∏ _i : ι, ∑ x ∈ S, wt R x.1.natAbs * wt R x.2.natAbs :=
        (Finset.prod_univ_sum (fun _ : ι => S)
          (fun _ x => wt R x.1.natAbs * wt R x.2.natAbs)).symm
    _ ≤ ∏ _i : ι, ((18 * R) * (18 * R)) := by
        apply Finset.prod_le_prod
        · intro i _
          exact Finset.sum_nonneg (fun x _ => hf0 x)
        · intro i _
          exact hSf
    _ = (18 * R) ^ (2 * Fintype.card ι) := by
        rw [Finset.prod_const, Finset.card_univ, pow_mul, sq]
    _ ≤ (64 * R) ^ (2 * Fintype.card ι) := pow_le_pow_left₀ (by linarith) (by linarith) _
end Formalism.MainNotions.WeightedLatticeSum
