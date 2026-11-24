-- Prove2me | solution 1 for Formalism.L2.SG.DensExact.densInertDisplay_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:25:05.793107+00:00
-- url     : https://prove2.me/submissions/718e72cc-b318-4d8f-8e23-9b67173d4488

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_DensExact
import Theorems.Thm_Formalism_L2_SG_DensExact_prod_pairs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.DensExact
namespace Formalism.L2.SG.DensExact
theorem _root_.solution : DensInertDisplay := by
  intro q n m c _ hcm hmc
  have hA : ∏ j ∈ Icc (n - m + c + 1) n, (1 - ((-(q : ℝ)) ^ j)⁻¹) =
      ∏ j ∈ Ico (n - m + c + 1) (n + 1), (1 - (-1 : ℝ) ^ j * ((q : ℝ) ^ j)⁻¹) := by
    have hI : Icc (n - m + c + 1) n = Ico (n - m + c + 1) (n + 1) := by
      ext x; simp only [mem_Icc, mem_Ico]; omega
    rw [hI]
    refine prod_congr rfl (fun j _ => ?_)
    rcases neg_one_pow_eq_or ℝ j with h | h <;> simp [neg_pow, h]
  have hB : ∏ i ∈ range c, ((1 - (-1 : ℝ) ^ (n - m + c - 2 * i) * ((q : ℝ) ^ (n - m + c - 2 * i))⁻¹) *
          (1 + (-1 : ℝ) ^ (n - m + c - 2 * i) * ((q : ℝ) ^ (n - m + c - 2 * i - 1))⁻¹)) =
      ∏ i ∈ range c, ((1 - (-1 : ℝ) ^ (n - m + c - 2 * i) * ((q : ℝ) ^ (n - m + c - 2 * i))⁻¹) *
          (1 - (-1 : ℝ) ^ (n - m + c - 2 * i - 1) * ((q : ℝ) ^ (n - m + c - 2 * i - 1))⁻¹)) := by
    refine prod_congr rfl (fun i hi => ?_)
    have hi' : i < c := mem_range.mp hi
    obtain ⟨k, hk⟩ : ∃ k, n - m + c - 2 * i = k + 1 := ⟨n - m + c - 2 * i - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel]
    ring
  have hC : ∏ i ∈ range c, ((1 - (-1 : ℝ) ^ (n - m + c - 2 * i) * ((q : ℝ) ^ (n - m + c - 2 * i))⁻¹) *
          (1 - (-1 : ℝ) ^ (n - m + c - 2 * i - 1) * ((q : ℝ) ^ (n - m + c - 2 * i - 1))⁻¹)) =
      ∏ j ∈ Ico (n - m + c + 1 - 2 * c) (n - m + c + 1), (1 - (-1 : ℝ) ^ j * ((q : ℝ) ^ j)⁻¹) :=
    prod_pairs (fun j => 1 - (-1 : ℝ) ^ j * ((q : ℝ) ^ j)⁻¹) c (n - m + c) (by omega)
  have hD : densProd q (-1) n m c =
      ∏ j ∈ Ico (n - m + c + 1 - 2 * c) (n + 1), (1 - (-1 : ℝ) ^ j * ((q : ℝ) ^ j)⁻¹) := by
    unfold densProd
    have hI : Icc (n + 1 - (m + c)) n = Ico (n - m + c + 1 - 2 * c) (n + 1) := by
      ext x; simp only [mem_Icc, mem_Ico]; omega
    rw [hI]
  rw [hA, hB, hC, hD, ← prod_Ico_consecutive (fun j => 1 - (-1 : ℝ) ^ j * ((q : ℝ) ^ j)⁻¹)
    (by omega : n - m + c + 1 - 2 * c ≤ n - m + c + 1) (by omega : n - m + c + 1 ≤ n + 1)]
  ring
end Formalism.L2.SG.DensExact
