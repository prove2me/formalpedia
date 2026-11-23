-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.fourth_reduction_identity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:00:45.88173+00:00
-- url     : https://prove2.me/submissions/3d3f4f0c-d0d8-4e32-b40a-bdab7bead7c4

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_cast
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_cast
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_last



set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution : Step4 := by
  intro P _ _ Om D _ w aN aZ H nn ngen q c κ hw hH hq hnn hN hZ hgen
  set 𝒜 := Om.powerset.filter (fun A => A.Nonempty) with h𝒜
  have hcard : (𝒜.card : ℝ) ≤ (2 : ℝ) ^ Om.card := by
    have : 𝒜.card ≤ 2 ^ Om.card := by
      rw [← Finset.card_powerset]; exact Finset.card_filter_le _ _
    exact_mod_cast this
  have hHc : ∀ p, 0 < H p ^ c := fun p => pow_pos (lt_of_lt_of_le one_pos (hH p)) _

  have one : ∀ A ∈ 𝒜, ∏ p, ∑ x : D p, w p x * ‖(if p ∈ A then aN p x else aZ p x)‖ ^ 2
      ≤ (∏ p, H p) ^ (2 * c) * ((2 : ℝ) ^ κ)⁻¹ * ∏ p, ngen p := by
    intro A hA
    obtain ⟨hAO, p0, hp0⟩ : A ⊆ Om ∧ A.Nonempty := by
      simpa [h𝒜, Finset.mem_filter, Finset.mem_powerset] using hA
    set g : P → ℝ := fun p => if p ∈ A then ((q p : ℝ) ^ κ)⁻¹ else 1 with hg
    have hg0 : ∀ p, 0 ≤ g p := fun p => by simp only [hg]; split_ifs <;> positivity
    have hq2 : ∀ p, ((q p : ℝ) ^ κ)⁻¹ ≤ ((2 : ℝ) ^ κ)⁻¹ := fun p => by
      apply inv_anti₀ (by positivity)
      gcongr
      exact_mod_cast hq p
    have h21 : ((2 : ℝ) ^ κ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    have hg1 : ∀ p, g p ≤ 1 := fun p => by
      simp only [hg]; split_ifs
      · exact (hq2 p).trans h21
      · exact le_rfl
    have hgp : ∏ p, g p ≤ ((2 : ℝ) ^ κ)⁻¹ := by
      rw [← Finset.mul_prod_erase univ g (Finset.mem_univ p0)]
      calc g p0 * ∏ p ∈ univ.erase p0, g p ≤ ((2 : ℝ) ^ κ)⁻¹ * 1 := by
            apply mul_le_mul
            · simp only [hg, if_pos hp0]; exact hq2 p0
            · exact Finset.prod_le_one (fun p _ => hg0 p) (fun p _ => hg1 p)
            · exact Finset.prod_nonneg fun p _ => hg0 p
            · positivity
        _ = _ := mul_one _
    calc ∏ p, ∑ x : D p, w p x * ‖(if p ∈ A then aN p x else aZ p x)‖ ^ 2
        ≤ ∏ p, (H p ^ c * (H p ^ c * ngen p)) * g p := by
          refine Finset.prod_le_prod (fun p _ => Finset.sum_nonneg fun x _ => mul_nonneg (hw p x) (sq_nonneg _))
            fun p _ => ?_
          have hb : H p ^ c * nn p ≤ H p ^ c * (H p ^ c * ngen p) :=
            mul_le_mul_of_nonneg_left (hgen p) (hHc p).le
          by_cases hp : p ∈ A
          · simp only [hg, if_pos hp]
            calc _ ≤ _ := hN p (hAO hp)
              _ = (H p ^ c * nn p) * ((q p : ℝ) ^ κ)⁻¹ := by ring
              _ ≤ _ := by gcongr
          · simp only [hg, if_neg hp, mul_one]
            exact (hZ p).trans hb
      _ = ((∏ p, H p) ^ (2 * c) * ∏ p, ngen p) * ∏ p, g p := by
          rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
            Finset.prod_pow, two_mul, pow_add]; ring
      _ ≤ ((∏ p, H p) ^ (2 * c) * ∏ p, ngen p) * ((2 : ℝ) ^ κ)⁻¹ := by
          refine mul_le_mul_of_nonneg_left hgp ?_
          refine mul_nonneg (pow_nonneg (Finset.prod_nonneg fun p _ => (zero_le_one.trans (hH p))) _)
            (Finset.prod_nonneg fun p _ => ?_)
          have := (hnn p).trans (hgen p)
          exact nonneg_of_mul_nonneg_right this (hHc p)
      _ = _ := by ring
  have hR0 : 0 ≤ (∏ p, H p) ^ (2 * c) * ((2 : ℝ) ^ κ)⁻¹ * ∏ p, ngen p := by
    refine mul_nonneg (mul_nonneg (pow_nonneg (Finset.prod_nonneg fun p _ => (zero_le_one.trans (hH p))) _) (by positivity))
      (Finset.prod_nonneg fun p _ => ?_)
    have := (hnn p).trans (hgen p)
    exact nonneg_of_mul_nonneg_right this (hHc p)
  calc ∑ d : (∀ p, D p), (∏ p, w p (d p)) *
        ‖∑ A ∈ 𝒜, ∏ p, (if p ∈ A then aN p (d p) else aZ p (d p))‖ ^ 2
      ≤ ∑ d : (∀ p, D p), (∏ p, w p (d p)) *
          ((𝒜.card : ℝ) * ∑ A ∈ 𝒜, ∏ p, ‖(if p ∈ A then aN p (d p) else aZ p (d p))‖ ^ 2) := by
        refine Finset.sum_le_sum fun d _ => mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun p _ => hw p _)
        calc ‖∑ A ∈ 𝒜, ∏ p, (if p ∈ A then aN p (d p) else aZ p (d p))‖ ^ 2
            ≤ (∑ A ∈ 𝒜, ‖∏ p, (if p ∈ A then aN p (d p) else aZ p (d p))‖) ^ 2 := by
              gcongr; exact norm_sum_le _ _
          _ ≤ (𝒜.card : ℝ) * ∑ A ∈ 𝒜, ‖∏ p, (if p ∈ A then aN p (d p) else aZ p (d p))‖ ^ 2 :=
              sq_sum_le_card_mul_sum_sq
          _ = _ := by
              congr 1
              refine Finset.sum_congr rfl fun A _ => ?_
              rw [norm_prod, Finset.prod_pow]
    _ = (𝒜.card : ℝ) * ∑ A ∈ 𝒜, ∏ p, ∑ x : D p, w p x * ‖(if p ∈ A then aN p x else aZ p x)‖ ^ 2 := by
        simp_rw [Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.prod_mul_distrib]; ring
    _ ≤ (2 : ℝ) ^ Om.card * ∑ A ∈ 𝒜, (∏ p, H p) ^ (2 * c) * ((2 : ℝ) ^ κ)⁻¹ * ∏ p, ngen p := by
        apply mul_le_mul hcard (Finset.sum_le_sum one) _ (by positivity)
        exact Finset.sum_nonneg fun A _ => Finset.prod_nonneg fun p _ => Finset.sum_nonneg fun x _ =>
          mul_nonneg (hw p x) (sq_nonneg _)
    _ = (2 : ℝ) ^ Om.card * ((𝒜.card : ℝ) * ((∏ p, H p) ^ (2 * c) * ((2 : ℝ) ^ κ)⁻¹ * ∏ p, ngen p)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 : ℝ) ^ Om.card * ((2 : ℝ) ^ Om.card * ((∏ p, H p) ^ (2 * c) * ((2 : ℝ) ^ κ)⁻¹ * ∏ p, ngen p)) := by
        gcongr
    _ = _ := by
        have : (4 : ℝ) ^ Om.card = (2 : ℝ) ^ Om.card * (2 : ℝ) ^ Om.card := by
          rw [← mul_pow]; norm_num
        rw [this]; ring
end Formalism.HermitianLatticeCounting.P.S4aux
