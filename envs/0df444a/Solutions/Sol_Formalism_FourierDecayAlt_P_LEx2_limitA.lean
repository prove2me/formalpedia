-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.limitA
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:36:25.118842+00:00
-- url     : https://prove2.me/submissions/e347bea1-482c-4e69-93eb-7c4fc2cfb2cd

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeasIterDeriv
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaLimit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2BoundedMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_weighted_L2_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_weighted_L2_const_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_weighted_L2_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_extract
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_dS_poly
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_conjS_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_weighted_L2_bounded_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_sum3

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
open Polynomial
namespace Formalism.FourierDecayAlt.P.LEx2
theorem _root_.solution : LimitA := by
  intro hCo B N F hJ hM hPos hFac hBN hMon hCl Y hY
  obtain ⟨c, hc⟩ := hMon
  have hW0 : ∀ ω, 0 ≤ F.Wt ω ^ N := fun ω => pow_nonneg (hPos.1 ω).le N
  have hWm : Measurable fun ω => F.Wt ω ^ N := hM.1.pow_const N
  have hmonL2 : ∀ Y', (∀ a, Y' a ∈ F.J a) → ∀ i, WeightedL2 B (fun ω => F.Wt ω ^ N) (fun ω => F.mon Y' ω i) := by
    intro Y' hY' i
    obtain ⟨C, Binv, hb, hmB, hinv⟩ := hBN Y' hY'
    have hg : ∀ ω l, F.gw Y' F.u ω l = ∑ k, F.BN Y' ω l k * F.mon Y' ω k := by
      intro ω l
      have h := hFac Y' hY' 0 ω l
      rw [conjS_zero] at h
      simpa using h
    have hgm : ∀ l, Measurable fun ω => F.gw Y' F.u ω l := by
      intro l
      simp_rw [hg]
      exact Finset.measurable_sum _ fun k _ => (hM.2.2 Y' l k).mul (hM.2.1 Y' k)
    have hgl : ∀ l, WeightedL2 B (fun ω => F.Wt ω ^ N) (fun ω => F.gw Y' F.u ω l) := by
      intro l
      have hcw := hPos.2 Y' hY' l
      refine ⟨(hgm l).aestronglyMeasurable, ?_⟩
      refine Integrable.mono' ((hCl Y' hY').const_mul (1 / F.cw Y' l))
        (hWm.mul ((hgm l).norm.pow_const 2)).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_of_nonneg (mul_nonneg (hW0 ω) (by positivity))]
      have h1 : F.dw Y' ω l * ‖F.gw Y' F.u ω l‖ ^ 2 ≤ LE.sq B (F.dw Y') (F.gw Y' F.u) ω := by
        unfold LE.sq
        exact Finset.single_le_sum (f := fun l => F.dw Y' ω l * ‖F.gw Y' F.u ω l‖ ^ 2)
          (fun l _ => mul_nonneg (mul_nonneg (hW0 ω) (hPos.2 Y' hY' l).le) (by positivity)) (Finset.mem_univ l)
      calc F.Wt ω ^ N * ‖F.gw Y' F.u ω l‖ ^ 2 = 1 / F.cw Y' l * (F.dw Y' ω l * ‖F.gw Y' F.u ω l‖ ^ 2) := by
            unfold Fam.dw; field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)
    have hmon : (fun ω => F.mon Y' ω i) = fun ω => ∑ l, Binv ω i l * F.gw Y' F.u ω l := by
      funext ω
      simp_rw [hg]
      exact (hinv ω (F.mon Y' ω) i).symm
    rw [hmon]
    exact weighted_L2_sum B _ hW0 _ _ fun l _ =>
      weighted_L2_bounded_mul B _ hW0 hWm _ _ C (hmB i l) (fun ω => (hb ω i l).2) (hgl l)
  have hcL2 : ∀ κ k, WeightedL2 B (fun ω => F.Wt ω ^ N) (fun ω => c κ ω k) := fun κ k =>
    hCo B N (F.r + 1) (fun ω => F.Wt ω ^ N) (fun y ω => F.mon y ω k) (fun κ ω => c κ ω k) F.J hW0 hJ
      (fun y ω => hc y ω k) (fun y hy => hmonL2 y hy k) κ
  have hcm : ∀ κ k, Measurable fun ω => c κ ω k := by
    intro κ k
    choose grid _ hcard using fun a => (hJ a).exists_subset_card_eq (F.r + 1 + 1)
    have h : (fun ω => c κ ω k) = fun ω => ∑ g ∈ Fintype.piFinset grid,
        ((∏ a, (Lagrange.basis (grid a) id (g a)).coeff (κ a : ℕ) : ℝ) : ℂ) * F.mon g ω k := by
      funext ω
      rw [extract N (F.r + 1) grid hcard (fun κ' => c κ' ω k) κ]
      simp_rw [hc]
    rw [h]
    exact Finset.measurable_sum _ fun g _ => measurable_const.mul (hM.2.1 g k)
  set D : ℕ := N * (F.r + 1) with hD
  let P : (Fin N → Fin (F.r + 1 + 1)) → ℂ[X] := fun κ => ∏ a, (X + C ((Y a : ℝ) : ℂ)) ^ (κ a : ℕ)
  have heval : ∀ κ (s : ℝ), (P κ).eval (s : ℂ) = ((∏ a, (Y a + s) ^ (κ a : ℕ) : ℝ) : ℂ) := by
    intro κ s
    simp only [P, eval_prod, eval_pow, eval_add, eval_X, eval_C]
    push_cast
    apply Finset.prod_congr rfl; intro a _; ring
  have hdeg : ∀ κ, (P κ).natDegree < D + 1 := by
    intro κ
    refine Nat.lt_succ_of_le ((natDegree_prod_le _ _).trans ?_)
    calc ∑ a, ((X + C ((Y a : ℝ) : ℂ)) ^ (κ a : ℕ)).natDegree ≤ ∑ _a : Fin N, (F.r + 1) := by
          apply Finset.sum_le_sum; intro a _
          rw [natDegree_pow, natDegree_X_add_C, mul_one]
          exact Nat.lt_succ_iff.1 (κ a).2
      _ = D := by simp [hD]
  let e : ℕ → Fn B F.ι := fun q ω i => ∑ k, F.BN Y ω i k * ∑ κ, (P κ).coeff q * c κ ω k
  have hpoly : ∀ (s : ℝ) ω i, conjS B (F.gw Y) F.u s ω i = ∑ q ∈ range (D + 1), (s : ℂ) ^ q * e q ω i := by
    intro s ω i
    rw [hFac Y hY s ω i]
    simp_rw [hc, ← heval, fun κ => eval_eq_sum_range' (hdeg κ) (s : ℂ)]
    have lhs : ∑ k, F.BN Y ω i k * ∑ κ, (∑ q ∈ range (D + 1), (P κ).coeff q * (s : ℂ) ^ q) * c κ ω k =
        ∑ k, ∑ κ, ∑ q ∈ range (D + 1), F.BN Y ω i k * ((P κ).coeff q * (s : ℂ) ^ q * c κ ω k) := by
      apply Finset.sum_congr rfl; intro k _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro κ _
      rw [Finset.sum_mul, Finset.mul_sum]
    have rhs : ∑ q ∈ range (D + 1), (s : ℂ) ^ q * e q ω i =
        ∑ q ∈ range (D + 1), ∑ k, ∑ κ, F.BN Y ω i k * ((P κ).coeff q * (s : ℂ) ^ q * c κ ω k) := by
      apply Finset.sum_congr rfl; intro q _
      simp only [e]
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _
      rw [Finset.mul_sum, Finset.mul_sum]; apply Finset.sum_congr rfl; intro κ _
      ring
    rw [lhs, rhs]
    exact sum3 (D + 1) (fun k κ q => F.BN Y ω i k * ((P κ).coeff q * (s : ℂ) ^ q * c κ ω k))
  obtain ⟨C, Binv, hb, _, _⟩ := hBN Y hY
  have hem : ∀ q i, Measurable fun ω => e q ω i := fun q i =>
    Finset.measurable_sum _ fun k _ => (hM.2.2 Y i k).mul
      (Finset.measurable_sum _ fun κ _ => measurable_const.mul (hcm κ k))
  have heL2 : ∀ q i, WeightedL2 B (fun ω => F.Wt ω ^ N) (fun ω => e q ω i) := fun q i =>
    weighted_L2_sum B _ hW0 _ _ fun k _ => weighted_L2_bounded_mul B _ hW0 hWm _ _ C (hM.2.2 Y i k) (fun ω => (hb ω i k).1)
      (weighted_L2_sum B _ hW0 _ _ fun κ _ => weighted_L2_const_mul B _ _ _ (hcL2 κ k))
  refine ⟨⟨e, hpoly⟩, fun p => ?_⟩
  have hdS : ∀ i, (fun ω => dS B (F.gw Y) F.u p ω i) =
      fun ω => (p.factorial : ℂ) * (if p < D + 1 then e p ω i else 0) := fun i => by
    funext ω; exact dS_poly B (F.gw Y) F.u D e hpoly p ω i
  have hdL2 : ∀ i, WeightedL2 B (fun ω => F.Wt ω ^ N) (fun ω => dS B (F.gw Y) F.u p ω i) := by
    intro i
    rw [hdS i]
    apply weighted_L2_const_mul
    by_cases hp : p < D + 1
    · simp only [if_pos hp]; exact heL2 p i
    · simp only [if_neg hp]; exact weighted_L2_zero B _
  refine ⟨fun i => ?_, ?_⟩
  · rw [hdS i]
    by_cases hp : p < D + 1
    · simp only [if_pos hp]; exact measurable_const.mul (hem p i)
    · simp only [if_neg hp]; exact measurable_const
  · have he : LE.sq B (F.dw Y) (dS B (F.gw Y) F.u p) =
        fun ω => ∑ i, F.cw Y i * (F.Wt ω ^ N * ‖dS B (F.gw Y) F.u p ω i‖ ^ 2) := by
      funext ω; unfold LE.sq Fam.dw; apply Finset.sum_congr rfl; intros; ring
    rw [he]
    exact integrable_finset_sum _ fun i _ => (hdL2 i).2.const_mul _
end Formalism.FourierDecayAlt.P.LEx2
