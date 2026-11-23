-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SecondPolynomialClauses.third_polynomial_prime_combination
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:30:59.599198+00:00
-- url     : https://prove2.me/submissions/968d4f47-7b04-4730-beab-745eb16e9d56

import Definitions.Def_Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondPolynomialClauses

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SecondPolynomialClauses
open Formalism.FourierDecayAlt.PairingProductCorollary
namespace Formalism.FourierDecayAlt.P.SecondPolynomialClauses
theorem _root_.solution : LeadingBlockSeveralPlacesBound := by
  intro ι _ _ K abelian₂ t t' Ntt Nt Nt' S1 S2 ht hLam hNt hNt' hS1 hS2 hG hA hB
  obtain ⟨m, hm⟩ : ∃ m : ι → ℝ, m = fun v => minFac (2 * abelian₂ v) (oAbs t t' v) K := ⟨_, rfl⟩
  have hm0 : ∀ v, 0 ≤ m v := by
    intro v; rw [hm]; dsimp only; unfold minFac; split_ifs with h
    · exact pow_nonneg (div_nonneg (by linarith [hLam v]) (norm_nonneg _)) _
    · exact zero_le_one
  have key : ∀ v (s : ℝ), 0 ≤ s → s * oAbs t t' v ≤ 2 → 2 * abelian₂ v < oAbs t t' v →
      (s * abelian₂ v) ^ (2 * K) ≤ m v ^ 2 := by
    intro v s hs hso hlt
    have ho : 0 < oAbs t t' v := lt_of_le_of_lt (by linarith [hLam v]) hlt
    have hmv : m v = (2 * abelian₂ v / oAbs t t' v) ^ K := by rw [hm]; dsimp only; rw [minFac, if_pos hlt]
    rw [hmv, ← pow_mul, mul_comm K 2]
    apply pow_le_pow_left₀ (mul_nonneg hs (hLam v))
    rw [le_div_iff₀ ho]; nlinarith [mul_le_mul_of_nonneg_right hso (hLam v)]
  have h1 : ∀ v, oAbs t t' v ≤ 1 / ‖t v‖ + 1 / ‖t' v‖ := by
    intro v; unfold oAbs
    calc _ ≤ ‖1 / t v‖ + ‖1 / t' v‖ := norm_sub_le _ _
      _ = _ := by rw [norm_div, norm_div, norm_one]
  have hto : ∀ v, ‖t v‖ ≤ ‖t' v‖ → ‖t v‖ * oAbs t t' v ≤ 2 := by
    intro v hle
    have ha : 0 < ‖t v‖ := norm_pos_iff.mpr (ht v).1
    have hb : 0 < ‖t' v‖ := norm_pos_iff.mpr (ht v).2
    calc ‖t v‖ * oAbs t t' v ≤ ‖t v‖ * (1 / ‖t v‖ + 1 / ‖t' v‖) := mul_le_mul_of_nonneg_left (h1 v) ha.le
      _ = 1 + ‖t v‖ / ‖t' v‖ := by rw [mul_add, mul_one_div_cancel ha.ne', mul_one_div]
      _ ≤ 2 := by linarith [(div_le_one hb).mpr hle]
  have hto' : ∀ v, ¬ ‖t v‖ ≤ ‖t' v‖ → ‖t' v‖ * oAbs t t' v ≤ 2 := by
    intro v hle
    have ha : 0 < ‖t v‖ := norm_pos_iff.mpr (ht v).1
    have hb : 0 < ‖t' v‖ := norm_pos_iff.mpr (ht v).2
    calc ‖t' v‖ * oAbs t t' v ≤ ‖t' v‖ * (1 / ‖t v‖ + 1 / ‖t' v‖) := mul_le_mul_of_nonneg_left (h1 v) hb.le
      _ = ‖t' v‖ / ‖t v‖ + 1 := by rw [mul_add, mul_one_div_cancel hb.ne', mul_one_div]
      _ ≤ 2 := by linarith [(div_le_one ha).mpr (le_of_lt (not_le.mp hle))]
  have hPA : (∏ v ∈ univ.filter (fun v => 2 * abelian₂ v < oAbs t t' v ∧ ‖t v‖ ≤ ‖t' v‖),
      (‖t v‖ * abelian₂ v) ^ (2 * K)) ≤
      ∏ v ∈ univ.filter (fun v => 2 * abelian₂ v < oAbs t t' v ∧ ‖t v‖ ≤ ‖t' v‖), m v ^ 2 :=
    Finset.prod_le_prod (fun v _ => pow_nonneg (mul_nonneg (norm_nonneg _) (hLam v)) _)
      (fun v hv => by
        obtain ⟨hv1, hv2⟩ := (Finset.mem_filter.mp hv).2
        exact key v _ (norm_nonneg _) (hto v hv2) hv1)
  have hPB : (∏ v ∈ univ.filter (fun v => 2 * abelian₂ v < oAbs t t' v ∧ ¬ ‖t v‖ ≤ ‖t' v‖),
      (‖t' v‖ * abelian₂ v) ^ (2 * K)) ≤
      ∏ v ∈ univ.filter (fun v => 2 * abelian₂ v < oAbs t t' v ∧ ¬ ‖t v‖ ≤ ‖t' v‖), m v ^ 2 :=
    Finset.prod_le_prod (fun v _ => pow_nonneg (mul_nonneg (norm_nonneg _) (hLam v)) _)
      (fun v hv => by
        obtain ⟨hv1, hv2⟩ := (Finset.mem_filter.mp hv).2
        exact key v _ (norm_nonneg _) (hto' v hv2) hv1)
  have hdisj : Disjoint (univ.filter (fun v => 2 * abelian₂ v < oAbs t t' v ∧ ‖t v‖ ≤ ‖t' v‖))
      (univ.filter (fun v => 2 * abelian₂ v < oAbs t t' v ∧ ¬ ‖t v‖ ≤ ‖t' v‖)) :=
    Finset.disjoint_filter.mpr fun v _ hv1 hv2 => hv2.2 hv1.2
  have hM : (∏ v ∈ univ.filter (fun v => 2 * abelian₂ v < oAbs t t' v ∧ ‖t v‖ ≤ ‖t' v‖), m v ^ 2) *
      (∏ v ∈ univ.filter (fun v => 2 * abelian₂ v < oAbs t t' v ∧ ¬ ‖t v‖ ≤ ‖t' v‖), m v ^ 2) =
      (∏ v, m v) ^ 2 := by
    rw [← Finset.prod_union hdisj, ← Finset.prod_pow]
    apply Finset.prod_subset (Finset.subset_univ _)
    intro v _ hv
    have hnot : ¬ 2 * abelian₂ v < oAbs t t' v := by
      intro hlt
      apply hv
      by_cases hle : ‖t v‖ ≤ ‖t' v‖
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, hle⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, hle⟩)
    rw [hm]; dsimp only; rw [minFac, if_neg hnot, one_pow]
  have hM0 : 0 ≤ ∏ v, m v := Finset.prod_nonneg fun v _ => hm0 v
  have hgoal : ∏ v, minFac (2 * abelian₂ v) (oAbs t t' v) K = ∏ v, m v := by rw [hm]
  rw [hgoal]
  have hsq : ‖Ntt‖ ^ 2 ≤ ((∏ v, m v) * ((S1 + S2) / 2)) ^ 2 := by
    calc ‖Ntt‖ ^ 2 ≤ Nt * Nt' := hG
      _ ≤ ((∏ v ∈ univ.filter (fun v => 2 * abelian₂ v < oAbs t t' v ∧ ‖t v‖ ≤ ‖t' v‖),
            (‖t v‖ * abelian₂ v) ^ (2 * K)) * S1) *
          ((∏ v ∈ univ.filter (fun v => 2 * abelian₂ v < oAbs t t' v ∧ ¬ ‖t v‖ ≤ ‖t' v‖),
            (‖t' v‖ * abelian₂ v) ^ (2 * K)) * S2) :=
          mul_le_mul hA hB hNt' (le_trans hNt hA)
      _ ≤ ((∏ v ∈ univ.filter (fun v => 2 * abelian₂ v < oAbs t t' v ∧ ‖t v‖ ≤ ‖t' v‖), m v ^ 2) * S1) *
          ((∏ v ∈ univ.filter (fun v => 2 * abelian₂ v < oAbs t t' v ∧ ¬ ‖t v‖ ≤ ‖t' v‖), m v ^ 2) * S2) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hPA hS1) (mul_le_mul_of_nonneg_right hPB hS2)
            (mul_nonneg (Finset.prod_nonneg fun v _ => pow_nonneg (mul_nonneg (norm_nonneg _) (hLam v)) _) hS2)
            (mul_nonneg (Finset.prod_nonneg fun v _ => sq_nonneg _) hS1)
      _ = (∏ v, m v) ^ 2 * (S1 * S2) := by rw [← hM]; ring
      _ ≤ (∏ v, m v) ^ 2 * ((S1 + S2) / 2) ^ 2 :=
          mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (S1 - S2)]) (sq_nonneg _)
      _ = _ := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hM0 (by linarith)) two_ne_zero).mp hsq
end Formalism.FourierDecayAlt.P.SecondPolynomialClauses
