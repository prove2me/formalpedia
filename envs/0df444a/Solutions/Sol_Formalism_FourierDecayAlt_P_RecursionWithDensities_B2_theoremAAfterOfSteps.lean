-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RecursionWithDensities.B2.theoremAAfterOfSteps
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:25:22.460856+00:00
-- url     : https://prove2.me/submissions/1e43ba09-2ed8-4b01-82ed-08af0aede224

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequalitySplitBySize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities
import Theorems.Thm_Formalism_FourierDecayAlt_P_OneLevelCoefficients_Q0
import Theorems.Thm_Formalism_FourierDecayAlt_P_OneLevelCoefficients_coef
import Theorems.Thm_Formalism_FourierDecayAlt_P_OneLevelCoefficients_gram_diag
import Theorems.Thm_Formalism_FourierDecayAlt_P_OneLevelCoefficients_size_le_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_OneLevelCoefficients_small


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RecursionWithDensities Formalism.FourierDecayAlt.P.RecursionWithDensities.B2
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.P.OneLevelCoefficients Finset
open scoped ComplexOrder
variable {E W : Type} [Field E]
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.B2
theorem _root_.solution : TC.TheoremAAfterOfSteps := by
  intro hOL hLS hJ C₁ C₄ h1 h4
  set C₀ : ℝ := max (3 * C₁) (2 * C₄) with hC₀
  have hC01 : 1 ≤ C₀ := le_trans (by linarith) (le_max_left _ _)
  have hC03 : 3 * C₁ ≤ C₀ := le_max_left _ _
  have hC04 : 2 * C₄ ≤ C₀ := le_max_right _ _
  obtain ⟨C'J, CJ, hJ⟩ := hJ C₀ hC01
  refine ⟨max C₀ CJ, max (max C'J (3 * C₁)) 1, ?_⟩
  intro E W _ D Θ jn H _ _ _ Vt c hK hf hΘ0 hC' hsm hS hG hKer hW hA2 hEB hDom hE72 hP hE73 hE74 hLat
    hE hCut hA4 R
  set C : ℝ := max C₀ CJ with hC
  have hCC0 : C₀ ≤ C := le_max_left _ _
  have hCCJ : CJ ≤ C := le_max_right _ _
  have hCpos : 0 ≤ C := by linarith
  have hΘ1 : 1 ≤ Θ := le_trans (le_max_right _ _) hC'
  have hΘ3 : 3 * C₁ ≤ Θ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hC'
  have hΘJ : C'J ≤ Θ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hC'
  set y : ℝ := Θ ^ (-((D.K : ℝ) - 5 / 2)) with hy
  have hy0 : 0 ≤ y := Real.rpow_nonneg hΘ0.le _
  have hK4 : (4 : ℝ) ≤ (D.K : ℝ) := by exact_mod_cast hK
  have hy1 : y ≤ Θ⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hΘ1 (by linarith)
  set ep : ℝ := (C₁ * y) ^ D.f with hep
  have hep0 : 0 ≤ ep := by positivity
  have ha : 3 ^ D.f * ep = (3 * C₁ * y) ^ D.f := by rw [hep, ← mul_pow, mul_assoc]
  have h3y : 3 * C₁ * y ≤ 1 := by
    calc 3 * C₁ * y ≤ Θ * Θ⁻¹ := mul_le_mul hΘ3 hy1 hy0 hΘ0.le
      _ = 1 := mul_inv_cancel₀ hΘ0.ne'
  have ha1 : 3 ^ D.f * ep ≤ 1 := by
    rw [ha]; exact pow_le_one₀ (by positivity) h3y
  have ha0 : 0 ≤ 3 ^ D.f * ep := by positivity
  have haC : 3 ^ D.f * ep ≤ (C₀ * y) ^ D.f := by
    rw [ha]; exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hC03 hy0) _
  have hb : 2 ^ D.f * ep ≤ 3 ^ D.f * ep :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) (by norm_num) _) hep0
  have he : ∀ i, 1 ≤ i → i ≤ D.r + 1 → 0 ≤ D.e i ∧ D.e i ≤ 1 := hEB
  set e' : ℕ → ℝ := fun i => if 1 ≤ i ∧ i ≤ D.r + 1 then D.e i else 0 with he'
  have he'0 : ∀ i, 0 ≤ e' i := by
    intro i; simp only [he']; split_ifs with h
    · exact (he i h.1 h.2).1
    · exact le_rfl
  have hprod : ∏ i ∈ Icc 1 (D.r + 1), (1 + e' i) = ∏ i ∈ Icc 1 (D.r + 1), (1 + D.e i) := by
    apply Finset.prod_congr rfl
    intro i hi; rw [Finset.mem_Icc] at hi
    simp only [he', if_pos hi]
  have hprod0 : 0 ≤ ∏ i ∈ Icc 1 (D.r + 1), (1 + D.e i) := by
    apply Finset.prod_nonneg
    intro i hi; rw [Finset.mem_Icc] at hi
    have := (he i hi.1 hi.2).1; linarith
  have hx0 : 0 ≤ (C₀ / Θ) ^ D.f := by positivity
  have hxy : (C₀ / Θ) ^ D.f ≤ (C / Θ) ^ D.f :=
    pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right hCC0 hΘ0.le) _
  have hr0 : (0 : ℝ) ≤ (D.r : ℝ) + 1 := by positivity
  have hBJ : 1 + CJ * ((D.r : ℝ) + 1) * (C₀ / Θ) ^ D.f ≤ 1 + C * ((D.r : ℝ) + 1) * (C / Θ) ^ D.f := by
    have s1 : CJ * ((D.r : ℝ) + 1) * (C₀ / Θ) ^ D.f ≤ C * ((D.r : ℝ) + 1) * (C₀ / Θ) ^ D.f :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCCJ hr0) hx0
    have s2 : C * ((D.r : ℝ) + 1) * (C₀ / Θ) ^ D.f ≤ C * ((D.r : ℝ) + 1) * (C / Θ) ^ D.f :=
      mul_le_mul_of_nonneg_left hxy (by positivity)
    linarith
  have hB0 : 0 ≤ 1 + C * ((D.r : ℝ) + 1) * (C / Θ) ^ D.f := by positivity
  have hK0 : (TC.withTh D (fun _ _ _ _ _ => 0)).KernelPSD :=
    ⟨hKer, fun _ _ _ Y => by
      show Matrix.PosSemidef (0 : Matrix Y Y ℂ)
      exact Matrix.PosSemidef.zero⟩
  suffices key : ∀ (T : Tower E) (ε : ℝ), 0 < ε → ∀ σ₀ : ℝ,
      (∀ w ∈ D.Wb D.Ntop, (D.gram ε 0 w [] []).re / D.wt w ≤ σ₀) →
      D.Sf ε (D.r + 1) D.emp (T.X (D.r + 1)) ≤
        ((1 + C * ((D.r : ℝ) + 1) * (C / Θ) ^ D.f) * (∏ i ∈ Icc 1 (D.r + 1), (1 + D.e i))) * σ₀ from
    hLS E W (TC.withTh D (fun _ _ _ _ _ => 0)) jn H Vt c hG hK0 hE hCut hA4 _ key R
  intro T ε hε σ₀ hσ₀
  have hempN : D.emp ∈ D.Wb D.Ntop := by
    simp [Data.Wb, D.emp_mem, D.cnt_emp]
  have hσ₀0 : 0 ≤ σ₀ := by
    refine le_trans ?_ (hσ₀ D.emp hempN)
    rw [D.wt_emp, div_one]; exact gram_diag D hG ε hε 0 D.emp []
  set S : ℕ → NNReal := fun k => (D.Wb (D.budget k)).sup (fun w => (D.Q T ε k w).toNNReal) with hSd
  set σ : ℕ → ℝ := fun k => √(S k : ℝ) with hσ
  have hσ0 : ∀ k, 0 ≤ σ k := fun k => Real.sqrt_nonneg _
  have hσsq : ∀ k, σ k ^ 2 = (S k : ℝ) := fun k => Real.sq_sqrt (NNReal.coe_nonneg _)
  have hσQ : ∀ k, ∀ w ∈ D.Wb (D.budget k), D.Q T ε k w ≤ σ k ^ 2 := by
    intro k w hw
    rw [hσsq]
    refine le_trans (Real.le_coe_toNNReal _) ?_
    exact_mod_cast Finset.le_sup (f := fun w => (D.Q T ε k w).toNNReal) hw
  have hSle : ∀ k (X : ℝ), 0 ≤ X → (∀ w ∈ D.Wb (D.budget k), D.Q T ε k w ≤ X) → (S k : ℝ) ≤ X := by
    intro k X hX h
    have : S k ≤ X.toNNReal := Finset.sup_le fun w hw => Real.toNNReal_le_toNNReal (h w hw)
    calc (S k : ℝ) ≤ (X.toNNReal : ℝ) := by exact_mod_cast this
      _ = X := Real.coe_toNNReal _ hX
  have hσle : ∀ k (X : ℝ), 0 ≤ X → (∀ w ∈ D.Wb (D.budget k), √(D.Q T ε k w) ≤ X) → σ k ≤ X := by
    intro k X hX h
    apply Real.sqrt_le_iff.mpr
    exact ⟨hX, hSle k _ (sq_nonneg X) fun w hw => (Real.sqrt_le_iff.mp (h w hw)).2⟩
  have hb0 : D.budget 0 = D.Ntop := by simp [Data.budget, Data.Ntop]
  have hσ00 : σ 0 ^ 2 ≤ σ₀ := by
    rw [hσsq]
    apply hSle 0 σ₀ hσ₀0
    intro w hw
    rw [Q0]; rw [hb0] at hw; exact hσ₀ w hw
  have hrec : ∀ i, 1 ≤ i → i ≤ D.r + 1 →
      σ i ≤ (1 + (C₀ * Θ ^ (-((D.K : ℝ) - 5 / 2))) ^ D.f) * √(1 + e' i) * σ (i - 1) +
        ∑ t ∈ Icc 2 i, ((C₀ / Θ) ^ D.f) ^ (t - 1) * σ (i - t) := by
    intro i hi1 hi
    have hei : e' i = D.e i := by simp only [he', if_pos (And.intro hi1 hi)]
    rw [hei]
    apply hσle i
    · apply add_nonneg
      · exact mul_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg _)) (hσ0 _)
      · exact Finset.sum_nonneg fun t _ => mul_nonneg (by positivity) (hσ0 _)
    intro w hw
    refine le_trans (hOL E W D ep C₄ hG hKer hW hA2 hEB hE72 hP hE73 hE74 hLat hep0 h4 hS.1
      (size_le_one D Θ hΘ1 hS) T (hDom T) ε hε σ i hi1 hi (fun k _ => ⟨hσ0 k, hσQ k⟩) w hw) ?_
    apply add_le_add
    · apply mul_le_mul_of_nonneg_right _ (hσ0 _)
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      apply Real.sqrt_le_iff.mpr
      refine ⟨by positivity, ?_⟩
      have q1 : 0 ≤ 2 ^ D.f * ep := by positivity
      nlinarith
    · apply Finset.sum_le_sum
      intro s hs; rw [Finset.mem_Icc] at hs
      apply mul_le_mul_of_nonneg_right _ (hσ0 _)
      exact coef D Θ C₄ C₀ _ _ hΘ1 h4 hC04 hf hS ha0 ha1 (he i hi1 hi).1 (he i hi1 hi).2 i s hs.1 hs.2 hi
  have hfin := hJ (D.K : ℝ) Θ D.f D.r e' σ hK4 hf hΘJ
    (small D.r D.f C C₀ Θ hΘ0 (by linarith) hCC0 hsm) he'0 hσ0 hrec
  rw [hprod] at hfin
  have hempB : D.emp ∈ D.Wb (D.budget (D.r + 1)) := by
    simp [Data.Wb, D.emp_mem, D.cnt_emp]
  have hQ := hσQ (D.r + 1) D.emp hempB
  have hQS : D.Q T ε (D.r + 1) D.emp = D.Sf ε (D.r + 1) D.emp (T.X (D.r + 1)) := by
    simp [Data.Q, D.wt_emp]
  rw [hQS] at hQ
  have hs0 : 0 ≤ σ 0 ^ 2 := sq_nonneg _
  calc D.Sf ε (D.r + 1) D.emp (T.X (D.r + 1)) ≤ σ (D.r + 1) ^ 2 := hQ
    _ ≤ (1 + CJ * ((D.r : ℝ) + 1) * (C₀ / Θ) ^ D.f) * (∏ i ∈ Icc 1 (D.r + 1), (1 + D.e i)) * σ 0 ^ 2 := hfin
    _ ≤ (1 + C * ((D.r : ℝ) + 1) * (C / Θ) ^ D.f) * (∏ i ∈ Icc 1 (D.r + 1), (1 + D.e i)) * σ 0 ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBJ hprod0) hs0
    _ ≤ (1 + C * ((D.r : ℝ) + 1) * (C / Θ) ^ D.f) * (∏ i ∈ Icc 1 (D.r + 1), (1 + D.e i)) * σ₀ :=
        mul_le_mul_of_nonneg_left hσ00 (mul_nonneg hB0 hprod0)
end Formalism.FourierDecayAlt.P.RecursionWithDensities.B2
