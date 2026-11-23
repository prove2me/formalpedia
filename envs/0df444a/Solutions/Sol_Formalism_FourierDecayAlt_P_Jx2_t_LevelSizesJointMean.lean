-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx2.t_LevelSizesJointMean
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:23.440928+00:00
-- url     : https://prove2.me/submissions/2efe18c6-b17c-4a20-b8e4-f1badd4401af

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx2
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped nonZeroDivisors ComplexConjugate
namespace Formalism.FourierDecayAlt.P.Jx2
theorem _root_.solution : LevelSizesJointMean := by
  intro C₁ C₄ hC₁ hC₄ E W _ D Θ hK hf hΘ hav hszD hszL he hSB hLS i hi
  have hΘpos : 0 < Θ := by linarith
  have hi' := Finset.mem_Icc.mp hi
  have hex1 : (1 : ℝ) ≤ (D.K : ℝ) - 5 / 2 := by
    have : (4 : ℝ) ≤ D.K := by exact_mod_cast hK
    linarith
  have hΘe : Θ ^ (-((D.K : ℝ) - 5 / 2)) ≤ Θ⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hΘepos : 0 < Θ ^ (-((D.K : ℝ) - 5 / 2)) := Real.rpow_pos_of_pos hΘpos _
  have hMpos : 0 < max (3 * C₁) (2 * C₄) := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  set X : ℝ := C₁ * Θ ^ (-((D.K : ℝ) - 5 / 2)) with hX
  set M : ℝ := max (3 * C₁) (2 * C₄) with hM
  set Y : ℝ := M * Θ ^ (-((D.K : ℝ) - 5 / 2)) with hY
  have hX0 : 0 ≤ X := mul_nonneg (by linarith) hΘepos.le
  have hY0 : 0 ≤ Y := mul_nonneg hMpos.le hΘepos.le
  have h3X : 3 * X ≤ 1 := by
    have h1 : 3 * C₁ * Θ⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv]
      first
      | exact (div_le_one hΘpos).mpr hΘ
      | exact (div_le_one₀ hΘpos).mpr hΘ
    have h2 : 3 * C₁ * Θ ^ (-((D.K : ℝ) - 5 / 2)) ≤ 3 * C₁ * Θ⁻¹ :=
      mul_le_mul_of_nonneg_left hΘe (by linarith)
    calc 3 * X = 3 * C₁ * Θ ^ (-((D.K : ℝ) - 5 / 2)) := by rw [hX]; ring
      _ ≤ 1 := h2.trans h1
  have h3XM : 3 * X ≤ Y := by
    calc 3 * X = 3 * C₁ * Θ ^ (-((D.K : ℝ) - 5 / 2)) := by rw [hX]; ring
      _ ≤ Y := mul_le_mul_of_nonneg_right (le_max_left _ _) hΘepos.le
  have hcard : (Fintype.card (Fin D.f → Fin 3) : ℝ) * X ^ D.f = (3 * X) ^ D.f := by
    first
    | (simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat, mul_pow]; done)
    | (simp [Fintype.card_fun, mul_pow]; done)
    | (rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, mul_pow]; push_cast; ring)
  have hA1 : (3 * X) ^ D.f ≤ 1 := by
    first
    | exact pow_le_one₀ (by linarith) h3X
    | exact pow_le_one _ (by linarith) h3X
  have hA2 : (3 * X) ^ D.f ≤ Y ^ D.f := by
    first
    | exact pow_le_pow_left (by linarith) h3XM _
    | exact pow_le_pow_left₀ (by linarith) h3XM _
  have hB2 : 2 ^ D.f * X ^ D.f ≤ Y ^ D.f := by
    rw [← mul_pow]
    have h2X : 2 * X ≤ Y := by linarith
    first
    | exact pow_le_pow_left (by linarith) h2X _
    | exact pow_le_pow_left₀ (by linarith) h2X _
  unfold TB.Data.LatticeSums at hLS
  unfold TB.Data.SizesBelow at hSB
  have hmaj : ∀ (z : Fin D.f → ℝ), (∀ v, 0 ≤ z v) → ∀ l, 0 ≤ D.maj z l := by
    intro z hz l
    unfold TB.Data.maj
    exact Finset.prod_nonneg (fun v _ => le_min zero_le_one
      (pow_nonneg (div_nonneg (hz v) (hav v l)) _))
  unfold TA.LevelSizes TA.LatSum
  try beta_reduce
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro l
    exact mul_nonneg (by positivity) (hmaj _ (hszD i) l)
  · intro S hS
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hLS.1 i hi'.1 hi'.2 S hS) (by positivity)
  · intro s hs hne
    have hs' := Finset.mem_Icc.mp hs
    exact ⟨hmaj _ (hszL _ _), fun S hS => hLS.2 i s hs'.1 hs'.2 hi'.2 hne S hS⟩
  · exact pow_nonneg hX0 _
  · show (1 + (Fintype.card (Fin D.f → Fin 3) : ℝ) * X ^ D.f) * (1 + 2 ^ D.f * X ^ D.f) ≤
      (1 + Y ^ D.f) ^ 2
    rw [hcard, sq]
    have hx0 := pow_nonneg hX0 D.f
    have hy0 := pow_nonneg hY0 D.f
    have h20 : (0 : ℝ) ≤ 2 ^ D.f * X ^ D.f := mul_nonneg (pow_nonneg zero_le_two D.f) hx0
    apply mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  · intro s hs
    have hs' := Finset.mem_Icc.mp hs
    have hvol0 : ∀ s', 0 ≤ D.vol (i - s + 1) s' := fun s' => hSB.1 _ _
    have hP0 : 0 ≤ ∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s' :=
      Finset.prod_nonneg (fun s' _ => hvol0 s')
    have hC4p : 0 ≤ C₄ ^ (D.f * s) := pow_nonneg (by linarith) _
    refine ⟨mul_nonneg hC4p hP0, ?_⟩
    have hPQ : ∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s' ≤ (((Θ ^ D.f)⁻¹) ^ 2) ^ (s - 1) := by
      calc ∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s' ≤ ∏ s' ∈ Ico 1 s, ((Θ ^ D.f)⁻¹) ^ 2 := by
            apply Finset.prod_le_prod (fun s' _ => hvol0 s')
            intro s' hs''
            have h5 := Finset.mem_Ico.mp hs''
            exact hSB.2 _ _ (by omega) h5.1 (by omega)
        _ = (((Θ ^ D.f)⁻¹) ^ 2) ^ (s - 1) := by rw [Finset.prod_const, Nat.card_Ico]
    have hQ0 : 0 ≤ (((Θ ^ D.f)⁻¹) ^ 2) ^ (s - 1) := by positivity
    have hAe : 1 + (Fintype.card (Fin D.f → Fin 3) : ℝ) * X ^ D.f ≤ 2 := by
      rw [hcard]
      linarith
    have hBe : 1 + D.e i ≤ 2 := by linarith [(he i hi'.1 hi'.2).2]
    have hB0 : 0 ≤ 1 + D.e i := by linarith [(he i hi'.1 hi'.2).1]
    have hkey : 4 * C₄ ^ (D.f * s) ≤ (M ^ D.f) ^ (2 * (s - 1)) := by
      have h2C : 2 * C₄ ≤ M := le_max_right _ _
      have h22 : 2 ≤ 2 * (s - 1) := by omega
      have hexp : 2 ≤ D.f * (2 * (s - 1)) := by
        have h6 := Nat.mul_le_mul hf h22
        simpa using h6
      have hexp2 : D.f * s ≤ D.f * (2 * (s - 1)) := Nat.mul_le_mul le_rfl (by omega)
      have h4 : (4 : ℝ) ≤ 2 ^ (D.f * (2 * (s - 1))) := by
        calc (4 : ℝ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (D.f * (2 * (s - 1))) := by
            first
            | exact pow_le_pow_right₀ (by norm_num) hexp
            | exact pow_le_pow_right (by norm_num) hexp
      have hc : C₄ ^ (D.f * s) ≤ C₄ ^ (D.f * (2 * (s - 1))) := by
        first
        | exact pow_le_pow_right₀ hC₄ hexp2
        | exact pow_le_pow_right hC₄ hexp2
      calc 4 * C₄ ^ (D.f * s) ≤ 2 ^ (D.f * (2 * (s - 1))) * C₄ ^ (D.f * (2 * (s - 1))) :=
            mul_le_mul h4 hc (pow_nonneg (by linarith) _) (by positivity)
        _ = (2 * C₄) ^ (D.f * (2 * (s - 1))) := by rw [mul_pow]
        _ ≤ M ^ (D.f * (2 * (s - 1))) := by
            first
            | exact pow_le_pow_left (by linarith) h2C _
            | exact pow_le_pow_left₀ (by linarith) h2C _
        _ = (M ^ D.f) ^ (2 * (s - 1)) := by rw [pow_mul]
    have hRHS : ((M / Θ) ^ D.f) ^ (2 * (s - 1)) =
        (M ^ D.f) ^ (2 * (s - 1)) * (((Θ ^ D.f)⁻¹) ^ 2) ^ (s - 1) := by
      rw [div_pow, div_eq_mul_inv, mul_pow, ← pow_mul ((Θ ^ D.f)⁻¹) 2 (s - 1)]
    show (1 + (Fintype.card (Fin D.f → Fin 3) : ℝ) * X ^ D.f) * (1 + D.e i) *
        (C₄ ^ (D.f * s) * ∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s') ≤ ((M / Θ) ^ D.f) ^ (2 * (s - 1))
    rw [hRHS]
    calc (1 + (Fintype.card (Fin D.f → Fin 3) : ℝ) * X ^ D.f) * (1 + D.e i) *
          (C₄ ^ (D.f * s) * ∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s')
        ≤ 2 * 2 * (C₄ ^ (D.f * s) * (((Θ ^ D.f)⁻¹) ^ 2) ^ (s - 1)) :=
          mul_le_mul (mul_le_mul hAe hBe hB0 (by norm_num)) (mul_le_mul_of_nonneg_left hPQ hC4p)
            (mul_nonneg hC4p hP0) (by norm_num)
      _ = (4 * C₄ ^ (D.f * s)) * (((Θ ^ D.f)⁻¹) ^ 2) ^ (s - 1) := by ring
      _ ≤ (M ^ D.f) ^ (2 * (s - 1)) * (((Θ ^ D.f)⁻¹) ^ 2) ^ (s - 1) :=
          mul_le_mul_of_nonneg_right hkey hQ0
end Formalism.FourierDecayAlt.P.Jx2
