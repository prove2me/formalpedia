-- Prove2me | solution 1 for CubicNewton.LocalQuad.step_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:15:59.751729+00:00
-- url     : https://prove2.me/submissions/cf57f036-e86d-4bf5-802f-213dbda471bc

import Mathlib
import Definitions.Def_CubicNewton_Shared_IsCubicStep
import Definitions.Def_CubicNewton_Shared_lamMin

open scoped RealInnerProductSpace

namespace CubicNewton.LocalQuad

theorem aux_snl_rayleigh {n : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n)) (hv : v ≠ 0) :
    CubicNewton.Shared.lamMin A * ‖v‖ ^ 2 ≤ ⟪A v, v⟫ := by
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set u : EuclideanSpace ℝ (Fin n) := ‖v‖⁻¹ • v with hu
  have hu1 : u ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    rw [mem_sphere_zero_iff_norm, hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnv.ne']
  have hbdd : BddBelow (Set.range fun w : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
      ⟪A w, w⟫) := by
    refine ⟨-‖A‖, ?_⟩
    rintro _ ⟨w, rfl⟩
    have hw : ‖(w : EuclideanSpace ℝ (Fin n))‖ = 1 := mem_sphere_zero_iff_norm.mp w.2
    have h1 := abs_real_inner_le_norm (A w) (w : EuclideanSpace ℝ (Fin n))
    have h2 := A.le_opNorm (w : EuclideanSpace ℝ (Fin n))
    rw [hw] at h1 h2
    have := neg_abs_le ⟪A w, (w : EuclideanSpace ℝ (Fin n))⟫
    simp only
    linarith
  have hle : CubicNewton.Shared.lamMin A ≤ ⟪A u, u⟫ := by
    unfold CubicNewton.Shared.lamMin
    exact ciInf_le hbdd ⟨u, hu1⟩
  have hAu : ⟪A u, u⟫ = ‖v‖⁻¹ ^ 2 * ⟪A v, v⟫ := by
    rw [hu, map_smul, real_inner_smul_left, real_inner_smul_right]; ring
  rw [hAu] at hle
  calc CubicNewton.Shared.lamMin A * ‖v‖ ^ 2 ≤ (‖v‖⁻¹ ^ 2 * ⟪A v, v⟫) * ‖v‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hle (by positivity)
    _ = ⟪A v, v⟫ := by field_simp

end CubicNewton.LocalQuad

open CubicNewton.LocalQuad

theorem solution {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : ∀ x, HasFDerivAt g (H x) x)
    (hL : 0 < L) (hLip : ∀ x y, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (M : ℝ) (hM : 0 < M) (x T : EuclideanSpace ℝ (Fin n))
    (hpos : 0 < CubicNewton.Shared.lamMin (H x)) (hT : CubicNewton.Shared.IsCubicStep g H M x T) :
    ‖T - x‖ ≤ ‖g x‖ / CubicNewton.Shared.lamMin (H x) := by
  have hmin0 := hT
  unfold CubicNewton.Shared.IsCubicStep CubicNewton.Shared.cubicModel at hmin0
  set v := T - x with hv
  set lam := CubicNewton.Shared.lamMin (H x) with hlam
  by_cases hv0 : v = 0
  · rw [hv0, norm_zero]; exact div_nonneg (norm_nonneg _) hpos.le
  have hs : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  rw [le_div_iff₀ hpos]
  by_contra hcon
  push Not at hcon
  set t := ‖g x‖ / (lam * ‖v‖) with ht
  have ht0 : 0 ≤ t := by positivity
  have htlt : t < 1 := by rw [ht, div_lt_one (by positivity)]; linarith
  have hmin := hmin0 (x + t • v)
  have e1 : x + t • v - x = t • v := by abel
  rw [e1] at hmin
  simp only [map_smul, real_inner_smul_left, real_inner_smul_right, norm_smul,
    Real.norm_of_nonneg ht0] at hmin
  have hray := aux_snl_rayleigh (H x) v hv0
  have hcs := abs_real_inner_le_norm (g x) v
  have hcs2 := neg_abs_le ⟪g x, v⟫
  have htl : lam * ‖v‖ * t = ‖g x‖ := by rw [ht]; field_simp
  set a := ⟪g x, v⟫
  set b := ⟪H x v, v⟫
  set s := ‖v‖
  set G := ‖g x‖
  have hc : 0 ≤ M / 6 * s ^ 3 * (1 + t + t ^ 2) := by positivity
  have hid : (1 - t) * (a + b * (1 + t) / 2 + M / 6 * s ^ 3 * (1 + t + t ^ 2)) =
      (a + 1 / 2 * b + M / 6 * s ^ 3) - (t * a + 1 / 2 * (t * (t * b)) + M / 6 * (t * s) ^ 3) := by
    ring
  have hX : a + b * (1 + t) / 2 + M / 6 * s ^ 3 * (1 + t + t ^ 2) ≤ 0 := by
    by_contra hX
    push Not at hX
    have : 0 < (1 - t) * (a + b * (1 + t) / 2 + M / 6 * s ^ 3 * (1 + t + t ^ 2)) :=
      mul_pos (by linarith) hX
    linarith
  have hb : lam * s ^ 2 * (1 + t) / 2 ≤ b * (1 + t) / 2 := by
    have : 0 ≤ (1 + t) / 2 := by positivity
    nlinarith
  have hGs : a ≥ - (G * s) := by linarith
  -- lam*s^2*(1+t)/2 - G*s = s*(lam*s + G)/2 - G*s = s*(lam*s - G)/2 > 0
  have hkey : lam * s ^ 2 * (1 + t) / 2 - G * s = s * (lam * s - G) / 2 := by
    have : lam * s ^ 2 * t = G * s := by rw [← htl]; ring
    nlinarith
  have hpos2 : 0 < s * (lam * s - G) / 2 := by
    have : 0 < lam * s - G := by linarith
    positivity
  linarith
