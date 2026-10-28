-- Prove2me | solution 1 for FunctionalInequalities.Analysis.resolvent_preimage_near_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:29:19.588568+00:00
-- url     : https://prove2.me/submissions/af67e390-58d4-4c0c-a429-2b05cb6817ed

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_SecondOrder

noncomputable section
open Set Filter
open scoped RealInnerProductSpace Topology
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
set_option maxHeartbeats 800000 in
 lemma solution {P : E → E} {z : E}
    (hm : ∀ a b, ‖P a - P b‖ ^ 2 ≤ ⟪P a - P b, a - b⟫)
    {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (hl : ∀ w, ‖w - z‖ < δ → c * ‖w - z‖ ≤ ‖P w - P z‖)
    (a : E) (ha : ‖P a - P z‖ < c ^ 2 * δ / 2) :
    ‖a - z‖ < δ := by
  by_contra hn
  have hN : 0 < ‖a - z‖ := lt_of_lt_of_le hδ (le_of_not_gt hn)
  let s : ℝ := δ / (2 * ‖a - z‖)
  have hs : 0 < s := div_pos hδ (by positivity)
  have hs1 : s < 1 :=
    (div_lt_one (by positivity)).2 (by linarith [le_of_not_gt hn])
  have hsN : s * ‖a - z‖ = δ / 2 := by
    dsimp [s]
    field_simp
  let w := z + s • (a - z)
  have hw : w - z = s • (a - z) := by
    dsimp [w]
    abel
  have hwn : ‖w - z‖ = s * ‖a - z‖ := by
    rw [hw, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
  have hwl : ‖w - z‖ < δ := by
    rw [hwn, hsN]
    linarith
  have hlow := hl w hwl
  have hsq :=
    (sq_le_sq₀ (mul_nonneg hc.le (norm_nonneg (w - z)))
      (norm_nonneg (P w - P z))).2 hlow
  have hm1 := hm w z
  rw [hw, real_inner_smul_right] at hm1
  have haw : a - w = (1 - s) • (a - z) := by
    dsimp [w]
    module
  have hm2 := hm a w
  rw [haw, real_inner_smul_right] at hm2
  have hip :
      ⟪P a - P w, a - z⟫ =
        ⟪P a - P z, a - z⟫ - ⟪P w - P z, a - z⟫ := by
    simp only [inner_sub_left]
    ring
  rw [hip] at hm2
  have hmon : ⟪P w - P z, a - z⟫ ≤ ⟪P a - P z, a - z⟫ := by
    nlinarith [sq_nonneg ‖P a - P w‖]
  have hupper := real_inner_le_norm (P a - P z) (a - z)
  have hb := hsq.trans
    (hm1.trans (mul_le_mul_of_nonneg_left (hmon.trans hupper) hs.le))
  rw [hwn] at hb
  have hcancel : c ^ 2 * (s * ‖a - z‖) ≤ ‖P a - P z‖ :=
    le_of_mul_le_mul_right (by nlinarith only [hb]) (mul_pos hs hN)
  rw [hsN] at hcancel
  nlinarith only [hcancel, ha]
