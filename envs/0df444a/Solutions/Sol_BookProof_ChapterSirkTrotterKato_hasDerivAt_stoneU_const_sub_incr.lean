-- Prove2me | solution 1 for BookProof.ChapterSirkTrotterKato.hasDerivAt_stoneU_const_sub_incr
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T07:12:49.704805+00:00
-- url     : https://prove2.me/submissions/ff17798a-c06a-4701-a8e9-0062e6534788

-- Generated from ChapterSirkTrotterKato.lean — solution of BookProof.ChapterSirkTrotterKato.hasDerivAt_stoneU_const_sub_incr
import Mathlib
import Definitions.Def_ChapterSirkTrotterKato
open BookProof.ChapterSirkTrotterKato











noncomputable section

open Filter Topology Asymptotics
open scoped InnerProductSpace


open BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

set_option maxHeartbeats 1000000 in
theorem solution (S : UnboundedSelfAdjoint H) {y : ℝ → H} {y' : H}
    {t u : ℝ} (hy : HasDerivAt y y' u) :
    HasDerivAt (fun r : ℝ => S.stoneU (t - r) (y r - y u)) (S.stoneU (t - u) y') u := by

  rw [hasDerivAt_iff_isLittleO]
  have hA : (fun r : ℝ => S.stoneU (t - r) (y r - y u - (r - u) • y')) =o[𝓝 u]
      fun r : ℝ => r - u := by
    have h := hasDerivAt_iff_isLittleO.mp hy
    rw [isLittleO_iff] at h ⊢
    intro c hc
    filter_upwards [h hc] with r hr
    calc ‖S.stoneU (t - r) (y r - y u - (r - u) • y')‖ = ‖y r - y u - (r - u) • y'‖ :=
          S.norm_stoneU_apply _ _
      _ ≤ c * ‖r - u‖ := hr
  have hB : (fun r : ℝ => (r - u) • (S.stoneU (t - r) y' - S.stoneU (t - u) y')) =o[𝓝 u]
      fun r : ℝ => r - u := by
    rw [isLittleO_iff]
    intro c hc
    have hcty : Continuous fun r : ℝ => S.stoneU (t - r) y' :=
      (S.continuous_stoneU_apply y').comp (continuous_const.sub continuous_id)
    have hc0 : Tendsto (fun r : ℝ => S.stoneU (t - r) y' - S.stoneU (t - u) y') (𝓝 u) (𝓝 0) := by
      have h1 : Tendsto (fun r : ℝ => S.stoneU (t - r) y') (𝓝 u) (𝓝 (S.stoneU (t - u) y')) :=
        hcty.tendsto u
      have h2 := h1.sub (tendsto_const_nhds (x := S.stoneU (t - u) y') (f := 𝓝 u))
      simpa using h2
    have hev : ∀ᶠ r in 𝓝 u, ‖S.stoneU (t - r) y' - S.stoneU (t - u) y'‖ ≤ c := by
      have h3 := hc0.norm
      simp only [norm_zero] at h3
      exact h3.eventually_le_const hc
    filter_upwards [hev] with r hr
    rw [norm_smul]
    simp only [Real.norm_eq_abs]
    calc |r - u| * ‖S.stoneU (t - r) y' - S.stoneU (t - u) y'‖ ≤ |r - u| * c :=
          mul_le_mul_of_nonneg_left hr (abs_nonneg _)
      _ = c * ‖r - u‖ := by rw [Real.norm_eq_abs]; ring
  have heq : (fun r : ℝ => S.stoneU (t - r) (y r - y u) - S.stoneU (t - u) (y u - y u)
        - (r - u) • S.stoneU (t - u) y')
      = fun r : ℝ => S.stoneU (t - r) (y r - y u - (r - u) • y')
          + (r - u) • (S.stoneU (t - r) y' - S.stoneU (t - u) y') := by
    funext r
    have h1 : S.stoneU (t - r) (y r - y u - (r - u) • y')
        = S.stoneU (t - r) (y r - y u) - (r - u) • S.stoneU (t - r) y' := by
      rw [map_sub, ContinuousLinearMap.map_smul_of_tower]
    simp only [sub_self, map_zero, sub_zero, h1, smul_sub]
    abel
  rw [heq]
  exact hA.add hB
