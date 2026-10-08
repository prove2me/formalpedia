-- Prove2me | solution 1 for BeckTeboulleMD.EMDA.bregman_ge_sq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T19:50:35.206461+00:00
-- url     : https://prove2.me/submissions/4ceac223-40c3-4855-9661-45d31bbfa383

import Mathlib
import Definitions.Def_BeckTeboulleMD_EMDA_Setting

set_option autoImplicit false

open Filter Topology in
theorem f3f6d117_key {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (ψ : E → ℝ) (σ : ℝ) (hψ : StrongConvexOn X σ ψ)
    (u : E) (hu : u ∈ X) (y : E) (hy : y ∈ X) (hd : DifferentiableAt ℝ ψ y) :
    fderiv ℝ ψ y (u - y) ≤ ψ u - ψ y - σ / 2 * ‖u - y‖ ^ 2 := by
  set v := u - y with hv
  set g : ℝ → ℝ := fun t => ψ (y + t • v) with hg
  have hline : HasDerivAt (fun t : ℝ => y + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add y
  have hgd : HasDerivAt g (fderiv ℝ ψ y v) 0 := by
    have h1 : HasFDerivAt ψ (fderiv ℝ ψ y) (y + (0:ℝ) • v) := by
      simpa using hd.hasFDerivAt
    exact h1.comp_hasDerivAt (0:ℝ) hline
  have hslope := hgd.tendsto_slope_zero_right
  -- bound on the slope for t ∈ (0,1)
  have hbound : ∀ᶠ t in 𝓝[>] (0:ℝ),
      t⁻¹ • (g (0 + t) - g 0) ≤ ψ u - ψ y - (1 - t) * (σ / 2 * ‖v‖ ^ 2) := by
    have : Set.Ioo (0:ℝ) 1 ∈ 𝓝[>] (0:ℝ) := Ioo_mem_nhdsGT (by norm_num)
    filter_upwards [this] with t ht
    obtain ⟨ht0, ht1⟩ := ht
    have key := hψ.2 hu hy (le_of_lt ht0) (by linarith : (0:ℝ) ≤ 1 - t) (by ring)
    have hpt : t • u + (1 - t) • y = y + t • v := by
      rw [hv, smul_sub, sub_smul, one_smul]; abel
    rw [hpt] at key
    simp only [smul_eq_mul] at key
    have hg0 : g 0 = ψ y := by simp [hg]
    have hgt : g (0 + t) = ψ (y + t • v) := by simp [hg]
    rw [hg0, hgt, smul_eq_mul]
    rw [inv_mul_le_iff₀ ht0]
    have : ‖u - y‖ = ‖v‖ := rfl
    rw [this] at key
    nlinarith [key]
  have hlim : Tendsto (fun t : ℝ => ψ u - ψ y - (1 - t) * (σ / 2 * ‖v‖ ^ 2))
      (𝓝[>] (0:ℝ)) (𝓝 (ψ u - ψ y - (1 - 0) * (σ / 2 * ‖v‖ ^ 2))) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    exact ((continuous_const.sub ((continuous_const.sub continuous_id).mul
      continuous_const))).tendsto 0 |>.congr (fun _ => rfl)
  have := le_of_tendsto_of_tendsto hslope hlim hbound
  simpa using this

open BeckTeboulleMD.EMDA in
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (ψ : E → ℝ) (σ : ℝ) (hσ : 0 < σ) (hψ : StrongConvexOn X σ ψ) :
    ∀ u ∈ X, ∀ y ∈ X, DifferentiableAt ℝ ψ y → σ / 2 * ‖u - y‖ ^ 2 ≤ bregman ψ u y := by
  intro u hu y hy hd
  have := f3f6d117_key X ψ σ hψ u hu y hy hd
  unfold bregman
  linarith
