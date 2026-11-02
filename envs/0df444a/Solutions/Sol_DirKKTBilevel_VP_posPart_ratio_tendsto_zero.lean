-- Prove2me | solution 1 for DirKKTBilevel.VP.posPart_ratio_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-02T00:53:39.389189+00:00
-- url     : https://prove2.me/submissions/1c4584fa-a408-4562-9b5e-a5239b2e33c1

import Mathlib
import Definitions.Def_DirKKTBilevel_VP_Model

open Filter Topology
open NonconvexSplitting.Shared SetConstrSOC.Directional
open DirKKTBilevel.VP

theorem solution {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    {q : ℕ} (obj : X → ℝ) (con : X → E q) (z u : X) (d : E q)
    (hfeas : ∀ j, con z j ≤ 0) (hdir : HasDirDerivAt con z u d)
    (hcrit : criticalCone obj con z u d) :
    Tendsto (fun t : ℝ => ‖posPart (con (z + t • u))‖ / t) (𝓝[>] 0) (𝓝 0) := by
  -- componentwise convergence of the difference quotients
  have hcomp : ∀ j, Tendsto (fun t : ℝ => t⁻¹ * (con (z + t • u) j - con z j)) (𝓝[>] 0)
      (𝓝 (d j)) := by
    intro j
    have := ((PiLp.proj (p := 2) (𝕜 := ℝ) (fun _ : Fin q => ℝ) j).continuous.tendsto d).comp hdir
    simpa [Function.comp_def] using this
  -- each component of `t⁻¹ • posPart (con (z + t u))` tends to `0`
  have hj : ∀ j, Tendsto (fun t : ℝ => t⁻¹ * max (con (z + t • u) j) 0) (𝓝[>] 0) (𝓝 0) := by
    intro j
    rcases (hfeas j).lt_or_eq with hlt | heq
    · -- inactive constraint: eventually negative
      have hcont : Tendsto (fun t : ℝ => con (z + t • u) j) (𝓝[>] 0) (𝓝 (con z j)) := by
        have h1 : Tendsto (fun t : ℝ => t * (t⁻¹ * (con (z + t • u) j - con z j)))
            (𝓝[>] 0) (𝓝 (0 * d j)) :=
          (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).mul (hcomp j)
        have h2 : ∀ᶠ t in 𝓝[>] (0:ℝ), t * (t⁻¹ * (con (z + t • u) j - con z j)) + con z j
            = con (z + t • u) j := by
          filter_upwards [self_mem_nhdsWithin] with t ht
          have : t ≠ 0 := ne_of_gt ht
          field_simp
          ring
        have := h1.add_const (con z j)
        rw [zero_mul, zero_add] at this
        exact this.congr' h2
      have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), con (z + t • u) j < 0 :=
        hcont.eventually (gt_mem_nhds hlt)
      apply tendsto_const_nhds.congr'
      filter_upwards [hev] with t ht
      rw [max_eq_right ht.le, mul_zero]
    · -- active constraint
      have hd : d j ≤ 0 := hcrit.1 j heq
      have hlim : Tendsto (fun t : ℝ => max (t⁻¹ * (con (z + t • u) j - con z j)) 0)
          (𝓝[>] 0) (𝓝 (max (d j) 0)) :=
        (hcomp j).max tendsto_const_nhds
      rw [max_eq_right hd] at hlim
      apply hlim.congr'
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : (0:ℝ) < t := ht
      rw [heq, sub_zero]
      rw [mul_max_of_nonneg _ _ (inv_nonneg.mpr ht'.le), mul_zero]
  -- assemble
  have hvec : Tendsto (fun t : ℝ => t⁻¹ • posPart (con (z + t • u))) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun t : ℝ => WithLp.toLp 2 (fun j => t⁻¹ * max (con (z + t • u) j) 0))
        (𝓝[>] 0) (𝓝 (WithLp.toLp 2 (fun _ : Fin q => (0:ℝ)))) := by
      apply (PiLp.continuous_toLp 2 (fun _ : Fin q => ℝ)).continuousAt.tendsto.comp
      exact tendsto_pi_nhds.mpr hj
    convert this using 1
    · funext t
      ext j
      simp only [PiLp.smul_apply, smul_eq_mul]
      rfl
    · congr 1
  have hn := (continuous_norm.tendsto (0 : E q)).comp hvec
  rw [norm_zero] at hn
  apply hn.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : (0:ℝ) < t := ht
  simp only [Function.comp_apply, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht']
  rw [div_eq_inv_mul]
