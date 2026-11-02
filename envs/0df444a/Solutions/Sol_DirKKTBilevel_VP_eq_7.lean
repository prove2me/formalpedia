-- Prove2me | solution 1 for DirKKTBilevel.VP.eq_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-02T00:54:45.008866+00:00
-- url     : https://prove2.me/submissions/dfe33182-4ae8-4593-88a5-0dda13552398

import Mathlib
import Definitions.Def_DirKKTBilevel_VP_Model

open Filter Topology
open NonconvexSplitting.Shared SetConstrSOC.Directional
open DirKKTBilevel.VP

theorem posPart_ratio_aux {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
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


theorem solution {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    {q : ℕ} (obj : X → ℝ) (con : X → E q) (z u : X) (d : E q) (ε δ ρ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hρ : 0 < ρ)
    (hobj : ContDiffAt ℝ 1 obj z) (hfeas : ∀ j, con z j ≤ 0) (hdir : HasDirDerivAt con z u d)
    (hcrit : criticalCone obj con z u d) (hcalm : IsCalmDirWith obj con z u ε δ ρ) :
    Tendsto (fun t : ℝ => (obj (z + t • u) + ρ * ‖posPart (con (z + t • u))‖ - obj z) / t)
      (𝓝[>] 0) (𝓝 0) := by
  have hpos := posPart_ratio_aux obj con z u d hfeas hdir hcrit
  -- derivative of `obj` along the ray
  have hD : HasFDerivAt obj (fderiv ℝ obj z) z :=
    (hobj.differentiableAt (by norm_num)).hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ => z + t • u) u 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const u).const_add z
  have hcomp : HasDerivAt (fun t : ℝ => obj (z + t • u)) (fderiv ℝ obj z u) 0 := by
    have hD' : HasFDerivAt obj (fderiv ℝ obj z) (z + (0:ℝ) • u) := by simpa using hD
    have := hD'.comp_hasDerivAt (0:ℝ) hline
    simpa [Function.comp_def] using this
  have hslope : Tendsto (fun t : ℝ => (obj (z + t • u) - obj z) / t) (𝓝[>] 0)
      (𝓝 (fderiv ℝ obj z u)) := by
    have := (hasDerivAt_iff_tendsto_slope.mp hcomp).mono_left
      (nhdsGT_le_nhdsNE (0:ℝ))
    apply this.congr'
    filter_upwards with t
    simp [slope_def_field]
  have hsum : Tendsto (fun t : ℝ => (obj (z + t • u) + ρ * ‖posPart (con (z + t • u))‖ - obj z) / t)
      (𝓝[>] 0) (𝓝 (fderiv ℝ obj z u)) := by
    have := hslope.add (hpos.const_mul ρ)
    rw [mul_zero, add_zero] at this
    apply this.congr'
    filter_upwards with t
    ring
  -- lower bound from calmness
  have hnorm0 : Tendsto (fun t : ℝ => ‖posPart (con (z + t • u))‖) (𝓝[>] 0) (𝓝 0) := by
    have h1 := (tendsto_nhdsWithin_of_tendsto_nhds (tendsto_id (x := 𝓝 (0:ℝ)))).mul hpos
    rw [mul_zero] at h1
    apply h1.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have : t ≠ 0 := ne_of_gt ht
    simp only [id]
    field_simp
  have hsmall : ∀ᶠ t in 𝓝[>] (0:ℝ), ‖posPart (con (z + t • u))‖ < ε :=
    hnorm0.eventually (gt_mem_nhds hε)
  have hsmall2 : ∀ᶠ t in 𝓝[>] (0:ℝ), t * ‖u‖ < ε := by
    have : Tendsto (fun t : ℝ => t * ‖u‖) (𝓝[>] 0) (𝓝 (0 * ‖u‖)) :=
      (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).mul tendsto_const_nhds
    rw [zero_mul] at this
    exact this.eventually (gt_mem_nhds hε)
  have hge : ∀ᶠ t in 𝓝[>] (0:ℝ),
      0 ≤ (obj (z + t • u) + ρ * ‖posPart (con (z + t • u))‖ - obj z) / t := by
    filter_upwards [hsmall, hsmall2, self_mem_nhdsWithin] with t h1 h2 ht
    have ht' : (0:ℝ) < t := ht
    apply div_nonneg _ ht'.le
    have hmem : (z + t • u) - z ∈ dirNbhd ε δ u := by
      rw [add_sub_cancel_left]
      refine ⟨?_, ?_⟩
      · rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht']; exact h2
      · rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht', smul_smul, mul_comm, sub_self,
          norm_zero]
        positivity
    have := hcalm (-posPart (con (z + t • u))) (by rwa [norm_neg]) (z + t • u) hmem (by
      intro j
      show con (z + t • u) j + (-(posPart (con (z + t • u)))) j ≤ 0
      simp only [PiLp.neg_apply]
      show con (z + t • u) j + -(max (con (z + t • u) j) 0) ≤ 0
      have := le_max_left (con (z + t • u) j) 0
      linarith)
    rw [norm_neg] at this
    linarith
  have hle : 0 ≤ fderiv ℝ obj z u := ge_of_tendsto hsum hge
  have hzero : fderiv ℝ obj z u = 0 := le_antisymm hcrit.2 hle
  rw [hzero] at hsum
  exact hsum
