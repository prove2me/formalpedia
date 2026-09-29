-- Prove2me | solution 1 for DeBruijnNewman.debruijn_newman_constant_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @adobner
-- created : 2026-09-24T21:42:14.001325+00:00
-- url     : https://prove2.me/submissions/f839a91a-4be0-46a4-a431-884be320b6e1

import Theorems.Thm_DeBruijnNewman_Dobner_zeta_zero_disk
import Theorems.Thm_DeBruijnNewman_Dobner_zeta_almost_periodic
import Theorems.Thm_DeBruijnNewman_Dobner_normalized_approximation

open Set Metric DeBruijnNewman DeBruijnNewman.Dobner

/-!
Dobner's argument, specialized to zeta. The three imported open lemmas are
the analytic inputs from arXiv:2005.05142. Everything below, including
persistence of a zero, the logarithmic drift, and the infimum argument, is
proved.

For persistence we use the minimum modulus principle, a consequence of
the maximum modulus principle already in Mathlib. It gives the
zero-existence part of the paper's Rouché argument; no multiplicity count
is needed. Choosing each error smaller than δ/4 makes this sufficient.
-/

private theorem exists_zero_of_center_norm_lt_on_sphere
    {g : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hg : DifferentiableOn ℂ g (closedBall c r))
    (hboundary : ∀ z ∈ sphere c r, ‖g c‖ < ‖g z‖) :
    ∃ z ∈ ball c r, g z = 0 := by
  by_contra h
  push Not at h
  have hc : c ∈ ball c r := mem_ball_self hr
  have hclosed : ∀ z ∈ closedBall c r, g z ≠ 0 := by
    intro z hz
    rcases lt_or_eq_of_le (mem_closedBall.mp hz) with hi | he
    · exact h z (mem_ball.mpr hi)
    · exact norm_pos_iff.mp
        ((norm_nonneg (g c)).trans_lt (hboundary z (mem_sphere.mpr he)))
  have hinv : DifferentiableOn ℂ (fun z => (g z)⁻¹) (closedBall c r) :=
    hg.inv hclosed
  obtain ⟨w, hw, hmax⟩ := Complex.exists_mem_frontier_isMaxOn_norm
    isBounded_ball ⟨c, hc⟩
    (hinv.mono closure_ball_subset_closedBall).diffContOnCl
  have hws : w ∈ sphere c r := by simpa only [frontier_ball c hr.ne'] using hw
  have hle : ‖(g c)⁻¹‖ ≤ ‖(g w)⁻¹‖ := hmax (subset_closure hc)
  have hlt : ‖(g w)⁻¹‖ < ‖(g c)⁻¹‖ := by
    simp only [norm_inv]
    exact (inv_lt_inv₀
      (norm_pos_iff.mpr (hclosed w (sphere_subset_closedBall hws)))
      (norm_pos_iff.mpr (hclosed c (ball_subset_closedBall hc)))).2 (hboundary w hws)
  exact (not_lt_of_ge hle) hlt

private theorem gammaT_ne_zero_of_im_pos (t : ℝ) (s : ℂ) (hs : 0 < s.im) :
    gammaT t s ≠ 0 := by
  have hs0 : s ≠ 0 := by
    intro h
    simp [h] at hs
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have he : s = 1 := sub_eq_zero.mp h
    simp [he] at hs
  have hGamma : Complex.Gamma (s / 2) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n hn
    have hi := congrArg Complex.im hn
    norm_num at hi
    linarith
  unfold gammaT gammaFactor
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero (div_ne_zero (mul_ne_zero hs0 hs1) (by norm_num))
        (Complex.exp_ne_zero _))
      hGamma)
    (Complex.exp_ne_zero _)

/-- Every fixed strip is eventually mapped strictly to the right of the
critical line. The bound is explicit, and only uses `t < 0`. -/
private theorem J_eventually_right (t : ℝ) (ht : t < 0) (a : ℝ) :
    ∃ Y : ℝ, 0 < Y ∧ ∀ s : ℂ, a ≤ s.re → Y ≤ s.im → 1 / 2 < (J t s).re := by
  let k : ℝ := |t| / 4
  have hk : 0 < k := div_pos (abs_pos.mpr (ne_of_lt ht)) (by norm_num)
  have hpi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  refine ⟨2 * Real.pi * Real.exp ((1 - a) / k), mul_pos hpi (Real.exp_pos _), ?_⟩
  intro s hs hy
  have hn : Real.exp ((1 - a) / k) ≤ ‖s / ((2 * Real.pi : ℝ) : ℂ)‖ := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi]
    apply (le_div_iff₀ hpi).mpr
    calc
      Real.exp ((1 - a) / k) * (2 * Real.pi)
          = 2 * Real.pi * Real.exp ((1 - a) / k) := mul_comm _ _
      _ ≤ s.im := hy
      _ ≤ ‖s‖ := Complex.im_le_norm s
  have hl := Real.log_le_log (Real.exp_pos ((1 - a) / k)) hn
  rw [Real.log_exp] at hl
  have hm := mul_le_mul_of_nonneg_left hl hk.le
  have hc : k * ((1 - a) / k) = 1 - a := by
    field_simp
  have hJ : (J t s).re =
      s.re + k * Real.log ‖s / ((2 * Real.pi : ℝ) : ℂ)‖ := by
    simp [J, k, Complex.log_re]
  rw [hJ]
  linarith

private theorem negative_time_has_nonreal_zero (t : ℝ) (ht : t < 0) :
    ∃ z : ℂ, H t z = 0 ∧ z.im ≠ 0 := by
  obtain ⟨c, r, δ, hr, hδ, hc, hcircle⟩ := zeta_zero_disk t ht
  obtain ⟨hhol, happ⟩ := normalized_approximation t ht
  have hab : c.re - r < c.re + r := by linarith
  have hε : 0 < δ / 4 := by positivity
  obtain ⟨Y, hY⟩ := happ (c.re - r) (c.re + r) hab (δ / 4) hε
  obtain ⟨R, hR, hright⟩ := J_eventually_right t ht (c.re - r)
  obtain ⟨τ, hτ, hperiod⟩ := zeta_almost_periodic t ht
    (c.re - r) (c.re + r) hab (δ / 4) hε
    (max Y R - c.im + r)
  let shift : ℂ → ℂ := fun s => s + (τ : ℂ) * Complex.I
  have hcoords (s : ℂ) (hs : s ∈ closedBall c r) :
      c.re - r ≤ s.re ∧ s.re ≤ c.re + r ∧ c.im - r ≤ s.im := by
    have hn : ‖s - c‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm] using hs
    have hre := (Complex.abs_re_le_norm (s - c)).trans hn
    have him := (Complex.abs_im_le_norm (s - c)).trans hn
    simp only [Complex.sub_re, Complex.sub_im, abs_le] at hre him
    constructor
    · linarith [hre.1]
    constructor
    · linarith [hre.2]
    · linarith [him.1]
  have hshift_re (s : ℂ) : (shift s).re = s.re := by simp [shift]
  have hshift_im (s : ℂ) : (shift s).im = s.im + τ := by simp [shift]
  have hheight (s : ℂ) (hs : s ∈ closedBall c r) :
      Y ≤ (shift s).im ∧ R ≤ (shift s).im := by
    have hlow := (hcoords s hs).2.2
    have hy := le_max_left Y R
    have hr' := le_max_right Y R
    rw [hshift_im]
    constructor <;> linarith
  have hupper (s : ℂ) (hs : s ∈ closedBall c r) : 0 < (shift s).im :=
    hR.trans_le (hheight s hs).2
  have hclose (s : ℂ) (hs : s ∈ closedBall c r) :
      ‖normalizedXi t (shift s) - zetaT t s‖ < δ / 2 := by
    have hb := hcoords s hs
    have he1 := hY (shift s) (by simpa only [hshift_re] using hb.1)
      (by simpa only [hshift_re] using hb.2.1) (hheight s hs).1
    have he2 := hperiod s hb.1 hb.2.1
    change ‖zetaT t (shift s) - zetaT t s‖ < δ / 4 at he2
    calc
      ‖normalizedXi t (shift s) - zetaT t s‖
          ≤ ‖normalizedXi t (shift s) - zetaT t (shift s)‖
            + ‖zetaT t (shift s) - zetaT t s‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < δ / 2 := by linarith
  have hdiff : DifferentiableOn ℂ (fun s => normalizedXi t (shift s)) (closedBall c r) := by
    exact hhol.comp (differentiable_id.add_const ((τ : ℂ) * Complex.I)).differentiableOn
      (fun s hs => hupper s hs)
  have hcenter : ‖normalizedXi t (shift c)‖ < δ / 2 := by
    simpa only [hc, sub_zero] using hclose c (mem_closedBall_self hr.le)
  have hboundary : ∀ s ∈ sphere c r,
      ‖normalizedXi t (shift c)‖ < ‖normalizedXi t (shift s)‖ := by
    intro s hs
    have he := hclose s (sphere_subset_closedBall hs)
    have hf := hcircle s hs
    have hn : ‖zetaT t s‖ ≤
        ‖normalizedXi t (shift s) - zetaT t s‖ + ‖normalizedXi t (shift s)‖ := by
      calc
        ‖zetaT t s‖ ≤ ‖zetaT t s - normalizedXi t (shift s)‖
            + ‖normalizedXi t (shift s)‖ := norm_le_norm_sub_add _ _
        _ = _ := by rw [norm_sub_rev]
    linarith
  obtain ⟨w, hw, hzero⟩ := exists_zero_of_center_norm_lt_on_sphere hr hdiff hboundary
  have hwc := ball_subset_closedBall hw
  have hgamma := gammaT_ne_zero_of_im_pos t (shift w) (hupper w hwc)
  have hxi : xiT t (J t (shift w)) = 0 :=
    (div_eq_zero_iff.mp hzero).resolve_right hgamma
  have hH : H t (-Complex.I * (2 * J t (shift w) - 1)) = 0 := by
    exact (mul_eq_zero.mp hxi).resolve_left (by norm_num)
  have hright' : 1 / 2 < (J t (shift w)).re :=
    hright (shift w) (by simpa only [hshift_re] using (hcoords w hwc).1)
      (hheight w hwc).2
  refine ⟨-Complex.I * (2 * J t (shift w) - 1), hH, ?_⟩
  have him (s : ℂ) : (-Complex.I * (2 * s - 1)).im = 1 - 2 * s.re := by
    simp
  rw [him]
  linarith

theorem solution :
    0 ≤ DeBruijnNewman.Lambda ∧
      ∀ t : ℝ, DeBruijnNewman.HasOnlyRealZeros t → 0 ≤ t := by
  have hadmissible : ∀ t : ℝ, HasOnlyRealZeros t → 0 ≤ t := by
    intro t ht
    by_contra h
    obtain ⟨z, hz, him⟩ := negative_time_has_nonreal_zero t (lt_of_not_ge h)
    exact him (ht z hz)
  refine ⟨?_, hadmissible⟩
  unfold Lambda
  by_cases hnonempty : {t : ℝ | HasOnlyRealZeros t}.Nonempty
  · exact le_csInf hnonempty (fun t ht => hadmissible t ht)
  · rw [Set.not_nonempty_iff_eq_empty.mp hnonempty, Real.sInf_empty]
