-- Prove2me | solution 1 for FoodDeliv.Decentral.lemma_C_8
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T10:52:12.548375+00:00
-- url     : https://prove2.me/submissions/1da83ab1-7dac-4d38-90b7-50f778f0b1c9

import Mathlib
import Definitions.Def_FoodDeliv_Decentral_Model

open Set FoodDeliv.Decentral

namespace G80FD

theorem cubic_anti {R μ ϕ : ℝ} (hR : 0 < R) (hμ : 0 < μ) (hϕ : 0 ≤ ϕ) :
    StrictAnti (chiCubic R μ ϕ) := by
  intro x y hxy
  unfold chiCubic
  have h1 : 0 < y ^ 2 + x * y + x ^ 2 := by
    nlinarith [sq_nonneg (x + y), sq_pos_of_pos (sub_pos.mpr hxy)]
  have h2 : 0 < (y - x) * (y ^ 2 + x * y + x ^ 2) := mul_pos (sub_pos.mpr hxy) h1
  nlinarith [mul_nonneg (mul_nonneg hμ.le hϕ) (sub_pos.mpr hxy).le]

/-- the root of the cubic in `[0, μ)` and the characterization of `chi` -/
theorem chi_spec {R μ ϕ : ℝ} (hR : 0 < R) (hμ : 0 < μ) (hϕ : 0 ≤ ϕ) (hϕR : ϕ < R * μ) :
    chi R μ ϕ ∈ Ico 0 μ ∧ chiCubic R μ ϕ (chi R μ ϕ) = 0 ∧
    {x | x ∈ Icc 0 μ ∧ chiCubic R μ ϕ x = 0} = {chi R μ ϕ} := by
  have hc : Continuous (chiCubic R μ ϕ) := by unfold chiCubic; fun_prop
  have h0 : 0 ≤ chiCubic R μ ϕ 0 := by unfold chiCubic; simp; positivity
  have hμv : chiCubic R μ ϕ μ < 0 := by
    unfold chiCubic; nlinarith [mul_pos hμ hμ, mul_lt_mul_of_pos_left hϕR (mul_pos hμ hμ)]
  obtain ⟨x0, hx0, hx0r⟩ : ∃ x0 ∈ Icc 0 μ, chiCubic R μ ϕ x0 = 0 :=
    intermediate_value_Icc' hμ.le hc.continuousOn ⟨hμv.le, h0⟩
  have hanti := cubic_anti hR hμ hϕ
  have hset : {x | x ∈ Icc 0 μ ∧ chiCubic R μ ϕ x = 0} = {x0} := by
    ext x
    simp only [mem_setOf_eq, mem_singleton_iff]
    constructor
    · rintro ⟨-, hx⟩
      exact hanti.injective (hx.trans hx0r.symm)
    · rintro rfl; exact ⟨hx0, hx0r⟩
  have hchi : chi R μ ϕ = x0 := by unfold chi; rw [hset, csInf_singleton]
  have hlt : x0 < μ := by
    rcases hx0.2.lt_or_eq with h | h
    · exact h
    · rw [h] at hx0r; linarith
  rw [hchi]
  exact ⟨⟨hx0.1, hlt⟩, hx0r, hset⟩

theorem cubic_pos_iff {R μ ϕ : ℝ} (hR : 0 < R) (hμ : 0 < μ) (hϕ : 0 ≤ ϕ) (hϕR : ϕ < R * μ)
    (x : ℝ) : 0 < chiCubic R μ ϕ x ↔ x < chi R μ ϕ := by
  obtain ⟨-, hr, -⟩ := chi_spec hR hμ hϕ hϕR
  have hanti := cubic_anti hR hμ hϕ
  constructor
  · intro h; by_contra h'; push_neg at h'
    have := hanti.antitone h'; linarith
  · intro h; rw [← hr]; exact hanti h

theorem cubic_neg_iff {R μ ϕ : ℝ} (hR : 0 < R) (hμ : 0 < μ) (hϕ : 0 ≤ ϕ) (hϕR : ϕ < R * μ)
    (x : ℝ) : chiCubic R μ ϕ x < 0 ↔ chi R μ ϕ < x := by
  obtain ⟨-, hr, -⟩ := chi_spec hR hμ hϕ hϕR
  have hanti := cubic_anti hR hμ hϕ
  constructor
  · intro h; by_contra h'; push_neg at h'
    have := hanti.antitone h'; linarith
  · intro h; rw [← hr]; exact hanti h

theorem chi_pos {R μ ϕ : ℝ} (hR : 0 < R) (hμ : 0 < μ) (hϕ : 0 < ϕ) (hϕR : ϕ < R * μ) :
    0 < chi R μ ϕ := by
  rw [← cubic_pos_iff hR hμ hϕ.le hϕR]; unfold chiCubic; simp; positivity

/-- the cubic identity `R χ³ = μ ϕ (2μ - χ)` -/
theorem chi_eq {R μ ϕ : ℝ} (hR : 0 < R) (hμ : 0 < μ) (hϕ : 0 ≤ ϕ) (hϕR : ϕ < R * μ) :
    R * chi R μ ϕ ^ 3 = μ * ϕ * (2 * μ - chi R μ ϕ) := by
  have := (chi_spec hR hμ hϕ hϕR).2.1
  unfold chiCubic at this; linarith

/-- the profit curve in the variable `s` -/
noncomputable def g (R μ ϕ s : ℝ) : ℝ := (R - μ * ϕ / s ^ 2) * (μ - s)

theorem g_deriv {R μ ϕ s : ℝ} (hs : s ≠ 0) :
    HasDerivAt (g R μ ϕ) (chiCubic R μ ϕ s / s ^ 3) s := by
  have h1 := (((hasDerivAt_pow 2 s).inv (pow_ne_zero 2 hs)).const_mul (μ * ϕ)).const_sub R
  have h2 := (hasDerivAt_id s).const_sub μ
  have hg : g R μ ϕ = fun s => (R - μ * ϕ * (fun x => x ^ 2)⁻¹ s) * (μ - id s) := by
    funext x; simp [g, div_eq_mul_inv]
  rw [hg]
  refine (h1.mul h2).congr_deriv ?_
  unfold chiCubic
  simp only [Pi.inv_apply, id]
  field_simp
  ring

theorem g_cont {R μ ϕ : ℝ} : ContinuousOn (g R μ ϕ) (Ioi 0) := by
  intro s hs
  exact (g_deriv (ne_of_gt hs)).continuousAt.continuousWithinAt

theorem g_mono {R μ ϕ : ℝ} (hR : 0 < R) (hμ : 0 < μ) (hϕ : 0 ≤ ϕ) (hϕR : ϕ < R * μ) :
    StrictMonoOn (g R μ ϕ) (Ioc 0 (chi R μ ϕ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioc 0 _)
  · exact g_cont.mono fun s hs => hs.1
  · intro s hs
    rw [interior_Ioc] at hs
    rw [(g_deriv (ne_of_gt hs.1)).deriv]
    exact div_pos ((cubic_pos_iff hR hμ hϕ hϕR s).mpr hs.2) (pow_pos hs.1 3)

theorem g_anti {R μ ϕ : ℝ} (hR : 0 < R) (hμ : 0 < μ) (hϕ : 0 < ϕ) (hϕR : ϕ < R * μ) :
    StrictAntiOn (g R μ ϕ) (Ici (chi R μ ϕ)) := by
  have hχ := chi_pos hR hμ hϕ hϕR
  apply strictAntiOn_of_deriv_neg (convex_Ici _)
  · exact g_cont.mono fun s hs => lt_of_lt_of_le hχ hs
  · intro s hs
    rw [interior_Ici] at hs
    have hs0 : 0 < s := lt_trans hχ hs
    rw [(g_deriv (ne_of_gt hs0)).deriv]
    exact div_neg_of_neg_of_pos ((cubic_neg_iff hR hμ hϕ.le hϕR s).mpr hs) (pow_pos hs0 3)

theorem g_chi {R μ ϕ : ℝ} (hR : 0 < R) (hμ : 0 < μ) (hϕ : 0 < ϕ) (hϕR : ϕ < R * μ) :
    g R μ ϕ (chi R μ ϕ) = 2 * R * (μ - chi R μ ϕ) ^ 2 / (2 * μ - chi R μ ϕ) := by
  have hχ := chi_pos hR hμ hϕ hϕR
  have hχμ := (chi_spec hR hμ hϕ.le hϕR).1.2
  have he := chi_eq hR hμ hϕ.le hϕR
  unfold g
  have h2 : 0 < 2 * μ - chi R μ ϕ := by linarith
  rw [eq_div_iff h2.ne']
  field_simp
  nlinarith [he]

/-- `μ ϕ / χ² = R χ / (2μ - χ)` -/
theorem chi_ratio {R μ ϕ : ℝ} (hR : 0 < R) (hμ : 0 < μ) (hϕ : 0 < ϕ) (hϕR : ϕ < R * μ) :
    μ * ϕ / chi R μ ϕ ^ 2 = R * chi R μ ϕ / (2 * μ - chi R μ ϕ) := by
  have hχ := chi_pos hR hμ hϕ hϕR
  have hχμ := (chi_spec hR hμ hϕ.le hϕR).1.2
  have he := chi_eq hR hμ hϕ.le hϕR
  have h2 : 0 < 2 * μ - chi R μ ϕ := by linarith
  rw [div_eq_div_iff (by positivity) h2.ne']
  nlinarith [he]

end G80FD

open Set FoodDeliv.Decentral

namespace G80FD

theorem dc_eq_g (R μ ϕ l : ℝ) : deliveryCurve R μ ϕ l = g R μ ϕ (μ - l) := by
  unfold deliveryCurve g; ring

theorem dc_cont (R μ ϕ : ℝ) : ContinuousOn (deliveryCurve R μ ϕ) (Iio μ) := by
  intro l hl
  have hne : (μ - l) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr (ne_of_gt hl))
  unfold deliveryCurve
  apply ContinuousAt.continuousWithinAt
  apply continuousAt_id.mul
  apply continuousAt_const.sub
  exact continuousAt_const.div (by fun_prop) hne

/-- threshold: `Rμϕ² + c²ϕ ≤ 2c³ ↔ ϕ ≤ th` -/
theorem th_iff {R μ c ϕ : ℝ} (hR : 0 < R) (hμ : 0 < μ) (hc : 0 < c) (hϕ : 0 < ϕ) :
    ϕ ≤ (Real.sqrt (c ^ 3 * (c + 8 * R * μ)) - c ^ 2) / (2 * R * μ) ↔
      R * μ * ϕ ^ 2 + c ^ 2 * ϕ ≤ 2 * c ^ 3 := by
  have hRμ : 0 < 2 * R * μ := by positivity
  have hsq : 0 ≤ c ^ 3 * (c + 8 * R * μ) := by positivity
  rw [le_div_iff₀ hRμ]
  have hL : 0 ≤ 2 * R * μ * ϕ + c ^ 2 := by positivity
  constructor
  · intro h
    have h1 : 2 * R * μ * ϕ + c ^ 2 ≤ Real.sqrt (c ^ 3 * (c + 8 * R * μ)) := by linarith
    have h2 := pow_le_pow_left₀ hL h1 2
    rw [Real.sq_sqrt hsq] at h2
    have h3 : 4 * (R * μ) * (R * μ * ϕ ^ 2 + c ^ 2 * ϕ - 2 * c ^ 3) ≤ 0 := by
      ring_nf; ring_nf at h2; linarith
    by_contra hcon; push_neg at hcon
    have := mul_pos (by positivity : (0:ℝ) < 4 * (R * μ)) (sub_pos.mpr hcon)
    linarith
  · intro h
    have h3 : (2 * R * μ * ϕ + c ^ 2) ^ 2 ≤ c ^ 3 * (c + 8 * R * μ) := by
      have : 4 * (R * μ) * (R * μ * ϕ ^ 2 + c ^ 2 * ϕ - 2 * c ^ 3) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
      ring_nf; ring_nf at this; linarith
    have := Real.le_sqrt_of_sq_le h3
    linarith

/-- `χ` versus `μϕ/c` -/
theorem cubic_at {R μ c ϕ : ℝ} (hc : 0 < c) :
    chiCubic R μ ϕ (μ * ϕ / c) = μ ^ 2 * ϕ / c ^ 3 * (2 * c ^ 3 - (R * μ * ϕ ^ 2 + c ^ 2 * ϕ)) := by
  unfold chiCubic; field_simp; ring

end G80FD

open G80FD in
set_option maxHeartbeats 1000000 in
theorem solution (R μ c ϕ : ℝ) (hμ : 0 < μ) (hc : 0 < c) (hcR : c < R * μ)
    (hϕ : 0 < ϕ) (hϕc : ϕ < c) :
    -- 1. `p (μ - c/(R-p))` and `p (μ - √(μϕ/(R-p)))`
    ((R - c ^ 2 / (μ * ϕ)) * (μ - c / (R - (R - c ^ 2 / (μ * ϕ)))) =
        μ * (R - c ^ 2 / (μ * ϕ)) * ((c - ϕ) / c) ∧
      (R - c ^ 2 / (μ * ϕ)) * (μ - Real.sqrt (μ * ϕ / (R - (R - c ^ 2 / (μ * ϕ))))) =
        μ * (R - c ^ 2 / (μ * ϕ)) * ((c - ϕ) / c) ∧
      ∀ p : ℝ, 0 < p → p < R →
        (p ≤ R - c ^ 2 / (μ * ϕ) →
          p * (μ - Real.sqrt (μ * ϕ / (R - p))) ≤ p * (μ - c / (R - p))) ∧
        (R - c ^ 2 / (μ * ϕ) < p →
          p * (μ - Real.sqrt (μ * ϕ / (R - p))) > p * (μ - c / (R - p)))) ∧
    -- 3. `p Λ1` and `p (μ - √(μϕ/(R-p)))`
    (∀ Λ1 ∈ Set.Ioo 0 μ,
      (R - μ * ϕ / (μ - Λ1) ^ 2) *
          (μ - Real.sqrt (μ * ϕ / (R - (R - μ * ϕ / (μ - Λ1) ^ 2)))) =
        Λ1 * (R - μ * ϕ / (μ - Λ1) ^ 2)) ∧
    -- 3. the curve `λ (R - μϕ/(μ-λ)²)` is unimodal on `(0, μ)`, with maximizer `λ2 = μ - χ`
    (lam2 R μ ϕ ∈ Set.Ioo 0 μ ∧
      StrictMonoOn (fun l => deliveryCurve R μ ϕ l) (Set.Ioc 0 (lam2 R μ ϕ)) ∧
      StrictAntiOn (fun l => deliveryCurve R μ ϕ l) (Set.Ico (lam2 R μ ϕ) μ) ∧
      deliveryCurve R μ ϕ (lam2 R μ ϕ) = 2 * R * (μ - chi R μ ϕ) ^ 2 / (2 * μ - chi R μ ϕ) ∧
      IsGreatest ((fun l => deliveryCurve R μ ϕ l) '' Set.Ioo 0 μ)
        (2 * R * (μ - chi R μ ϕ) ^ 2 / (2 * μ - chi R μ ϕ))) ∧
    -- 3. the two roots `λ1 ≤ λ'1` and `λ1 < λ2`
    ((Real.sqrt (R * μ) - Real.sqrt c) ^ 2 < 2 * R * (μ - chi R μ ϕ) ^ 2 / (2 * μ - chi R μ ϕ) →
      (∃ l' : ℝ, lam1 R μ c ϕ ≤ l' ∧
        {l : ℝ | l ∈ Set.Ioo 0 μ ∧
            deliveryCurve R μ ϕ l = (Real.sqrt (R * μ) - Real.sqrt c) ^ 2} =
          {lam1 R μ c ϕ, l'}) ∧
      lam1 R μ c ϕ < lam2 R μ ϕ) ∧
    -- 4. the three curves at `Λ1 = ((c - ϕ)/c) μ`, and the order of the thresholds
    ((c - ϕ) / c * μ * (R - c ^ 2 / (μ * ϕ)) = μ * (R - c ^ 2 / (μ * ϕ)) * ((c - ϕ) / c)) ∧
    (∀ Λ1 ∈ Set.Ioo 0 μ,
      (Λ1 ≤ (c - ϕ) / c * μ ↔ R - c / (μ - Λ1) ≤ R - μ * ϕ / (μ - Λ1) ^ 2) ∧
      (Λ1 ≥ (c - ϕ) / c * μ ↔ R - c / (μ - Λ1) ≥ R - μ * ϕ / (μ - Λ1) ^ 2)) ∧
    (ϕ ≤ (Real.sqrt (c ^ 3 * (c + 8 * R * μ)) - c ^ 2) / (2 * R * μ) →
      lam2 R μ ϕ ≤ (c - ϕ) / c * μ) ∧
    ((Real.sqrt (c ^ 3 * (c + 8 * R * μ)) - c ^ 2) / (2 * R * μ) < ϕ →
      lam2 R μ ϕ > (c - ϕ) / c * μ) := by
  have hR : 0 < R := by
    by_contra h; push_neg at h; nlinarith
  have hϕR : ϕ < R * μ := by linarith
  obtain ⟨⟨hχ0, hχμ⟩, hroot, -⟩ := chi_spec hR hμ hϕ.le hϕR
  have hχ := chi_pos hR hμ hϕ hϕR
  have hμϕ : 0 < μ * ϕ := mul_pos hμ hϕ
  have hl2 : lam2 R μ ϕ = μ - chi R μ ϕ := rfl
  set χ := chi R μ ϕ with hχdef
  set M := 2 * R * (μ - χ) ^ 2 / (2 * μ - χ) with hM
  set L2 := lam2 R μ ϕ with hL2
  have hdcL2 : deliveryCurve R μ ϕ L2 = M := by
    rw [dc_eq_g, hl2, sub_sub_cancel]; exact g_chi hR hμ hϕ hϕR
  have hL2mem : L2 ∈ Ioo 0 μ := ⟨by rw [hl2]; linarith, by rw [hl2]; linarith⟩
  have hdmono : StrictMonoOn (deliveryCurve R μ ϕ) (Ioc 0 L2) := by
    intro a ha b hb hab
    rw [dc_eq_g, dc_eq_g]
    have hga := g_anti hR hμ hϕ hϕR
    refine hga (show χ ≤ μ - b by rw [hl2] at hb; linarith [hb.2])
      (show χ ≤ μ - a by rw [hl2] at ha; linarith [ha.2]) (by linarith)
  have hdanti : StrictAntiOn (deliveryCurve R μ ϕ) (Ico L2 μ) := by
    intro a ha b hb hab
    rw [dc_eq_g, dc_eq_g]
    have hgm := g_mono hR hμ hϕ.le hϕR
    refine hgm ⟨by linarith [hb.2], ?_⟩ ⟨by linarith [ha.2], ?_⟩ (by linarith)
    · rw [hl2] at hb; linarith [hb.1]
    · rw [hl2] at ha; linarith [ha.1]
  have hdle : ∀ l ∈ Ioo 0 μ, deliveryCurve R μ ϕ l ≤ M := by
    intro l hl
    rw [← hdcL2]
    rcases le_total l L2 with h | h
    · exact hdmono.monotoneOn ⟨hl.1, h⟩ ⟨hL2mem.1, le_refl _⟩ h
    · exact hdanti.antitoneOn ⟨le_refl _, hL2mem.2⟩ ⟨h, hl.2⟩ h
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ⟨hL2mem, hdmono, hdanti, hdcL2, ⟨L2, hL2mem, hdcL2⟩, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · -- 1a
    have e : R - (R - c ^ 2 / (μ * ϕ)) = c ^ 2 / (μ * ϕ) := by ring
    rw [e]; field_simp
  · -- 1b
    have e : μ * ϕ / (R - (R - c ^ 2 / (μ * ϕ))) = (μ * ϕ / c) ^ 2 := by
      have : R - (R - c ^ 2 / (μ * ϕ)) = c ^ 2 / (μ * ϕ) := by ring
      rw [this]; field_simp
    rw [e, Real.sqrt_sq (by positivity)]; field_simp
  · intro p hp hpR
    have hRp : 0 < R - p := by linarith
    have key : c / (R - p) ≤ Real.sqrt (μ * ϕ / (R - p)) ↔ p ≤ R - c ^ 2 / (μ * ϕ) := by
      rw [Real.le_sqrt (by positivity) (by positivity), div_pow, div_le_div_iff₀ (by positivity) hRp,
        le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ hμϕ]
      constructor <;> intro h <;> nlinarith
    constructor
    · intro h
      have := key.mpr h
      have : p * (μ - Real.sqrt (μ * ϕ / (R - p))) ≤ p * (μ - c / (R - p)) :=
        mul_le_mul_of_nonneg_left (by linarith) hp.le
      exact this
    · intro h
      have h' : Real.sqrt (μ * ϕ / (R - p)) < c / (R - p) := by
        by_contra hc'; push_neg at hc'; have := key.mp hc'; linarith
      show p * (μ - c / (R - p)) < p * (μ - Real.sqrt (μ * ϕ / (R - p)))
      exact mul_lt_mul_of_pos_left (by linarith) hp
  · -- 3a
    intro Λ hΛ
    have hd : 0 < μ - Λ := by linarith [hΛ.2]
    have e : μ * ϕ / (R - (R - μ * ϕ / (μ - Λ) ^ 2)) = (μ - Λ) ^ 2 := by
      have : R - (R - μ * ϕ / (μ - Λ) ^ 2) = μ * ϕ / (μ - Λ) ^ 2 := by ring
      rw [this]; field_simp
    rw [e, Real.sqrt_sq hd.le]; ring
  · rintro y ⟨l, hl, rfl⟩; exact hdle l hl
  · -- 3c
    intro hT
    set T := (Real.sqrt (R * μ) - Real.sqrt c) ^ 2 with hTdef
    have hTpos : 0 < T := by
      have : Real.sqrt c < Real.sqrt (R * μ) := Real.sqrt_lt_sqrt hc.le hcR
      positivity
    have hdc0 : deliveryCurve R μ ϕ 0 = 0 := by unfold deliveryCurve; ring
    have hcont := dc_cont R μ ϕ
    -- first root
    obtain ⟨l1, hl1, hl1T⟩ : ∃ l1 ∈ Icc 0 L2, deliveryCurve R μ ϕ l1 = T :=
      intermediate_value_Icc hL2mem.1.le (hcont.mono fun x hx => lt_of_le_of_lt hx.2 hL2mem.2)
        ⟨by rw [hdc0]; exact hTpos.le, by rw [hdcL2]; exact hT.le⟩
    have hl1pos : 0 < l1 := by
      rcases hl1.1.lt_or_eq with h | h
      · exact h
      · rw [← h, hdc0] at hl1T; linarith
    have hl1lt : l1 < L2 := by
      rcases hl1.2.lt_or_eq with h | h
      · exact h
      · rw [h, hdcL2] at hl1T; linarith
    -- a point near μ with negative value
    set s1 := min (χ / 2) (Real.sqrt (μ * ϕ / (2 * R))) with hs1
    have hs1pos : 0 < s1 := lt_min (by linarith) (Real.sqrt_pos.mpr (by positivity))
    have hs1χ : s1 < χ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hs1sq : s1 ^ 2 ≤ μ * ϕ / (2 * R) := by
      have h := min_le_right (χ / 2) (Real.sqrt (μ * ϕ / (2 * R)))
      have := pow_le_pow_left₀ hs1pos.le h 2
      rwa [Real.sq_sqrt (by positivity)] at this
    set b := μ - s1 with hb
    have hbneg : deliveryCurve R μ ϕ b < T := by
      unfold deliveryCurve
      have e : μ - b = s1 := by rw [hb]; ring
      rw [e]
      have h1 : 2 * R ≤ μ * ϕ / s1 ^ 2 := by
        rw [le_div_iff₀ (by positivity)]
        rw [le_div_iff₀ (by positivity)] at hs1sq; linarith
      have hbpos : 0 < b := by rw [hb]; linarith
      have : b * (R - μ * ϕ / s1 ^ 2) < 0 := mul_neg_of_pos_of_neg hbpos (by linarith)
      linarith
    have hL2b : L2 < b := by rw [hb, hl2]; linarith
    have hbμ : b < μ := by rw [hb]; linarith
    obtain ⟨l', hl', hl'T⟩ : ∃ l' ∈ Icc L2 b, deliveryCurve R μ ϕ l' = T :=
      intermediate_value_Icc' hL2b.le (hcont.mono fun x hx => lt_of_le_of_lt hx.2 hbμ)
        ⟨hbneg.le, by rw [hdcL2]; exact hT.le⟩
    have hl'gt : L2 < l' := by
      rcases hl'.1.lt_or_eq with h | h
      · exact h
      · rw [← h, hdcL2] at hl'T; linarith
    have hl'μ : l' < μ := lt_of_le_of_lt hl'.2 hbμ
    have hset : {l : ℝ | l ∈ Ioo 0 μ ∧ deliveryCurve R μ ϕ l = T} = {l1, l'} := by
      ext l
      simp only [mem_setOf_eq, mem_insert_iff, mem_singleton_iff]
      constructor
      · rintro ⟨hl, hlT⟩
        rcases le_total l L2 with h | h
        · left
          exact hdmono.injOn ⟨hl.1, h⟩ ⟨hl1pos, hl1lt.le⟩ (hlT.trans hl1T.symm)
        · right
          exact hdanti.injOn ⟨h, hl.2⟩ ⟨hl'gt.le, hl'μ⟩ (hlT.trans hl'T.symm)
      · rintro (rfl | rfl)
        · exact ⟨⟨hl1pos, lt_trans hl1lt hL2mem.2⟩, hl1T⟩
        · exact ⟨⟨lt_trans hL2mem.1 hl'gt, hl'μ⟩, hl'T⟩
    have hlam1 : lam1 R μ c ϕ = l1 := by
      unfold lam1
      rw [← hTdef, hset, csInf_pair]
      exact min_eq_left (by linarith)
    refine ⟨⟨l', by rw [hlam1]; linarith, by rw [hlam1]; exact hset⟩, by rw [hlam1]; exact hl1lt⟩
  · -- 4a
    ring
  · -- 4b
    intro Λ hΛ
    have hd : 0 < μ - Λ := by linarith [hΛ.2]
    have key : (Λ ≤ (c - ϕ) / c * μ ↔ μ * ϕ / (μ - Λ) ^ 2 ≤ c / (μ - Λ)) := by
      rw [div_le_div_iff₀ (by positivity) hd]
      have e : (c - ϕ) / c * μ = μ - μ * ϕ / c := by field_simp
      rw [e, le_sub_comm, div_le_iff₀ hc]
      constructor
      · intro h; nlinarith [mul_le_mul_of_nonneg_left h hd.le]
      · intro h
        have : μ * ϕ * (μ - Λ) ≤ c * (μ - Λ) * (μ - Λ) := by nlinarith
        have := le_of_mul_le_mul_right this hd
        linarith
    have key' : (Λ ≥ (c - ϕ) / c * μ ↔ c / (μ - Λ) ≤ μ * ϕ / (μ - Λ) ^ 2) := by
      rw [div_le_div_iff₀ hd (by positivity)]
      have e : (c - ϕ) / c * μ = μ - μ * ϕ / c := by field_simp
      rw [ge_iff_le, e, sub_le_comm, le_div_iff₀ hc]
      constructor
      · intro h; nlinarith [mul_le_mul_of_nonneg_left h hd.le]
      · intro h
        have : c * (μ - Λ) * (μ - Λ) ≤ μ * ϕ * (μ - Λ) := by nlinarith
        have := le_of_mul_le_mul_right this hd
        linarith
    constructor
    · rw [key]; constructor <;> intro h <;> linarith
    · rw [key']; constructor <;> intro h <;> linarith
  · -- 4c
    intro hth
    rw [th_iff hR hμ hc hϕ] at hth
    rw [hl2]
    have h1 : 0 ≤ chiCubic R μ ϕ (μ * ϕ / c) := by
      rw [cubic_at hc]; apply mul_nonneg (by positivity); linarith
    have h2 : μ * ϕ / c ≤ χ := by
      by_contra hcon; push_neg at hcon
      have := (cubic_neg_iff hR hμ hϕ.le hϕR _).mpr hcon; linarith
    have e : (c - ϕ) / c * μ = μ - μ * ϕ / c := by field_simp
    rw [e]; linarith
  · -- 4d
    intro hth
    have hth' : ¬ (ϕ ≤ (Real.sqrt (c ^ 3 * (c + 8 * R * μ)) - c ^ 2) / (2 * R * μ)) := not_le.mpr hth
    rw [th_iff hR hμ hc hϕ] at hth'
    push_neg at hth'
    rw [hl2]
    have h1 : chiCubic R μ ϕ (μ * ϕ / c) < 0 := by
      rw [cubic_at hc]; apply mul_neg_of_pos_of_neg (by positivity); linarith
    have h2 : χ < μ * ϕ / c := (cubic_neg_iff hR hμ hϕ.le hϕR _).mp h1
    have e : (c - ϕ) / c * μ = μ - μ * ϕ / c := by field_simp
    show μ - χ > (c - ϕ) / c * μ
    rw [e]; linarith
