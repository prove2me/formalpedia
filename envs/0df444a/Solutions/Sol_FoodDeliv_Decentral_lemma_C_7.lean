-- Prove2me | solution 1 for FoodDeliv.Decentral.lemma_C_7
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T10:49:04.061966+00:00
-- url     : https://prove2.me/submissions/1bc53808-9127-4511-b0b9-9290c1976cd2

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

/-- the profit curve `f(p) = g(s(p))` with `s(p) = √(μϕ/(R-p))` -/
theorem f_eq_g {R μ ϕ p : ℝ} (hμ : 0 < μ) (hϕ : 0 < ϕ) (hp : p < R) :
    p * (μ - Real.sqrt (μ * ϕ / (R - p))) = g R μ ϕ (Real.sqrt (μ * ϕ / (R - p))) := by
  unfold g
  have hpos : 0 < μ * ϕ / (R - p) := div_pos (mul_pos hμ hϕ) (by linarith)
  rw [Real.sq_sqrt hpos.le]
  congr 1
  field_simp
  ring

theorem s_mono {R μ ϕ : ℝ} (hμ : 0 < μ) (hϕ : 0 < ϕ) {p q : ℝ} (hpq : p < q) (hq : q < R) :
    Real.sqrt (μ * ϕ / (R - p)) < Real.sqrt (μ * ϕ / (R - q)) := by
  apply Real.sqrt_lt_sqrt (div_pos (mul_pos hμ hϕ) (by linarith)).le
  exact div_lt_div_of_pos_left (mul_pos hμ hϕ) (by linarith) (by linarith)

theorem s_pos {R μ ϕ p : ℝ} (hμ : 0 < μ) (hϕ : 0 < ϕ) (hp : p < R) :
    0 < Real.sqrt (μ * ϕ / (R - p)) :=
  Real.sqrt_pos.mpr (div_pos (mul_pos hμ hϕ) (by linarith))

end G80FD

open G80FD in
set_option maxHeartbeats 1000000 in
theorem solution (R μ c ϕ : ℝ) (hμ : 0 < μ) (hc : 0 < c) (hcR : c < R * μ)
    (hϕ : 0 < ϕ) (hϕc : ϕ < c) :
    -- 1. the zero at `p = R - ϕ/μ`
    (R - ϕ / μ) * (μ - Real.sqrt (μ * ϕ / (R - (R - ϕ / μ)))) = 0 ∧
    -- 2. `χ` is the unique root in `[0, μ]`
    (chi R μ ϕ ∈ Set.Icc 0 μ ∧ chiCubic R μ ϕ (chi R μ ϕ) = 0 ∧
      ∀ x ∈ Set.Icc 0 μ, chiCubic R μ ϕ x = 0 → x = chi R μ ϕ) ∧
    -- 2. unimodal on `(0, R - ϕ/μ]`, with its maximum and unique maximizer
    (∃ m ∈ Set.Ioc 0 (R - ϕ / μ),
      StrictMonoOn (fun p => p * (μ - Real.sqrt (μ * ϕ / (R - p)))) (Set.Ioc 0 m) ∧
      StrictAntiOn (fun p => p * (μ - Real.sqrt (μ * ϕ / (R - p))))
        (Set.Icc m (R - ϕ / μ))) ∧
    IsGreatest ((fun p => p * (μ - Real.sqrt (μ * ϕ / (R - p)))) '' Set.Ioc 0 (R - ϕ / μ))
      (2 * R * (μ - chi R μ ϕ) ^ 2 / (2 * μ - chi R μ ϕ)) ∧
    {p ∈ Set.Ioc 0 (R - ϕ / μ) | ∀ q ∈ Set.Ioc 0 (R - ϕ / μ),
        q * (μ - Real.sqrt (μ * ϕ / (R - q))) ≤ p * (μ - Real.sqrt (μ * ϕ / (R - p)))} =
      {2 * R * (μ - chi R μ ϕ) / (2 * μ - chi R μ ϕ)} ∧
    -- 2. `χ` increases in `ϕ`, and the maximum decreases with `ϕ`
    StrictMonoOn (fun φ => chi R μ φ) (Set.Ico 0 c) ∧
    StrictAntiOn (fun φ => 2 * R * (μ - chi R μ φ) ^ 2 / (2 * μ - chi R μ φ)) (Set.Ico 0 c) ∧
    -- 4. comparison of the two maximizers
    (ϕ ≤ (Real.sqrt (c ^ 3 * (c + 8 * R * μ)) - c ^ 2) / (2 * R * μ) →
      2 * R * (μ - chi R μ ϕ) / (2 * μ - chi R μ ϕ) > R - Real.sqrt (c / μ * R)) := by
  have hR : 0 < R := by
    by_contra h; push_neg at h; nlinarith
  have hϕR : ϕ < R * μ := by linarith
  obtain ⟨⟨hχ0, hχμ⟩, hroot, hset⟩ := chi_spec hR hμ hϕ.le hϕR
  have hχ := chi_pos hR hμ hϕ hϕR
  set χ := chi R μ ϕ with hχdef
  set f : ℝ → ℝ := fun p => p * (μ - Real.sqrt (μ * ϕ / (R - p))) with hf
  set pmax := R - ϕ / μ with hpmax
  set ps := 2 * R * (μ - χ) / (2 * μ - χ) with hps
  set M := 2 * R * (μ - χ) ^ 2 / (2 * μ - χ) with hM
  have h2 : 0 < 2 * μ - χ := by linarith
  have hpmaxR : pmax < R := by simp only [hpmax]; have := div_pos hϕ hμ; linarith
  -- R - ps = μϕ/χ²
  have hRps : R - ps = μ * ϕ / χ ^ 2 := by
    have hr : μ * ϕ / χ ^ 2 = R * χ / (2 * μ - χ) := chi_ratio hR hμ hϕ hϕR
    rw [hr, hps]; field_simp; ring
  have hps_pos : 0 < ps := by simp only [hps]; apply div_pos _ h2; nlinarith
  have hps_le : ps < pmax := by
    have e : pmax - ps = μ * ϕ / χ ^ 2 - ϕ / μ := by simp only [hpmax]; linarith [hRps]
    have : ϕ / μ < μ * ϕ / χ ^ 2 := by
      rw [div_lt_div_iff₀ hμ (by positivity)]
      nlinarith [mul_pos hϕ (mul_pos (sub_pos.mpr hχμ) (by linarith : 0 < μ + χ))]
    linarith
  have hpsR : ps < R := lt_trans hps_le hpmaxR
  have hs_ps : Real.sqrt (μ * ϕ / (R - ps)) = χ := by
    have : μ * ϕ / (μ * ϕ / χ ^ 2) = χ ^ 2 := by field_simp
    rw [hRps, this, Real.sqrt_sq hχ.le]
  have hs_pmax : Real.sqrt (μ * ϕ / (R - pmax)) = μ := by
    have : R - pmax = ϕ / μ := by simp only [hpmax]; ring
    have h' : μ * ϕ / (ϕ / μ) = μ ^ 2 := by field_simp
    rw [this, h', Real.sqrt_sq hμ.le]
  have hfg : ∀ p, p < R → f p = g R μ ϕ (Real.sqrt (μ * ϕ / (R - p))) := fun p hp =>
    f_eq_g hμ hϕ hp
  have hfps : f ps = M := by
    rw [hfg ps hpsR, hs_ps, g_chi hR hμ hϕ hϕR]
  have hle_chi : ∀ x ∈ Ioc 0 ps, Real.sqrt (μ * ϕ / (R - x)) ≤ χ := by
    intro x hx
    rw [← hs_ps]; rcases hx.2.lt_or_eq with h | h
    · exact (s_mono hμ hϕ h hpsR).le
    · rw [h]
  have hmono : StrictMonoOn f (Ioc 0 ps) := by
    intro p hp q hq hpq
    have hqR : q < R := lt_of_le_of_lt hq.2 hpsR
    rw [hfg p (lt_trans hpq hqR), hfg q hqR]
    exact g_mono hR hμ hϕ.le hϕR ⟨s_pos hμ hϕ (lt_trans hpq hqR), hle_chi p hp⟩
      ⟨s_pos hμ hϕ hqR, hle_chi q hq⟩ (s_mono hμ hϕ hpq hqR)
  have hanti : StrictAntiOn f (Icc ps pmax) := by
    intro p hp q hq hpq
    have hqR : q < R := lt_of_le_of_lt hq.2 hpmaxR
    have hpR : p < R := lt_trans hpq hqR
    rw [hfg p hpR, hfg q hqR]
    have hge : ∀ x ∈ Icc ps pmax, χ ≤ Real.sqrt (μ * ϕ / (R - x)) := by
      intro x hx
      rw [← hs_ps]; rcases hx.1.lt_or_eq with h | h
      · exact (s_mono hμ hϕ h (lt_of_le_of_lt hx.2 hpmaxR)).le
      · rw [h]
    exact g_anti hR hμ hϕ hϕR (hge p hp) (hge q hq) (s_mono hμ hϕ hpq hqR)
  have hle : ∀ p ∈ Ioc 0 pmax, f p ≤ M := by
    intro p hp
    rw [← hfps]
    rcases le_total p ps with h | h
    · exact hmono.monotoneOn ⟨hp.1, h⟩ ⟨hps_pos, le_refl _⟩ h
    · exact hanti.antitoneOn ⟨le_refl _, hps_le.le⟩ ⟨h, hp.2⟩ h
  refine ⟨?_, ⟨⟨hχ0, hχμ.le⟩, hroot, fun x hx hx0 => ?_⟩, ⟨ps, ⟨hps_pos, hps_le.le⟩, hmono, hanti⟩,
    ⟨⟨ps, ⟨hps_pos, hps_le.le⟩, hfps⟩, ?_⟩, ?_, ?_, ?_, ?_⟩
  · -- part 1
    have : R - (R - ϕ / μ) = ϕ / μ := by ring
    have h' : μ * ϕ / (ϕ / μ) = μ ^ 2 := by field_simp
    rw [this, h', Real.sqrt_sq hμ.le, sub_self, mul_zero]
  · have : x ∈ {x | x ∈ Icc 0 μ ∧ chiCubic R μ ϕ x = 0} := ⟨hx, hx0⟩
    rw [hset] at this; exact this
  · rintro y ⟨p, hp, rfl⟩
    exact hle p hp
  · ext p
    simp only [mem_setOf_eq, mem_singleton_iff]
    constructor
    · rintro ⟨hp, hmax⟩
      have h1 := hmax ps ⟨hps_pos, hps_le.le⟩
      have h1' : f ps ≤ f p := h1
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · have := hmono ⟨hp.1, h.le⟩ ⟨hps_pos, le_refl _⟩ h; linarith
      · have := hanti ⟨le_refl _, hps_le.le⟩ ⟨h.le, hp.2⟩ h; linarith
    · rintro rfl
      refine ⟨⟨hps_pos, hps_le.le⟩, fun q hq => ?_⟩
      have := hle q hq
      show f q ≤ f ps
      rw [hfps]; exact this
  · -- χ increasing in φ
    intro φ₁ h₁ φ₂ h₂ hlt
    have hR1 : φ₁ < R * μ := by linarith [h₁.2]
    have hR2 : φ₂ < R * μ := by linarith [h₂.2]
    obtain ⟨⟨-, hc1μ⟩, hr1, -⟩ := chi_spec hR hμ h₁.1 hR1
    show chi R μ φ₁ < chi R μ φ₂
    rw [← cubic_pos_iff hR hμ h₂.1 hR2]
    have e : chiCubic R μ φ₂ (chi R μ φ₁) =
        chiCubic R μ φ₁ (chi R μ φ₁) + (φ₂ - φ₁) * μ * (2 * μ - chi R μ φ₁) := by
      unfold chiCubic; ring
    rw [e, hr1]
    have : 0 < (φ₂ - φ₁) * μ * (2 * μ - chi R μ φ₁) :=
      mul_pos (mul_pos (by linarith) hμ) (by linarith)
    linarith
  · -- the maximum decreases
    intro φ₁ h₁ φ₂ h₂ hlt
    have hR1 : φ₁ < R * μ := by linarith [h₁.2]
    have hR2 : φ₂ < R * μ := by linarith [h₂.2]
    obtain ⟨⟨ha0, haμ⟩, -, -⟩ := chi_spec hR hμ h₁.1 hR1
    obtain ⟨⟨hb0, hbμ⟩, -, -⟩ := chi_spec hR hμ h₂.1 hR2
    have hab : chi R μ φ₁ < chi R μ φ₂ := by
      rw [← cubic_pos_iff hR hμ h₂.1 hR2]
      obtain ⟨-, hr1, -⟩ := chi_spec hR hμ h₁.1 hR1
      have e : chiCubic R μ φ₂ (chi R μ φ₁) =
          chiCubic R μ φ₁ (chi R μ φ₁) + (φ₂ - φ₁) * μ * (2 * μ - chi R μ φ₁) := by
        unfold chiCubic; ring
      rw [e, hr1]
      have : 0 < (φ₂ - φ₁) * μ * (2 * μ - chi R μ φ₁) :=
        mul_pos (mul_pos (by linarith) hμ) (by linarith)
      linarith
    set a := chi R μ φ₁
    set b := chi R μ φ₂
    show 2 * R * (μ - b) ^ 2 / (2 * μ - b) < 2 * R * (μ - a) ^ 2 / (2 * μ - a)
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    have hu : 0 < μ - b := by linarith
    have key : (μ - b) ^ 2 * (2 * μ - a) < (μ - a) ^ 2 * (2 * μ - b) := by
      nlinarith [mul_pos (mul_pos hu (sub_pos.mpr hab)) hμ, mul_pos hu (sub_pos.mpr hab),
        mul_pos (mul_pos hu hu) (sub_pos.mpr hab)]
    nlinarith [mul_lt_mul_of_pos_left key (mul_pos (by norm_num : (0:ℝ) < 2) hR)]
  · -- part 4
    intro hth
    set w := Real.sqrt (c / μ * R) with hw
    have hw2 : w ^ 2 = c / μ * R := Real.sq_sqrt (by positivity)
    have hw0 : 0 < w := Real.sqrt_pos.mpr (by positivity)
    have hwR : w < R := by
      have : w ^ 2 < R ^ 2 := by
        rw [hw2, div_mul_eq_mul_div, div_lt_iff₀ hμ]; nlinarith
      nlinarith
    -- the quadratic form of the threshold
    have hq : R * μ * ϕ ^ 2 + c ^ 2 * ϕ ≤ 2 * c ^ 3 := by
      have hRμ : 0 < 2 * R * μ := by positivity
      rw [le_div_iff₀ hRμ] at hth
      have h1 : 2 * R * μ * ϕ + c ^ 2 ≤ Real.sqrt (c ^ 3 * (c + 8 * R * μ)) := by linarith
      have h2 := pow_le_pow_left₀ (by positivity) h1 2
      rw [Real.sq_sqrt (by positivity)] at h2
      have h3 : 4 * (R * μ) * (R * μ * ϕ ^ 2 + c ^ 2 * ϕ - 2 * c ^ 3) ≤ 0 := by
        ring_nf; ring_nf at h2; linarith
      by_contra hcon
      push_neg at hcon
      have := mul_pos (by positivity : (0:ℝ) < 4 * (R * μ)) (sub_pos.mpr hcon)
      linarith
    -- ϕ (R + w)² < 4 μ w³
    have hc_eq : c = μ * w ^ 2 / R := by rw [hw2]; field_simp
    have hkey : ϕ * (R + w) ^ 2 < 4 * μ * w ^ 3 := by
      by_contra hcon
      push_neg at hcon
      set A := 4 * μ * w ^ 3 / (R + w) ^ 2 with hA
      have hRw : 0 < R + w := by linarith
      have hA0 : 0 ≤ A := by positivity
      have hϕA : A ≤ ϕ := by rw [hA, div_le_iff₀ (by positivity)]; linarith
      have hmon : R * μ * A ^ 2 + c ^ 2 * A ≤ R * μ * ϕ ^ 2 + c ^ 2 * ϕ := by
        have e1 : A ^ 2 ≤ ϕ ^ 2 := pow_le_pow_left₀ hA0 hϕA 2
        have e2 := mul_le_mul_of_nonneg_left e1 (mul_pos hR hμ).le
        have e3 := mul_le_mul_of_nonneg_left hϕA (sq_nonneg c)
        linarith
      have hid : R * μ * A ^ 2 + c ^ 2 * A - 2 * c ^ 3 =
          μ ^ 3 * w ^ 6 * ((R - w) * (14 * R ^ 3 + 10 * R ^ 2 * w + 6 * R * w ^ 2 + 2 * w ^ 3))
            / (R ^ 3 * (R + w) ^ 4) := by
        rw [hA, hc_eq]; field_simp; ring
      have hpos : 0 < μ ^ 3 * w ^ 6 * ((R - w) * (14 * R ^ 3 + 10 * R ^ 2 * w + 6 * R * w ^ 2
          + 2 * w ^ 3)) / (R ^ 3 * (R + w) ^ 4) := by
        apply div_pos _ (by positivity)
        apply mul_pos (by positivity)
        exact mul_pos (by linarith) (by positivity)
      linarith
    -- μϕ/χ² < w
    have hlt : μ * ϕ / χ ^ 2 < w := by
      rw [div_lt_iff₀ (by positivity)]
      by_contra hcon
      push_neg at hcon
      -- χ² ≤ μϕ/w
      have he := chi_eq hR hμ hϕ.le hϕR
      have h1 : 2 * μ ^ 2 * ϕ = χ * (R * χ ^ 2 + μ * ϕ) := by
        rw [← hχdef] at he; nlinarith [he]
      have h2 : w * χ * (R * χ ^ 2 + μ * ϕ) ≤ χ * μ * ϕ * (R + w) := by
        nlinarith [mul_le_mul_of_nonneg_left hcon (mul_pos hχ hR).le]
      have h3 : 2 * μ * w ≤ χ * (R + w) := by
        have : w * (2 * μ ^ 2 * ϕ) ≤ χ * μ * ϕ * (R + w) := by rw [h1]; linarith
        have hμϕ : 0 < μ * ϕ := mul_pos hμ hϕ
        nlinarith
      have h4 : 4 * μ ^ 2 * w ^ 2 ≤ χ ^ 2 * (R + w) ^ 2 := by
        have := pow_le_pow_left₀ (by positivity) h3 2; nlinarith
      have h5 : χ ^ 2 * w ≤ μ * ϕ := by linarith
      have h6 : 4 * μ ^ 2 * w ^ 3 ≤ μ * ϕ * (R + w) ^ 2 := by
        have := mul_le_mul_of_nonneg_left h4 hw0.le
        nlinarith [mul_le_mul_of_nonneg_right h5 (sq_nonneg (R + w))]
      nlinarith [mul_lt_mul_of_pos_left hkey hμ]
    show ps > R - w
    linarith [hRps]
