-- Prove2me | solution 1 for DefectCoverUp.USEquilibrium.regulator_harm_threshold
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T07:18:40.767433+00:00
-- url     : https://prove2.me/submissions/445eb0ec-c67b-4e43-85a0-0f77767f7067

import Mathlib
import Definitions.Def_DefectCoverUp_USEquilibrium_Model
import Theorems.Thm_DefectCoverUp_USEquilibrium_welfare_difference

open DefectCoverUp.USEquilibrium

/-- A cubic with negative leading coefficient, negative at `0` and positive at `H > 0`,
changes sign exactly once on `[0, H]`. -/
lemma cu_cubic_threshold (f : ℝ → ℝ) (a b c e H : ℝ) (ha : a < 0)
    (hf : ∀ x, f x = a * x ^ 3 + b * x ^ 2 + c * x + e) (hH : 0 < H)
    (h0 : f 0 < 0) (h1 : 0 < f H) :
    ∃ s ∈ Set.Ioo 0 H, ∀ x ∈ Set.Icc (0 : ℝ) H, (0 ≤ f x ↔ s ≤ x) := by
  have hcont : ContinuousOn f (Set.Icc 0 H) := by
    have : f = fun x => a * x ^ 3 + b * x ^ 2 + c * x + e := funext hf
    rw [this]; fun_prop
  obtain ⟨s, ⟨hs0, hsH⟩, hs⟩ :=
    intermediate_value_Ioo hH.le hcont (show (0 : ℝ) ∈ Set.Ioo (f 0) (f H) from ⟨h0, h1⟩)
  set q : ℝ → ℝ := fun x => a * x ^ 2 + (b + a * s) * x + (c + b * s + a * s ^ 2) with hq
  have hfs : a * s ^ 3 + b * s ^ 2 + c * s + e = 0 := by rw [← hf]; exact hs
  have hfac : ∀ x, f x = (x - s) * q x := by
    intro x; rw [hf]; simp only [hq]; linear_combination hfs
  have hq0 : 0 < q 0 := by
    have := hfac 0; rw [this] at h0; nlinarith
  have hqH : 0 < q H := by
    have := hfac H; rw [this] at h1
    by_contra hc; have hc := not_lt.mp hc; nlinarith
  have hqpos : ∀ x ∈ Set.Icc (0 : ℝ) H, 0 < q x := by
    rintro x ⟨hx0, hxH⟩
    have key : H * q x = (H - x) * q 0 + x * q H - a * x * (H - x) * H := by
      simp only [hq]; ring
    have : 0 < H * q x := by
      rw [key]
      have h2 : 0 ≤ -a * x * (H - x) * H := by
        have : 0 ≤ -a := by linarith
        have : 0 ≤ H - x := by linarith
        positivity
      rcases eq_or_lt_of_le hx0 with hx | hx
      · subst hx; nlinarith
      · nlinarith [mul_pos hx hqH, mul_nonneg (sub_nonneg.mpr hxH) hq0.le]
    exact pos_of_mul_pos_right this hH.le
  refine ⟨s, ⟨hs0, hsH⟩, fun x hx => ?_⟩
  have hqx := hqpos x hx
  rw [hfac x]
  constructor
  · intro h; by_contra hc; have hc := not_le.mp hc
    have : (x - s) * q x < 0 := mul_neg_of_neg_of_pos (by linarith) hqx
    linarith
  · intro h; exact mul_nonneg (by linarith) hqx.le

/-- Generic threshold rule: if `Om - X` changes sign once at `hR` on `[0, H]` and
`X > 0`, then `post ρ * Om h - X h ≥ 0` iff `h ≥ hR` and `ρ ≥ max ((X/Om - PD)/(1-PD)) 0`. -/
lemma cu_rule (Om X : ℝ → ℝ) (PD H hR : ℝ) (hPD0 : 0 < PD) (hPD1 : PD < 1)
    (hR0 : 0 < hR) (hRH : hR < H)
    (hX : ∀ h ∈ Set.Ioc 0 H, 0 < X h) (hc : Continuous (fun h => Om h - X h))
    (hthr : ∀ h ∈ Set.Icc (0 : ℝ) H, (0 ≤ Om h - X h ↔ hR ≤ h)) :
    (fun h => max ((X h / Om h - PD) / (1 - PD)) 0) hR = 1 ∧
    (∀ h ∈ Set.Icc hR H,
      (fun h => max ((X h / Om h - PD) / (1 - PD)) 0) h ∈ Set.Icc (0 : ℝ) 1) ∧
    ∀ h ∈ Set.Ioc 0 H, ∀ ρ ∈ Set.Icc (0 : ℝ) 1,
      (0 ≤ (ρ + (1 - ρ) * PD) * Om h - X h ↔
        hR ≤ h ∧ (fun h => max ((X h / Om h - PD) / (1 - PD)) 0) h ≤ ρ) := by
  have hPD' : 0 < 1 - PD := by linarith
  -- value at the threshold
  have hzero : Om hR - X hR = 0 := by
    have hge : 0 ≤ Om hR - X hR := (hthr hR ⟨hR0.le, hRH.le⟩).2 le_rfl
    refine le_antisymm ?_ hge
    have ht : Filter.Tendsto (fun h => Om h - X h) (nhdsWithin hR (Set.Iio hR))
        (nhds (Om hR - X hR)) := hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsLT hR0] with x hx
    have hx' : ¬ (0 ≤ Om x - X x) := by
      rw [hthr x ⟨hx.1.le, (hx.2.trans hRH).le⟩]; exact not_le.mpr hx.2
    exact (not_le.mp hx').le
  have hXR := hX hR ⟨hR0, hRH.le⟩
  refine ⟨?_, ?_, ?_⟩
  · show max ((X hR / Om hR - PD) / (1 - PD)) 0 = 1
    have : Om hR = X hR := by linarith
    rw [this, div_self hXR.ne', div_self hPD'.ne']
    exact max_eq_left zero_le_one
  · rintro h ⟨hh1, hh2⟩
    show max ((X h / Om h - PD) / (1 - PD)) 0 ∈ Set.Icc (0 : ℝ) 1
    have hXh := hX h ⟨hR0.trans_le hh1, hh2⟩
    have hge := (hthr h ⟨(hR0.trans_le hh1).le, hh2⟩).2 hh1
    have hOm : 0 < Om h := by linarith
    refine ⟨le_max_right _ _, max_le ?_ zero_le_one⟩
    rw [div_le_one hPD']
    have : X h / Om h ≤ 1 := by rw [div_le_one hOm]; linarith
    linarith
  · rintro h ⟨hh0, hhH⟩ ρ ⟨hρ0, hρ1⟩
    show _ ↔ hR ≤ h ∧ max ((X h / Om h - PD) / (1 - PD)) 0 ≤ ρ
    have hXh := hX h ⟨hh0, hhH⟩
    have hpost0 : 0 < ρ + (1 - ρ) * PD := by nlinarith
    have hpost1 : ρ + (1 - ρ) * PD ≤ 1 := by nlinarith
    by_cases hle : hR ≤ h
    · have hge := (hthr h ⟨hh0.le, hhH⟩).2 hle
      have hOm : 0 < Om h := by linarith
      simp only [hle, true_and, max_le_iff, hρ0, and_true]
      rw [div_le_iff₀ hPD', div_sub' hOm.ne', div_le_iff₀ hOm]
      constructor <;> intro H1 <;> nlinarith
    · simp only [hle, false_and, iff_false, not_le]
      have hlt : Om h - X h < 0 := by
        by_contra hc'
        exact hle ((hthr h ⟨hh0.le, hhH⟩).1 (not_lt.mp hc'))
      rcases le_or_gt (Om h) 0 with hO | hO
      · nlinarith
      · nlinarith

theorem solution (P : Params) (hP : P.Standing) :
    (∃ a b c : ℝ, ∀ h : ℝ,
      chi1hat P h = -3 * P.l / (2 * P.hbar * P.vbar) * h ^ 3 +
        a * h ^ 2 + b * h + c) ∧
    -3 * P.l / (2 * P.hbar * P.vbar) < 0 ∧
    chi1hat P 0 = -P.r * P.l / P.vbar * (P.vbar - P.p) - P.C ∧
    chi1hat P 0 < 0 ∧
    chi1hat P P.hbar =
      (P.r + P.hbar) / (2 * P.vbar) * (P.vbar - P.p) * (1 - P.l) ∧
    0 < chi1hat P P.hbar ∧
    ∃ hI ∈ Set.Ioo 0 P.hbar, ∃ ρI : ℝ → ℝ,
      (∀ h ∈ Set.Icc (0 : ℝ) P.hbar, (0 ≤ chi1hat P h ↔ hI ≤ h)) ∧
      (∀ h ∈ Set.Icc hI P.hbar,
        ρI h = max (rhoPrime P h) 0 ∧ ρI h ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ h ∈ Set.Ioc 0 P.hbar,
        ((∀ ρ ∈ Set.Icc (0 : ℝ) 1, WRI P h ρ - WRNI P h ρ < 0) ↔ h < hI)) ∧
      ∀ h ∈ Set.Ioc 0 P.hbar, ∀ ρ ∈ Set.Icc (0 : ℝ) 1,
        (0 ≤ WRI P h ρ - WRNI P h ρ ↔ hI ≤ h ∧ ρI h ≤ ρ) := by
  have hP' := hP
  obtain ⟨hp, hr, hrp, hH, hpv, hC, hl0, hl1, hth0, hth1, hal0, hal1, hK1, hK2, hPD0, hPD1⟩ := hP'
  have hv : 0 < P.vbar := by linarith
  have hform : ∀ h : ℝ, chi1hat P h = -3 * P.l / (2 * P.hbar * P.vbar) * h ^ 3 +
      ((3 * P.hbar * P.l / 2 - P.l * P.p / 2 - P.l * P.r + 3 * P.l * P.vbar / 2 + P.p / 2
        - P.vbar / 2) / (P.vbar * P.hbar)) * h ^ 2 +
      ((P.C * P.vbar + P.hbar * P.l * P.p + P.hbar * P.l * P.r - 2 * P.hbar * P.l * P.vbar
        - P.hbar * P.p + P.hbar * P.vbar - P.l * P.p * P.r / 2 + P.l * P.r * P.vbar / 2
        - P.p * P.r / 2 + P.r * P.vbar / 2) / (P.vbar * P.hbar)) * h +
      ((-P.C * P.hbar * P.vbar + P.hbar * P.l * P.p * P.r - P.hbar * P.l * P.r * P.vbar)
        / (P.vbar * P.hbar)) := by
    intro h; unfold chi1hat chi1; field_simp; ring
  have hlead : -3 * P.l / (2 * P.hbar * P.vbar) < 0 := by
    rw [neg_mul, neg_div]; exact neg_neg_of_pos (by positivity)
  have hz : chi1hat P 0 = -P.r * P.l / P.vbar * (P.vbar - P.p) - P.C := by
    unfold chi1hat chi1; field_simp; ring
  have hzneg : chi1hat P 0 < 0 := by
    rw [hz]
    have : 0 < P.r * P.l / P.vbar * (P.vbar - P.p) := by
      have : 0 < P.vbar - P.p := by linarith
      positivity
    have e : -P.r * P.l / P.vbar * (P.vbar - P.p) = -(P.r * P.l / P.vbar * (P.vbar - P.p)) := by
      ring
    linarith
  have hHv : chi1hat P P.hbar =
      (P.r + P.hbar) / (2 * P.vbar) * (P.vbar - P.p) * (1 - P.l) := by
    unfold chi1hat chi1; field_simp; ring
  have hHpos : 0 < chi1hat P P.hbar := by
    rw [hHv]
    have : 0 < P.vbar - P.p := by linarith
    have : 0 < 1 - P.l := by linarith
    have : 0 < P.r + P.hbar := by linarith
    positivity
  obtain ⟨hI, ⟨hI0, hIH⟩, hthr⟩ :=
    cu_cubic_threshold (chi1hat P) _ _ _ _ _ hlead hform hH hzneg hHpos
  -- the generic reliability rule
  set X : ℝ → ℝ := fun h => P.l * h * (P.vbar - h / 2) / P.vbar + P.C with hXdef
  have hX : ∀ h ∈ Set.Ioc 0 P.hbar, 0 < X h := by
    rintro h ⟨h0, h1⟩
    simp only [hXdef]
    have : 0 < P.vbar - h / 2 := by linarith
    positivity
  have hchi : ∀ h, chi1hat P h = chi1 P h - X h := by
    intro h; simp only [hXdef]; unfold chi1hat; ring
  have hc : Continuous (fun h => chi1 P h - X h) := by
    simp only [hXdef]; unfold chi1; fun_prop
  have hthr' : ∀ h ∈ Set.Icc (0 : ℝ) P.hbar, (0 ≤ chi1 P h - X h ↔ hI ≤ h) := by
    intro h hh; rw [← hchi]; exact hthr h hh
  obtain ⟨h1, h2, h3⟩ := cu_rule (chi1 P) X P.PD P.hbar hI hPD0 hPD1 hI0 hIH hX hc hthr'
  have hW : ∀ h ∈ Set.Ioc 0 P.hbar, ∀ ρ ∈ Set.Icc (0 : ℝ) 1,
      WRI P h ρ - WRNI P h ρ = (ρ + (1 - ρ) * P.PD) * chi1 P h - X h := by
    intro h hh ρ hρ
    rw [DefectCoverUp.USEquilibrium.welfare_difference P hP h hh ρ hρ]
    simp only [hXdef]; unfold post; ring
  refine ⟨⟨_, _, _, hform⟩, hlead, hz, hzneg, hHv, hHpos, hI, ⟨hI0, hIH⟩,
    fun h => max ((X h / chi1 P h - P.PD) / (1 - P.PD)) 0, hthr,
    fun h hh => ⟨rfl, h2 h hh⟩, ?_, ?_⟩
  · intro h hh
    constructor
    · intro hall
      by_contra hc'
      have hge : hI ≤ h := not_lt.mp hc'
      have := hall 1 ⟨zero_le_one, le_rfl⟩
      have h31 := (h3 h hh 1 ⟨zero_le_one, le_rfl⟩).2 ⟨hge, (h2 h ⟨hge, hh.2⟩).2⟩
      rw [hW h hh 1 ⟨zero_le_one, le_rfl⟩] at this
      linarith
    · intro hlt ρ hρ
      rw [hW h hh ρ hρ]
      by_contra hc'
      have := (h3 h hh ρ hρ).1 (not_lt.mp hc')
      exact absurd this.1 (not_le.mpr hlt)
  · intro h hh ρ hρ
    rw [hW h hh ρ hρ]
    exact h3 h hh ρ hρ
