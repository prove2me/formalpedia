-- Prove2me | solution 1 for DefectCoverUp.USEquilibrium.manufacturer_report_rule
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T07:16:46.076319+00:00
-- url     : https://prove2.me/submissions/8c3af835-fa20-478b-8e47-2ee26062f4f4

import Mathlib
import Definitions.Def_DefectCoverUp_USEquilibrium_Model
import Theorems.Thm_DefectCoverUp_USEquilibrium_profit_difference
import Theorems.Thm_DefectCoverUp_USEquilibrium_manufacturer_harm_threshold

open DefectCoverUp.USEquilibrium

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
    ∃ hR ∈ Set.Ioo 0 P.hbar, ∃ ρR : ℝ → ℝ,
      ρR hR = 1 ∧
      (∀ h ∈ Set.Icc hR P.hbar, ρR h ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ h ∈ Set.Icc hR P.hbar, ρR h = max (rho1 P h) 0) ∧
      ∀ h ∈ Set.Ioc 0 P.hbar, ∀ ρ ∈ Set.Icc (0 : ℝ) 1,
        (piNR P h ρ ≤ piRI P h ρ ↔ hR ≤ h ∧ ρR h ≤ ρ) := by
  obtain ⟨-, -, -, -, -, -, hR, ⟨hR0, hRH⟩, hthr⟩ :=
    DefectCoverUp.USEquilibrium.manufacturer_harm_threshold P hP
  have hP' := hP
  obtain ⟨hp, hr, hrp, hH, hpv, hC, hl0, hl1, hth0, hth1, hal0, hal1, hK1, hK2, hPD0, hPD1⟩ := hP'
  have hv : 0 < P.vbar := by linarith
  have hX : ∀ h ∈ Set.Ioc 0 P.hbar, 0 < P.p * P.l * h / P.vbar := by
    rintro h ⟨h0, -⟩; positivity
  have hc : Continuous (fun h => Omega1 P h - P.p * P.l * h / P.vbar) := by
    unfold Omega1; fun_prop
  have hthr' : ∀ h ∈ Set.Icc (0 : ℝ) P.hbar,
      (0 ≤ Omega1 P h - P.p * P.l * h / P.vbar ↔ hR ≤ h) := hthr
  obtain ⟨h1, h2, h3⟩ := cu_rule (Omega1 P) (fun h => P.p * P.l * h / P.vbar) P.PD P.hbar hR
    hPD0 hPD1 hR0 hRH hX hc hthr'
  refine ⟨hR, ⟨hR0, hRH⟩, _, h1, h2, fun h _ => rfl, ?_⟩
  intro h hh ρ hρ
  rw [← sub_nonneg, DefectCoverUp.USEquilibrium.profit_difference P hP h hh ρ hρ]
  exact h3 h hh ρ hρ
