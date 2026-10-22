-- Prove2me | solution 1 for DefectCoverUp.USEquilibrium.proposition_1_us
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T07:21:40.455686+00:00
-- url     : https://prove2.me/submissions/9e95997a-38d0-4ef4-9aef-31432cfa472a

import Mathlib
import Definitions.Def_DefectCoverUp_USEquilibrium_Model
import Theorems.Thm_DefectCoverUp_USEquilibrium_regulator_harm_threshold

open DefectCoverUp.USEquilibrium

theorem solution (P : Params) (hP : P.Standing) :
    ∃ hI ∈ Set.Ioo 0 P.hbar, ∃ ρI : ℝ → ℝ,
      ρI hI = 1 ∧
      (∀ h ∈ Set.Icc hI P.hbar, ρI h ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ h ∈ Set.Ioc 0 P.hbar, ∀ ρ ∈ Set.Icc (0 : ℝ) 1,
        (investigates P h ρ ↔ hI ≤ h ∧ ρI h ≤ ρ) := by
  obtain ⟨-, -, -, -, -, -, hI, ⟨hI0, hIH⟩, ρI, hthr, hρI, -, hmain⟩ :=
    DefectCoverUp.USEquilibrium.regulator_harm_threshold P hP
  obtain ⟨hp, hr, hrp, hH, hpv, hC, hl0, hl1, hth0, hth1, hal0, hal1, hK1, hK2, hPD0, hPD1⟩ := hP
  have hv : 0 < P.vbar := by linarith
  -- `chi1hat` vanishes at the threshold, by continuity
  have hc : Continuous (chi1hat P) := by unfold chi1hat chi1; fun_prop
  have hzero : chi1hat P hI = 0 := by
    have hge : 0 ≤ chi1hat P hI := (hthr hI ⟨hI0.le, hIH.le⟩).2 le_rfl
    refine le_antisymm ?_ hge
    have ht : Filter.Tendsto (chi1hat P) (nhdsWithin hI (Set.Iio hI))
        (nhds (chi1hat P hI)) := hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsLT hI0] with x hx
    have hx' : ¬ (0 ≤ chi1hat P x) := by
      rw [hthr x ⟨hx.1.le, (hx.2.trans hIH).le⟩]; exact not_le.mpr hx.2
    exact (not_le.mp hx').le
  have hX : 0 < P.l * hI * (P.vbar - hI / 2) / P.vbar + P.C := by
    have : 0 < P.vbar - hI / 2 := by linarith
    positivity
  have hchi : chi1 P hI = P.l * hI * (P.vbar - hI / 2) / P.vbar + P.C := by
    unfold chi1hat at hzero; linear_combination hzero
  have hrho : rhoPrime P hI = 1 := by
    unfold rhoPrime
    rw [hchi, div_self hX.ne', div_self (by linarith : (1 : ℝ) - P.PD ≠ 0)]
  refine ⟨hI, ⟨hI0, hIH⟩, ρI, ?_, fun h hh => (hρI h hh).2, ?_⟩
  · rw [(hρI hI ⟨le_rfl, hIH.le⟩).1, hrho]; exact max_eq_left zero_le_one
  · intro h hh ρ hρ
    unfold investigates
    rw [← sub_nonneg]
    exact hmain h hh ρ hρ
