-- Prove2me | solution 1 for DefectCoverUp.USEquilibrium.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T07:21:54.653711+00:00
-- url     : https://prove2.me/submissions/aace6807-59bc-4acc-b040-aee90611d6b7

import Mathlib
import Definitions.Def_DefectCoverUp_USEquilibrium_Model
import Theorems.Thm_DefectCoverUp_USEquilibrium_proposition_1_us
import Theorems.Thm_DefectCoverUp_USEquilibrium_manufacturer_report_rule
import Theorems.Thm_DefectCoverUp_USEquilibrium_report_without_investigation

open DefectCoverUp.USEquilibrium

theorem solution (P : Params) (hP : P.Standing) :
    ∃ hI ∈ Set.Ioo 0 P.hbar, ∃ ρI : ℝ → ℝ,
      ∃ hR ∈ Set.Ioo 0 P.hbar, ∃ ρR : ℝ → ℝ,
        ρI hI = 1 ∧
        (∀ h ∈ Set.Icc hI P.hbar, ρI h ∈ Set.Icc (0 : ℝ) 1) ∧
        ρR hR = 1 ∧
        (∀ h ∈ Set.Icc hR P.hbar, ρR h ∈ Set.Icc (0 : ℝ) 1) ∧
        (∀ h ∈ Set.Ioc 0 P.hbar, ∀ ρ ∈ Set.Icc (0 : ℝ) 1,
          (investigates P h ρ ↔ hI ≤ h ∧ ρI h ≤ ρ)) ∧
        ∀ h ∈ Set.Ioc 0 P.hbar, ∀ ρ ∈ Set.Icc (0 : ℝ) 1,
          ((max hI hR ≤ h ∧ max (ρI h) (ρR h) ≤ ρ) →
            ∀ σ : MAct × RAct, IsSPNE P h ρ σ ↔ σ = (MAct.R, RAct.I)) ∧
          ((h < hI ∨ (hI ≤ h ∧ ρ < ρI h)) →
            ∀ σ : MAct × RAct, IsSPNE P h ρ σ ↔ σ = (MAct.R, RAct.NI)) ∧
          (((hI ≤ h ∧ h < hR ∧ ρI h ≤ ρ) ∨
            (hR ≤ h ∧ ρI h ≤ ρ ∧ ρ < ρR h)) →
            ∀ σ : MAct × RAct, IsSPNE P h ρ σ ↔ σ = (MAct.NR, RAct.I)) := by
  obtain ⟨hI, hIm, ρI₀, hI1₀, hIr₀, hinv₀⟩ := DefectCoverUp.USEquilibrium.proposition_1_us P hP
  -- extend the regulator curve by the value `2` below its threshold (outside its domain)
  set ρI : ℝ → ℝ := fun h => if h < hI then 2 else ρI₀ h with hρIdef
  have hI1 : ρI hI = 1 := by simp only [hρIdef, lt_irrefl, if_false]; exact hI1₀
  have hIr : ∀ h ∈ Set.Icc hI P.hbar, ρI h ∈ Set.Icc (0 : ℝ) 1 := by
    intro h hh
    simp only [hρIdef, not_lt.mpr hh.1, if_false]; exact hIr₀ h hh
  have hbig : ∀ h ρ : ℝ, ρ ≤ 1 → ρI h ≤ ρ → hI ≤ h := by
    intro h ρ hρ hle
    by_contra hc
    have hc' : h < hI := not_le.mp hc
    simp only [hρIdef, hc', if_true] at hle
    linarith
  have hinv : ∀ h ∈ Set.Ioc 0 P.hbar, ∀ ρ ∈ Set.Icc (0 : ℝ) 1,
      (investigates P h ρ ↔ hI ≤ h ∧ ρI h ≤ ρ) := by
    intro h hh ρ hρ
    rw [hinv₀ h hh ρ hρ]
    by_cases hc : h < hI
    · simp only [hρIdef, hc, if_true, not_le.mpr hc, false_and]
    · simp only [hρIdef, hc, if_false]
  obtain ⟨hR, hRm, ρR, hR1, hRr, -, hrep⟩ :=
    DefectCoverUp.USEquilibrium.manufacturer_report_rule P hP
  refine ⟨hI, hIm, ρI, hR, hRm, ρR, hI1, hIr, hR1, hRr, hinv, ?_⟩
  intro h hh ρ hρ
  have hNI := DefectCoverUp.USEquilibrium.report_without_investigation P hP h hh ρ hρ
  have hi := hinv h hh ρ hρ
  have hr := hrep h hh ρ hρ
  -- characterisation of SPNE given the regulator's and manufacturer's choices
  have key : ∀ σ : MAct × RAct, IsSPNE P h ρ σ ↔
      ((σ.2 = RAct.I ↔ investigates P h ρ) ∧
        (σ.1 = MAct.R ↔ piNR P h ρ ≤ piReport P h ρ σ.2)) := fun σ => Iff.rfl
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨hm1, hm2⟩ σ
    have hinvT : investigates P h ρ := hi.2 ⟨le_of_max_le_left hm1, le_of_max_le_left hm2⟩
    have hrepT : piNR P h ρ ≤ piRI P h ρ :=
      hr.2 ⟨le_of_max_le_right hm1, le_of_max_le_right hm2⟩
    rw [key]
    obtain ⟨a, b⟩ := σ
    cases a <;> cases b <;> simp [piReport, hinvT, hrepT]
  · intro hcase σ
    have hinvF : ¬ investigates P h ρ := by
      rw [hi]
      rcases hcase with hc | ⟨-, hc⟩
      · exact fun ⟨h1, _⟩ => absurd h1 (not_le.mpr hc)
      · exact fun ⟨_, h2⟩ => absurd h2 (not_le.mpr hc)
    rw [key]
    obtain ⟨a, b⟩ := σ
    cases a <;> cases b <;> simp [piReport, hinvF, hNI]
  · intro hcase σ
    have hinvT : investigates P h ρ := by
      rw [hi]
      rcases hcase with ⟨h1, -, h3⟩ | ⟨h1, h2, -⟩
      · exact ⟨h1, h3⟩
      · exact ⟨hbig h ρ hρ.2 h2, h2⟩
    have hrepF : ¬ piNR P h ρ ≤ piRI P h ρ := by
      rw [hr]
      rcases hcase with ⟨-, h2, -⟩ | ⟨-, -, h3⟩
      · exact fun ⟨a, _⟩ => absurd a (not_le.mpr h2)
      · exact fun ⟨_, b⟩ => absurd b (not_le.mpr h3)
    rw [key]
    obtain ⟨a, b⟩ := σ
    cases a <;> cases b <;> simp [piReport, hinvT, hrepF]
