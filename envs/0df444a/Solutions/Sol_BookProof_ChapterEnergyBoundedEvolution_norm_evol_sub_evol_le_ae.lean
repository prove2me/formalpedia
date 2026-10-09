-- Prove2me | solution 1 for BookProof.ChapterEnergyBoundedEvolution.norm_evol_sub_evol_le_ae
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:38:46.683137+00:00
-- url     : https://prove2.me/submissions/fb954239-6ea3-4f93-bd61-91ce225e35b1

-- Generated from ChapterEnergyBoundedEvolution.lean — solution of BookProof.ChapterEnergyBoundedEvolution.norm_evol_sub_evol_le_ae
import Mathlib
import Definitions.Def_ChapterEnergyBoundedEvolution
import Theorems.Thm_BookProof_ChapterEnergyBoundedEvolution_phase_split
import Theorems.Thm_BookProof_EnergyBandDecomposition_norm_evolution_sub_scalar_le_prime
open BookProof.ChapterEnergyBoundedEvolution




open MeasureTheory Complex
open scoped ENNReal
open BookProof.EnergyBandDecomposition

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {E : X → ℝ} {f : X → ℂ}

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {E : X → ℝ} {f : X → ℂ}

set_option maxHeartbeats 1000000 in
theorem solution {Emax : ℝ} (h : EnergyLimited E μ Emax f) (s t : ℝ) :
    ∀ᵐ x ∂μ, ‖evol E t f x - evol E s f x‖ ≤ (|t - s| * Emax) * ‖f x‖ := by

  filter_upwards [h] with x hx
  rcases eq_or_ne (f x) 0 with hf | hf
  · simp [evol, hf]
  · have hE : |E x| ≤ Emax := hx hf
    have hsplit : Complex.exp (-(Complex.I * ((s : ℂ) * (E x : ℂ))))
        * Complex.exp (-(Complex.I * (((t - s : ℝ) : ℂ) * (E x : ℂ))))
        = Complex.exp (-(Complex.I * ((t : ℂ) * (E x : ℂ)))) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hfac : evol E t f x - evol E s f x
        = Complex.exp (-(Complex.I * ((s : ℂ) * (E x : ℂ))))
          * (Complex.exp (-(Complex.I * (((t - s : ℝ) : ℂ) * (E x : ℂ)))) * f x - f x) :=
      phase_split hsplit
    rw [hfac, norm_mul]
    have hphase : ‖Complex.exp (-(Complex.I * ((s : ℂ) * (E x : ℂ))))‖ = 1 := by
      have h : Complex.exp (-(Complex.I * ((s : ℂ) * (E x : ℂ))))
          = Complex.exp (Complex.I * ((-(s * E x) : ℝ) : ℂ)) := by
        congr 1
        push_cast
        ring
      rw [h, Complex.norm_exp_I_mul_ofReal]
    rw [hphase, one_mul]
    have hbound := norm_evolution_sub_scalar_le_prime (ε := Emax) (a := E x) (t - s) 0 (f x)
      (by simpa using hE)
    simpa using hbound
