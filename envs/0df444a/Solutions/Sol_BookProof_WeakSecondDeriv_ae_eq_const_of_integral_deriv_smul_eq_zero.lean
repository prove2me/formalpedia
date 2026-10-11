-- Prove2me | solution 1 for BookProof.WeakSecondDeriv.ae_eq_const_of_integral_deriv_smul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T17:21:05.169235+00:00
-- url     : https://prove2.me/submissions/dd5d4813-6b50-4170-815f-cc86635709f1

-- Generated from ChapterWeakSecondDerivative.lean — solution of BookProof.WeakSecondDeriv.ae_eq_const_of_integral_deriv_smul_eq_zero
import Mathlib
import Definitions.Def_ChapterWeakSecondDerivative
import Theorems.Thm_BookProof_WeakSecondDeriv_IsTestFun_integrable
import Theorems.Thm_BookProof_WeakSecondDeriv_IsTestFun_sub
import Theorems.Thm_BookProof_WeakSecondDeriv_IsTestFun_const_mul
import Theorems.Thm_BookProof_WeakSecondDeriv_exists_unitTest
import Theorems.Thm_BookProof_WeakSecondDeriv_exists_antideriv
import Theorems.Thm_BookProof_WeakSecondDeriv_integrable_test_smul
import Definitions.Def_ChapterSirkFinitePrecision
open BookProof.WeakSecondDeriv




open MeasureTheory Filter Topology intervalIntegral Set

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution {r : ℝ → F}
    (hr : LocallyIntegrable r volume)
    (h : ∀ g : ℝ → ℝ, IsTestFun g → ∫ x, deriv g x • r x = 0) :
    ∃ c : F, r =ᵐ[volume] fun _ => c := by

  obtain ⟨ρ, hρ, hρ1⟩ := exists_unitTest
  set c : F := ∫ x, ρ x • r x with hc
  have key : ∀ φ : ℝ → ℝ, IsTestFun φ → ∫ x, φ x • r x = (∫ x, φ x) • c := by
    intro φ hφ
    set I := ∫ x, φ x with hI
    have hIρ : IsTestFun (fun x => I * ρ x) := hρ.const_mul I
    have hψ : IsTestFun (fun x => φ x - I * ρ x) := hφ.sub hIρ
    have hψ0 : ∫ x, (φ x - I * ρ x) = 0 := by
      rw [integral_sub hφ.integrable hIρ.integrable, MeasureTheory.integral_const_mul, hρ1]
      simp [hI]
    obtain ⟨G, hG, hdG⟩ := exists_antideriv hψ hψ0
    have h1 := h G hG
    rw [hdG] at h1
    have hint2 : Integrable (fun x => I • (ρ x • r x)) volume :=
      (integrable_test_smul hρ hr).smul I
    have h2 : ∫ x, ((fun x => φ x - I * ρ x) x) • r x = (∫ x, φ x • r x) - I • c := by
      have he : ∀ x, (φ x - I * ρ x) • r x = φ x • r x - I • (ρ x • r x) := by
        intro x; rw [sub_smul, smul_smul]
      simp_rw [he]
      rw [integral_sub (integrable_test_smul hφ hr) hint2, MeasureTheory.integral_smul]
    rw [h2] at h1
    exact sub_eq_zero.mp h1
  refine ⟨c, ?_⟩
  have hloc : LocallyIntegrable (fun x => r x - c) volume := hr.sub (locallyIntegrable_const c)
  have hz := ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc (fun g hg1 hg2 => ?_)
  · filter_upwards [hz] with x hx
    simpa [sub_eq_zero] using hx
  · have hg : IsTestFun g := ⟨hg1, hg2⟩
    have he : ∀ x, g x • (r x - c) = g x • r x - g x • c := fun x => by rw [smul_sub]
    simp_rw [he]
    rw [integral_sub (integrable_test_smul hg hr) (hg.integrable.smul_const c),
      _root_.integral_smul_const, key g hg]
    module
