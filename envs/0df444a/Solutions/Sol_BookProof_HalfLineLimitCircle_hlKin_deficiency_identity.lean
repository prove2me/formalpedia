-- Prove2me | solution 1 for BookProof.HalfLineLimitCircle.hlKin_deficiency_identity
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:40:58.277269+00:00
-- url     : https://prove2.me/submissions/09400d6d-dbd4-4606-8e73-1edac0d8240b

-- Generated from ChapterHalfLineLimitCircle.lean — solution of BookProof.HalfLineLimitCircle.hlKin_deficiency_identity
import Mathlib
import Definitions.Def_ChapterHalfLineLimitCircle
import Theorems.Thm_BookProof_HalfLineLimitCircle_hlKin_coeFn
import Theorems.Thm_BookProof_HalfLineLimitCircle_integral_deriv2_mul
import Theorems.Thm_BookProof_HalfLineLimitCircle_deriv2_deficiencyFun
import Theorems.Thm_BookProof_HalfLineLimitCircle_deficiencyVec_coeFn
import Theorems.Thm_BookProof_HalfLineLimitCircle_inner_eq_integral
import Definitions.Def_ChapterFarisLavine
open BookProof.HalfLineLimitCircle




open MeasureTheory Set BookProof.FarisLavine

noncomputable section

local notation "smoothTop" => ((⊤ : ℕ∞) : WithTop ℕ∞)

set_option maxHeartbeats 1000000 in
theorem solution (v : hlCore) :
    (inner ℂ (hlKin v) deficiencyVec : ℂ) = Complex.I * inner ℂ (v : HL) deficiencyVec := by

  obtain ⟨f, rfl⟩ := hlEquiv.surjective v
  simp only [hlEquiv_coe]
  rw [inner_eq_integral (hlKin_coeFn f) deficiencyVec_coeFn,
    inner_eq_integral (testIncl_coeFn f) deficiencyVec_coeFn]
  have hibp := integral_deriv2_mul (f : ℝ → ℂ) f.2 deficiencyFun deficiencyFun_contDiff
  rw [deriv2_deficiencyFun] at hibp
  have hpoint : ∀ x : ℝ, (starRingEnd ℂ) ((f : ℝ → ℂ) x) * (-Complex.I * deficiencyFun x)
      = -(Complex.I * ((starRingEnd ℂ) ((f : ℝ → ℂ) x) * deficiencyFun x)) := fun x => by ring
  simp only [map_neg, neg_mul, integral_neg]
  rw [hibp]
  simp_rw [hpoint]
  rw [integral_neg, integral_const_mul]
  ring
