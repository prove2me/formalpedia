-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.dbar_conjugation_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:37:42.502382+00:00
-- url     : https://prove2.me/submissions/164456ec-3c8e-452f-8fdc-b9a7c72858a3

import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DbarConjugationWeight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C7.DbarConjW := by
  intro TT N f ζ hTT hG hf
  unfold C7.GGz at hG
  have hq : 0 < Complex.normSq ζ := by linarith
  have hζ : ζ ≠ 0 := by intro h; rw [h, Complex.normSq_zero] at hq; exact lt_irrefl _ hq
  let q : ℂ → ℝ := fun x => x.re * x.re + x.im * x.im
  have hqn : ∀ x, Complex.normSq x = q x := fun x => Complex.normSq_apply x
  have hWfun : (fun x => ((C7.Wz TT x : ℝ) : ℂ) ^ N * f x) =
      fun x => (((q x / (q x - TT)) ^ N : ℝ) : ℂ) * f x := by
    funext x; simp only [C7.Wz, C7.GGz, hqn]; push_cast; ring
  have hre : HasFDerivAt (fun x : ℂ => x.re) Complex.reCLM ζ := Complex.reCLM.hasFDerivAt
  have him : HasFDerivAt (fun x : ℂ => x.im) Complex.imCLM ζ := Complex.imCLM.hasFDerivAt
  have hqd : HasFDerivAt q ((ζ.re • Complex.reCLM + ζ.re • Complex.reCLM) +
      (ζ.im • Complex.imCLM + ζ.im • Complex.imCLM)) ζ := (hre.mul hre).add (him.mul him)
  have hq0 : q ζ - TT ≠ 0 := by rw [← hqn]; linarith
  have hφ : HasDerivAt (fun s : ℝ => (s / (s - TT)) ^ N)
      ((N : ℝ) * (q ζ / (q ζ - TT)) ^ (N - 1) * ((1 * (q ζ - TT) - q ζ * 1) / (q ζ - TT) ^ 2)) (q ζ) :=
    ((hasDerivAt_id (q ζ)).div ((hasDerivAt_id (q ζ)).sub_const TT) hq0).pow N
  have hWc := Complex.ofRealCLM.hasFDerivAt.comp ζ (hφ.comp_hasFDerivAt ζ hqd)
  have hP : HasFDerivAt (fun x => (((q x / (q x - TT)) ^ N : ℝ) : ℂ) * f x) _ ζ := hWc.mul hf.hasFDerivAt
  unfold C7.dbar
  rw [hWfun, hP.fderiv]
  simp
  have hWz : ((C7.Wz TT ζ : ℝ) : ℂ) = ((q ζ : ℝ) : ℂ) / (((q ζ : ℝ) : ℂ) - TT) := by
    simp only [C7.Wz, C7.GGz, hqn]; push_cast; ring
  have hGz : ((C7.GGz TT ζ : ℝ) : ℂ) = ((q ζ : ℝ) : ℂ) - TT := by
    simp only [C7.GGz, hqn]; push_cast; ring
  have hQ : ((q ζ : ℝ) : ℂ) = ζ * (starRingEnd ℂ) ζ := by rw [← hqn, Complex.mul_conj]
  have hc : (starRingEnd ℂ) ζ ≠ 0 := (map_ne_zero _).2 hζ
  have hd : ζ * (starRingEnd ℂ) ζ - TT ≠ 0 := by rw [← hQ]; exact_mod_cast hq0
  rw [hWz, hGz, hQ, Complex.re_eq_add_conj, Complex.im_eq_sub_conj]
  rcases N with _ | m
  · simp
  · simp only [Nat.add_sub_cancel]; push_cast
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    have hre2 : (ζ + (starRingEnd ℂ) ζ) / 2 + (ζ + (starRingEnd ℂ) ζ) / 2 + Complex.I *
        ((ζ - (starRingEnd ℂ) ζ) / (2 * Complex.I) + (ζ - (starRingEnd ℂ) ζ) / (2 * Complex.I)) = 2 * ζ := by
      field_simp; ring
    have hW : (ζ * (starRingEnd ℂ) ζ / (ζ * (starRingEnd ℂ) ζ - (TT : ℂ))) ^ (m + 1) /
        ((starRingEnd ℂ) ζ * (ζ * (starRingEnd ℂ) ζ - (TT : ℂ))) =
        (ζ * (starRingEnd ℂ) ζ / (ζ * (starRingEnd ℂ) ζ - (TT : ℂ))) ^ m * ζ /
          (ζ * (starRingEnd ℂ) ζ - (TT : ℂ)) ^ 2 := by
      rw [pow_succ]
      generalize (ζ * (starRingEnd ℂ) ζ / (ζ * (starRingEnd ℂ) ζ - (TT : ℂ))) ^ m = P
      field_simp
    linear_combination (f ζ * (((m : ℂ) + 1) * (ζ * (starRingEnd ℂ) ζ / (ζ * (starRingEnd ℂ) ζ - (TT : ℂ))) ^ m *
        (-(TT : ℂ) / (ζ * (starRingEnd ℂ) ζ - (TT : ℂ)) ^ 2)) / 2) * hre2 +
      (((m : ℂ) + 1) * (TT : ℂ) * f ζ) * hW
end Formalism.FourierDecayAlt.P
