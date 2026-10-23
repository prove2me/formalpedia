-- Prove2me | solution 1 for AvramDividend.Classical.continuousOn_Ioi_eq_of_laplace_eq_signed
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T07:43:41.702285+00:00
-- url     : https://prove2.me/submissions/76653be3-c14a-4c1f-822c-78b687f3eae1

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_continuousOn_Ioi_eq_of_laplace_eq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- Signed continuous functions with the same integrable Laplace transform agree. -/
theorem solution
    (f g : ℝ → ℝ) (b : ℝ)
    (hfcont : ContinuousOn f (Ioi 0))
    (hgcont : ContinuousOn g (Ioi 0))
    (hlap : ∀ θ : ℝ, b < θ →
      IntegrableOn (fun x : ℝ => Real.exp (-θ * x) * f x) (Ioi 0) ∧
      IntegrableOn (fun x : ℝ => Real.exp (-θ * x) * g x) (Ioi 0) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) * f x) =
        ∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) * g x) :
    ∀ x : ℝ, 0 < x → f x = g x := by
  let A : ℝ → ℝ := fun x => |f x| + |g x|
  let F : ℝ → ℝ := fun x => f x + A x
  let G : ℝ → ℝ := fun x => g x + A x
  have hAcont : ContinuousOn A (Ioi (0 : ℝ)) := hfcont.abs.add hgcont.abs
  have hFcont : ContinuousOn F (Ioi (0 : ℝ)) := hfcont.add hAcont
  have hGcont : ContinuousOn G (Ioi (0 : ℝ)) := hgcont.add hAcont
  have hFnonneg : ∀ x : ℝ, 0 < x → 0 ≤ F x := by
    intro x _
    dsimp [F, A]
    linarith [neg_le_abs (f x), abs_nonneg (g x)]
  have hGnonneg : ∀ x : ℝ, 0 < x → 0 ≤ G x := by
    intro x _
    dsimp [G, A]
    linarith [neg_le_abs (g x), abs_nonneg (f x)]
  have hFG : ∀ θ : ℝ, b < θ →
      IntegrableOn (fun x : ℝ => Real.exp (-θ * x) * F x) (Ioi 0) ∧
      IntegrableOn (fun x : ℝ => Real.exp (-θ * x) * G x) (Ioi 0) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) * F x) =
        ∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) * G x := by
    intro θ hθ
    obtain ⟨hf, hg, heq⟩ := hlap θ hθ
    have hfa : IntegrableOn
        (fun x : ℝ => Real.exp (-θ * x) * |f x|) (Ioi 0) := by
      change Integrable (fun x : ℝ => Real.exp (-θ * x) * |f x|)
        (volume.restrict (Ioi 0))
      simpa only [abs_mul, abs_of_pos (Real.exp_pos _)] using hf.abs
    have hga : IntegrableOn
        (fun x : ℝ => Real.exp (-θ * x) * |g x|) (Ioi 0) := by
      change Integrable (fun x : ℝ => Real.exp (-θ * x) * |g x|)
        (volume.restrict (Ioi 0))
      simpa only [abs_mul, abs_of_pos (Real.exp_pos _)] using hg.abs
    have hA : IntegrableOn
        (fun x : ℝ => Real.exp (-θ * x) * A x) (Ioi 0) := by
      have heqA : (fun x : ℝ => Real.exp (-θ * x) * A x) =
          (fun x : ℝ => Real.exp (-θ * x) * |f x|) +
          (fun x : ℝ => Real.exp (-θ * x) * |g x|) := by
        funext x
        simp [A, mul_add, Pi.add_apply]
      rw [heqA]
      exact hfa.add hga
    have hFi : IntegrableOn
        (fun x : ℝ => Real.exp (-θ * x) * F x) (Ioi 0) := by
      have heqF : (fun x : ℝ => Real.exp (-θ * x) * F x) =
          (fun x : ℝ => Real.exp (-θ * x) * f x) +
          (fun x : ℝ => Real.exp (-θ * x) * A x) := by
        funext x
        simp [F, mul_add, Pi.add_apply]
      rw [heqF]
      exact hf.add hA
    have hGi : IntegrableOn
        (fun x : ℝ => Real.exp (-θ * x) * G x) (Ioi 0) := by
      have heqG : (fun x : ℝ => Real.exp (-θ * x) * G x) =
          (fun x : ℝ => Real.exp (-θ * x) * g x) +
          (fun x : ℝ => Real.exp (-θ * x) * A x) := by
        funext x
        simp [G, mul_add, Pi.add_apply]
      rw [heqG]
      exact hg.add hA
    refine ⟨hFi, hGi, ?_⟩
    have hsF :
        (∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) * F x) =
        (∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) * f x) +
          ∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) * A x := by
      simpa only [F, mul_add] using (integral_add hf hA)
    have hsG :
        (∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) * G x) =
        (∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) * g x) +
          ∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) * A x := by
      simpa only [G, mul_add] using (integral_add hg hA)
    calc
      _ = (∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) * f x) +
          ∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) * A x := hsF
      _ = (∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) * g x) +
          ∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) * A x := by rw [heq]
      _ = _ := hsG.symm
  have huniq := continuousOn_Ioi_eq_of_laplace_eq
    F G b hFcont hGcont hFnonneg hGnonneg hFG
  intro x hx
  have h := huniq x hx
  dsimp [F, G] at h
  linarith
