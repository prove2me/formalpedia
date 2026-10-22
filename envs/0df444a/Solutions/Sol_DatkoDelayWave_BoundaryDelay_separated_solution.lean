-- Prove2me | solution 1 for DatkoDelayWave.BoundaryDelay.separated_solution
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:38:37.513213+00:00
-- url     : https://prove2.me/submissions/45334cdc-8632-4947-81c0-38dca711d4c5

import Mathlib
import Definitions.Def_DatkoDelayWave_BoundaryDelay_DelayedWave

set_option autoImplicit false
open DatkoDelayWave.BoundaryDelay

theorem solution (a k ε : ℝ) (ω : ℂ) (φ : ℝ → ℂ)
    (hφ : IsEigenpair a k ε ω φ) :
    IsClassicalSolution a k ε (fun x t => Complex.exp (ω * (t : ℂ)) * φ x) := by
  obtain ⟨hc, hode, hleft, hright⟩ := hφ
  have hE : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Complex.exp (ω * (s : ℂ)))
      (Complex.exp (ω * (t : ℂ)) * ω) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => ω * (s : ℂ)) (ω * 1) t :=
      (hasDerivAt_id t).ofReal_comp.const_mul ω
    simpa using h1.cexp
  have hut : ∀ x t, ut (fun x t => Complex.exp (ω * (t : ℂ)) * φ x) x t
      = ω * Complex.exp (ω * (t : ℂ)) * φ x := by
    intro x t
    show deriv (fun s : ℝ => Complex.exp (ω * (s : ℂ)) * φ x) t = _
    rw [((hE t).mul_const (φ x)).deriv]
    ring
  have hutt : ∀ x t, utt (fun x t => Complex.exp (ω * (t : ℂ)) * φ x) x t
      = ω * (ω * Complex.exp (ω * (t : ℂ))) * φ x := by
    intro x t
    have : ut (fun x t => Complex.exp (ω * (t : ℂ)) * φ x) x
        = fun s : ℝ => ω * Complex.exp (ω * (s : ℂ)) * φ x := funext (hut x)
    unfold utt
    rw [this]
    have h2 : HasDerivAt (fun s : ℝ => ω * Complex.exp (ω * (s : ℂ)) * φ x)
        (ω * (Complex.exp (ω * (t : ℂ)) * ω) * φ x) t :=
      ((hE t).const_mul ω).mul_const (φ x)
    rw [h2.deriv]
    ring
  have hux : ∀ y t, ux (fun x t => Complex.exp (ω * (t : ℂ)) * φ x) y t
      = Complex.exp (ω * (t : ℂ)) * deriv φ y := by
    intro y t
    show deriv (fun y : ℝ => Complex.exp (ω * (t : ℂ)) * φ y) y = _
    exact congrFun (deriv_const_mul_field' _) _
  have huxx : ∀ x t, uxx (fun x t => Complex.exp (ω * (t : ℂ)) * φ x) x t
      = Complex.exp (ω * (t : ℂ)) * deriv (deriv φ) x := by
    intro x t
    show deriv (fun y : ℝ => ux (fun x t => Complex.exp (ω * (t : ℂ)) * φ x) y t) x = _
    simp only [hux]
    exact congrFun (deriv_const_mul_field' _) _
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (Complex.contDiff_exp.comp (contDiff_const.mul
      (Complex.ofRealCLM.contDiff.comp contDiff_snd))).mul (hc.comp contDiff_fst)
  · intro x hx t _
    rw [hutt, huxx, hut, hode x hx]
    ring
  · intro t _
    simp [hleft]
  · intro t ht
    have hd : deriv φ 1 = -((k : ℂ) * ω * Complex.exp (-(ε : ℂ) * ω) * φ 1) := by
      linear_combination hright
    have e : Complex.exp (ω * ((t - ε : ℝ) : ℂ))
        = Complex.exp (ω * (t : ℂ)) * Complex.exp (-(ε : ℂ) * ω) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [hux, hut, hd, e]
    ring
