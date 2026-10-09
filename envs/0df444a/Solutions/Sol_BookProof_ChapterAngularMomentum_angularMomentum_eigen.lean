-- Prove2me | solution 1 for BookProof.ChapterAngularMomentum.angularMomentum_eigen
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T16:37:29.491781+00:00
-- url     : https://prove2.me/submissions/35e49ac6-3c97-4c4b-a99e-3efea6b72cd3

-- Generated from ChapterAngularMomentum.lean — solution of BookProof.ChapterAngularMomentum.angularMomentum_eigen
import Mathlib
import Definitions.Def_ChapterAngularMomentum
import Theorems.Thm_BookProof_ChapterAngularMomentum_fderiv_rotationVector
open BookProof.ChapterAngularMomentum




open Complex

set_option maxHeartbeats 1000000 in
theorem solution {u : ℂ → ℂ} {μ : ℝ} {z : ℂ}
    (hdiff : DifferentiableAt ℝ u z)
    (hequiv : ∀ t : ℝ, u (Complex.exp ((t : ℂ) * Complex.I) * z)
      = Complex.exp ((μ : ℂ) * (t : ℂ) * Complex.I) * u z) :
    -Complex.I * (z.re * fderiv ℝ u z Complex.I - z.im * fderiv ℝ u z 1) = (μ : ℂ) * u z := by

  -- the rotation path and its velocity at `t = 0`
  have hpath : HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * Complex.I) * z)
      (Complex.I * z) 0 := by
    have h : HasDerivAt (fun s : ℝ => ((s : ℂ) * Complex.I)) Complex.I (0 : ℝ) := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const Complex.I
    have hexp : HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * Complex.I))
        (Complex.exp (((0 : ℝ) : ℂ) * Complex.I) * Complex.I) 0 := h.cexp
    simpa using hexp.mul_const z
  -- the derivative of `t ↦ u(e^{it} z)` at `0`, computed by the chain rule
  have hchain : HasDerivAt (fun s : ℝ => u (Complex.exp ((s : ℂ) * Complex.I) * z))
      (fderiv ℝ u z (Complex.I * z)) 0 := by
    have hu : HasFDerivAt u (fderiv ℝ u z)
        ((fun s : ℝ => Complex.exp ((s : ℂ) * Complex.I) * z) 0) := by
      simpa using hdiff.hasFDerivAt
    have h := HasFDerivAt.comp_hasDerivAt (0 : ℝ) hu hpath
    exact h
  -- the same derivative, computed from the equivariance
  have hphase : HasDerivAt (fun s : ℝ => Complex.exp ((μ : ℂ) * (s : ℂ) * Complex.I) * u z)
      (Complex.I * (μ : ℂ) * u z) 0 := by
    have h : HasDerivAt (fun s : ℝ => (μ : ℂ) * (s : ℂ) * Complex.I)
        ((μ : ℂ) * Complex.I) (0 : ℝ) := by
      have h0 : HasDerivAt (fun s : ℝ => ((s : ℂ))) 1 (0 : ℝ) :=
        Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))
      simpa [mul_comm, mul_assoc] using ((h0.const_mul (μ : ℂ)).mul_const Complex.I)
    have hexp := h.cexp
    have := hexp.mul_const (u z)
    simpa [mul_comm, mul_assoc, mul_left_comm] using this
  have hfun : (fun s : ℝ => u (Complex.exp ((s : ℂ) * Complex.I) * z))
      = fun s : ℝ => Complex.exp ((μ : ℂ) * (s : ℂ) * Complex.I) * u z := by
    funext s; exact hequiv s
  rw [hfun] at hchain
  have hval : fderiv ℝ u z (Complex.I * z) = Complex.I * (μ : ℂ) * u z :=
    hchain.unique hphase
  rw [← fderiv_rotationVector u z, hval]
  have : -Complex.I * (Complex.I * (μ : ℂ) * u z) = (μ : ℂ) * u z := by
    rw [show -Complex.I * (Complex.I * (μ : ℂ) * u z)
      = (-(Complex.I * Complex.I)) * ((μ : ℂ) * u z) by ring, Complex.I_mul_I]
    ring
  exact this
