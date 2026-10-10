-- Prove2me | solution 1 for ConleyZehnder.czIndex_zero
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T23:31:21.065502+00:00
-- url     : https://prove2.me/submissions/6b8bc52c-c5da-43b9-a770-c60826511434

import Theorems.Thm_ConleyZehnder_czIndex_two_mul_eq_neg_signature
import Theorems.Thm_ConleyZehnder_signature_eq_zero_of_hyperbolic
import Theorems.Thm_ConleyZehnder_symplectic_cayley_isHermitian

open ConleyZehnder Matrix

theorem solution {n : ℕ} (ψ : C(unitInterval, Mat n)) (hψ : ψ ∈ SP n)
    (hcirc : ∀ s : unitInterval, 0 < (s : ℝ) → ∀ z : ℂ, ‖z‖ = 1 →
      ((ψ s).map (fun x : ℝ => (x : ℂ)) - z • 1).det ≠ 0) :
    czIndex ψ = 0 := by
  -- no `ψ(t)` has the eigenvalue `-1`
  have hneg : ∀ t, (1 + ψ t).det ≠ 0 := by
    intro t
    rcases eq_or_lt_of_le t.2.1 with h0 | hpos
    · have ht : t = 0 := Subtype.ext h0.symm
      rw [ht, hψ.2.1, show (1 : Mat n) + 1 = (2 : ℝ) • 1 by rw [two_smul], det_smul, det_one]
      positivity
    · have h := hcirc t hpos (-1) (by simp)
      have e : (ψ t).map (fun x : ℝ => (x : ℂ)) - (-1 : ℂ) • 1 =
          (1 + ψ t).map (fun x : ℝ => (x : ℂ)) := by
        ext i j
        by_cases hij : i = j
        · subst hij; simp [add_comm]
        · simp [one_apply, hij]
      have hd : ((1 + ψ t).map (fun x : ℝ => (x : ℂ))).det = ((1 + ψ t).det : ℂ) := by
        rw [show (1 + ψ t).map (fun x : ℝ => (x : ℂ)) = Complex.ofRealHom.mapMatrix (1 + ψ t)
          from rfl, ← RingHom.map_det]
        rfl
      rw [e, hd] at h
      exact_mod_cast h
  have hN := symplectic_cayley_isHermitian (ψ 1) (hψ.1 1) (by rw [add_comm]; exact hneg 1)
  have h1 := czIndex_two_mul_eq_neg_signature ψ hψ hneg hN
  have h2 := signature_eq_zero_of_hyperbolic (ψ 1) (hψ.1 1) (hcirc 1 (by norm_num)) hN
  omega
