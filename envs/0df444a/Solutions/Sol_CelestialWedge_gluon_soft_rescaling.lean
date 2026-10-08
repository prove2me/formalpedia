-- Prove2me | solution 1 for CelestialWedge.gluon_soft_rescaling
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T20:56:18.781646+00:00
-- url     : https://prove2.me/submissions/b9012a15-4ecf-48f3-b7f1-77e2fd5e5224

import Mathlib
import Definitions.Def_celestial_wedge_algebra
import Definitions.Def_celestial_gluon_s_algebra

set_option autoImplicit false

open CelestialWedge Complex in
theorem solution {V ι : Type*} [AddCommGroup V] [Module ℂ V] [Fintype ι]
    (br : V →ₗ[ℂ] V →ₗ[ℂ] V) (f : ι → ι → ι → ℂ) (R : ℚ → ι → ℚ → V)
    (hR : ∀ (k l n n' : ℚ) (a b : ι), InGluonSoftRange k n → InGluonSoftRange l n' →
      br (R k a n) (R l b n') =
        ∑ c, (-I * f a b c * gluonSoftCoeff k l n n') • R (k + l - 1) c (n + n'))
    (p q m n : ℚ) (a b : ι) (hpm : InWedge p m) (hqn : InWedge q n) :
    br (gluonRescale R p a m) (gluonRescale R q b n) =
      ∑ c, (-I * f a b c) • gluonRescale R (p + q - 1) c (m + n) := by
  have hk : InGluonSoftRange (3 - 2 * p) m := by
    unfold InGluonSoftRange; rw [show (3 - (3 - 2 * p)) / 2 = p by ring]; exact hpm
  have hl : InGluonSoftRange (3 - 2 * q) n := by
    unfold InGluonSoftRange; rw [show (3 - (3 - 2 * q)) / 2 = q by ring]; exact hqn
  obtain ⟨A, B, hA, hB⟩ := hpm
  obtain ⟨C, D, hC, hD⟩ := hqn
  have hcoeff : gluonSoftCoeff (3 - 2 * p) (3 - 2 * q) m n =
      ((Nat.factorial (B + D) : ℂ) / ((Nat.factorial B : ℂ) * (Nat.factorial D : ℂ))) *
      ((Nat.factorial (A + C) : ℂ) / ((Nat.factorial A : ℂ) * (Nat.factorial C : ℂ))) := by
    unfold gluonSoftCoeff
    rw [show (1 - (3 - 2 * p)) / 2 - m + ((1 - (3 - 2 * q)) / 2 - n) = ((B + D : ℕ) : ℚ) by
          push_cast; linarith,
        show (1 - (3 - 2 * p)) / 2 - m = ((B : ℕ) : ℚ) by linarith,
        show (1 - (3 - 2 * q)) / 2 - n = ((D : ℕ) : ℚ) by linarith,
        show (1 - (3 - 2 * p)) / 2 + m + ((1 - (3 - 2 * q)) / 2 + n) = ((A + C : ℕ) : ℚ) by
          push_cast; linarith,
        show (1 - (3 - 2 * p)) / 2 + m = ((A : ℕ) : ℚ) by linarith,
        show (1 - (3 - 2 * q)) / 2 + n = ((C : ℕ) : ℚ) by linarith]
    simp only [Nat.floor_natCast]
  unfold gluonRescale
  simp only [map_smul, LinearMap.smul_apply]
  rw [hR _ _ _ _ _ _ hk hl, Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [show 3 - 2 * p + (3 - 2 * q) - 1 = 3 - 2 * (p + q - 1) by ring,
    show p - m - 1 = ((B : ℕ) : ℚ) by linarith, show p + m - 1 = ((A : ℕ) : ℚ) by linarith,
    show q - n - 1 = ((D : ℕ) : ℚ) by linarith, show q + n - 1 = ((C : ℕ) : ℚ) by linarith,
    show p + q - 1 - (m + n) - 1 = ((B + D : ℕ) : ℚ) by push_cast; linarith,
    show p + q - 1 + (m + n) - 1 = ((A + C : ℕ) : ℚ) by push_cast; linarith]
  simp only [Nat.floor_natCast, smul_smul, hcoeff]
  congr 1
  have h1 : (Nat.factorial A : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero A
  have h2 : (Nat.factorial B : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero B
  have h3 : (Nat.factorial C : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero C
  have h4 : (Nat.factorial D : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero D
  field_simp
