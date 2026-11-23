-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx1.psd_kernel_hermitian
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:55.450814+00:00
-- url     : https://prove2.me/submissions/6d300242-3c15-43a3-aac7-102b0ce03168

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PsdFormConjRewrite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexOrder ComplexConjugate nonZeroDivisors
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx1
variable {α : Type}
namespace Formalism.FourierDecayAlt.P.Jx1
theorem _root_.solution (F : Finset α) (k : α → α → ℂ) (h : A5.IsPSD F k) :
    ∀ x ∈ F, ∀ y ∈ F, k y x = conj (k x y) := by
  classical
  intro x hx y hy
  set B : (α → ℂ) → (α → ℂ) → ℂ := fun a b => ∑ u ∈ F, ∑ v ∈ F, a u * conj (b v) * k u v with hB
  have hS : ∀ a, (B a a).im = 0 := fun a => (h a).1
  have hexp : ∀ a b, B (a + b) (a + b) = B a a + B b b + (B a b + B b a) := by
    intro a b
    simp only [hB, Pi.add_apply, map_add, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    ring
  have hpol : ∀ a b, (B a b + B b a).im = 0 := by
    intro a b
    have h0 := hS (a + b)
    rw [hexp, Complex.add_im, Complex.add_im, hS a, hS b] at h0
    simpa using h0
  have hsc1 : ∀ (c : ℂ) a b, B (c • a) b = c * B a b := by
    intro c a b
    simp only [hB, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    ring
  have hsc2 : ∀ (c : ℂ) a b, B a (c • b) = conj c * B a b := by
    intro c a b
    simp only [hB, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    ring
  have hBe : ∀ p q, p ∈ F → q ∈ F →
      B (fun u => if u = p then 1 else 0) (fun u => if u = q then 1 else 0) = k p q := by
    intro p q hp hq
    simp [hB, apply_ite (starRingEnd ℂ), ite_mul, hp, hq]
  have h1 := hpol (fun u => if u = x then 1 else 0) (fun u => if u = y then 1 else 0)
  have h2 := hpol (fun u => if u = x then 1 else 0) (Complex.I • fun u => if u = y then 1 else 0)
  rw [hsc2, hsc1] at h2
  rw [hBe x y hx hy, hBe y x hy hx] at h1 h2
  apply Complex.ext <;> simp [Complex.mul_im] at h1 h2 ⊢ <;> linarith
end Formalism.FourierDecayAlt.P.Jx1
