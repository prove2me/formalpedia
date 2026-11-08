-- Prove2me | solution 1 for CVStabilizer.weyl_mul
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:12:00.684961+00:00
-- url     : https://prove2.me/submissions/b9f64a4c-5f0f-4eb7-a60a-51b3a597976b

import Mathlib
import Definitions.Def_CVStabilizer_Weyl

open CVStabilizer in
theorem solution (n : ℕ) :
    (∀ v v' : PhaseSpace n, weyl v ∘ weyl v' =
      (fun ψ => Complex.exp (((Real.pi * omega n v v' / 2 : ℝ) : ℂ) * Complex.I) • ψ)
        ∘ weyl (v + v')) ∧
    (∀ (v : PhaseSpace n) (a b : ℝ), weyl (a • v) ∘ weyl (b • v) = weyl ((a + b) • v)) := by
  have h1 : ∀ v v' : PhaseSpace n, weyl v ∘ weyl v' =
      (fun ψ => Complex.exp (((Real.pi * omega n v v' / 2 : ℝ) : ℂ) * Complex.I) • ψ)
        ∘ weyl (v + v') := by
    intro v v'
    funext ψ x
    simp only [Function.comp_apply, weyl, Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
    have hx : x + v.1 + v'.1 = x + (v + v').1 := by rw [Prod.fst_add, add_assoc]
    rw [hx]
    congr 2
    rw [← add_mul, ← add_mul, ← Complex.ofReal_add, ← Complex.ofReal_add]
    have s1 : ∑ i, v'.2 i * (x + v.1) i = ∑ i, v'.2 i * x i + ∑ i, v.1 i * v'.2 i := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by simp only [Pi.add_apply]; ring)
    have s2 : ∑ i, (v + v').2 i * x i = ∑ i, v.2 i * x i + ∑ i, v'.2 i * x i := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by simp only [Prod.snd_add, Pi.add_apply]; ring)
    have s3 : ∑ i, (v + v').1 i * (v + v').2 i = ∑ i, v.1 i * v.2 i + ∑ i, v'.1 i * v'.2 i
        + (∑ i, v.1 i * v'.2 i + ∑ i, v'.1 i * v.2 i) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by
        simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]; ring)
    have s4 : omega n v v' = ∑ i, v.1 i * v'.2 i - ∑ i, v'.1 i * v.2 i := by
      rw [omega_apply, Finset.sum_sub_distrib]
    rw [s1, s2, s3, s4]
    ring
  refine ⟨h1, fun v a b => ?_⟩
  have h0 : omega n (a • v) (b • v) = 0 := by
    rw [omega_apply]
    apply Finset.sum_eq_zero
    intro i _
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h1 (a • v) (b • v), ← add_smul, h0]
  funext ψ
  simp
