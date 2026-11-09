-- Prove2me | solution 1 for CVStabilizer.logical_weyl_relations
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T10:32:13.828839+00:00
-- url     : https://prove2.me/submissions/4f21db82-71c6-4b53-ade3-513889f4cff6

import Mathlib
import Definitions.Def_CVStabilizer_Weyl

namespace Aux_CVStab_weyl

open CVStabilizer

theorem comm {n : ℕ} (a b : PhaseSpace n) (ψ : (Fin n → ℝ) → ℂ) :
    weyl a (weyl b ψ) =
      Complex.exp (((Real.pi * omega n a b : ℝ) : ℂ) * Complex.I) • weyl b (weyl a ψ) := by
  funext y
  simp only [weyl, Pi.smul_apply, smul_eq_mul, Pi.add_apply]
  rw [add_right_comm y b.1 a.1]
  have hreal : Real.pi * ((∑ i, a.2 i * y i) + (∑ i, a.1 i * a.2 i) / 2) +
      Real.pi * ((∑ i, b.2 i * (y i + a.1 i)) + (∑ i, b.1 i * b.2 i) / 2)
      = Real.pi * omega n a b + (Real.pi * ((∑ i, b.2 i * y i) + (∑ i, b.1 i * b.2 i) / 2) +
        Real.pi * ((∑ i, a.2 i * (y i + b.1 i)) + (∑ i, a.1 i * a.2 i) / 2)) := by
    simp only [omega_apply, mul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have s1 : ∑ i, b.2 i * a.1 i = ∑ i, a.1 i * b.2 i :=
      Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    have s2 : ∑ i, a.2 i * b.1 i = ∑ i, b.1 i * a.2 i :=
      Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    rw [s1, s2]
    ring
  have key : Complex.exp (((Real.pi * ((∑ i, a.2 i * y i) + (∑ i, a.1 i * a.2 i) / 2) : ℝ) : ℂ)
        * Complex.I) *
      Complex.exp (((Real.pi * ((∑ i, b.2 i * (y i + a.1 i)) + (∑ i, b.1 i * b.2 i) / 2) : ℝ) : ℂ)
        * Complex.I)
      = Complex.exp (((Real.pi * omega n a b : ℝ) : ℂ) * Complex.I) *
        (Complex.exp (((Real.pi * ((∑ i, b.2 i * y i) + (∑ i, b.1 i * b.2 i) / 2) : ℝ) : ℂ)
          * Complex.I) *
        Complex.exp (((Real.pi * ((∑ i, a.2 i * (y i + b.1 i)) + (∑ i, a.1 i * a.2 i) / 2) : ℝ) : ℂ)
          * Complex.I)) := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, ← add_mul, ← add_mul, ← add_mul,
      ← Complex.ofReal_add, ← Complex.ofReal_add, ← Complex.ofReal_add, hreal]
  linear_combination ψ (y + a.1 + b.1) * key

theorem hom {n : ℕ} (s t : ℝ) (a b : PhaseSpace n) :
    omega n (s • a) (t • b) = s * t * omega n a b := by
  rw [LinearMap.map_smul₂, LinearMap.map_smul, smul_eq_mul, smul_eq_mul]
  ring

end Aux_CVStab_weyl

open CVStabilizer in
theorem solution (n m : ℕ) (x z : Fin m → PhaseSpace n)
    (hxx : ∀ i j, omega n (x i) (x j) = 0) (hzz : ∀ i j, omega n (z i) (z j) = 0)
    (hxz : ∀ i j, omega n (x i) (z j) = if i = j then 1 else 0) :
    ∀ (i j : Fin m) (s t : ℝ),
      weyl (s • x i) ∘ weyl (t • x j) = weyl (t • x j) ∘ weyl (s • x i) ∧
      weyl (s • z i) ∘ weyl (t • z j) = weyl (t • z j) ∘ weyl (s • z i) ∧
      weyl (s • x i) ∘ weyl (t • z j) =
        (fun ψ => Complex.exp
            (((Real.pi * s * t * (if i = j then 1 else 0) : ℝ) : ℂ) * Complex.I) • ψ)
          ∘ weyl (t • z j) ∘ weyl (s • x i) := by
  intro i j s t
  refine ⟨?_, ?_, ?_⟩
  · funext ψ
    simp only [Function.comp_apply]
    rw [Aux_CVStab_weyl.comm, Aux_CVStab_weyl.hom, hxx]
    simp
  · funext ψ
    simp only [Function.comp_apply]
    rw [Aux_CVStab_weyl.comm, Aux_CVStab_weyl.hom, hzz]
    simp
  · funext ψ
    simp only [Function.comp_apply]
    rw [Aux_CVStab_weyl.comm, Aux_CVStab_weyl.hom, hxz]
    rw [show Real.pi * (s * t * (if i = j then (1:ℝ) else 0))
      = Real.pi * s * t * (if i = j then 1 else 0) by ring]
