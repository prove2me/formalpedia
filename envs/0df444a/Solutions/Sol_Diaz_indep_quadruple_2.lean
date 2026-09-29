-- Prove2me | solution 2 for Diaz.indep_quadruple
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T09:26:52.758214+00:00
-- url     : https://prove2.me/submissions/60053877-f8f7-4afa-b704-5ae87f0032f1

/-
`Diaz.indep_quadruple` through `Diaz.indep`.

The quadratic in `v` over `L = K(u)` forces `c = 0` and `d = 0`, which is where
the hypothesis `Transcendental (K(u)) v` is used. With those two gone the
relation is `a u + b ū = 0`, and that is exactly the hypothesis of
`Diaz.indep` — `u` and `ū` are `ℚ`-independent when `u` is transcendental over
`K` and `u ū ∈ K`.

The previous accepted proof re-derived that last step by hand, building
`X² + (b/a)ρ` over `K` to contradict transcendence of `u`; that is the proof of
`Diaz.indep` again, inline, and it left the node with no theorem-level parent.
-/
import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation
import Theorems.Thm_Diaz_indep

open ComplexConjugate
open Diaz

theorem solution {K : Subfield ℂ} {u v : ℂ}
    (hu : u ≠ 0) (hv : v ≠ 0)
    (hq : u * conj u ∈ K) (hq' : v * conj v ∈ K)
    (hut : Transcendental (↥K) u)
    (hvt : Transcendental (↥(hull K u)) v)
    {a b c d : ℚ}
    (h : (a : ℂ) * u + (b : ℂ) * conj u + (c : ℂ) * v + (d : ℂ) * conj v = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  classical
  set L : Subfield ℂ := hull K u with hL
  have hKL : ∀ x, x ∈ K → x ∈ L := fun x hx =>
    Subfield.subset_closure (Or.inl hx)
  have huL : u ∈ L := Subfield.subset_closure (Or.inr rfl)
  have hcu : conj u ≠ 0 := by simpa using hu
  have hcv : conj v ≠ 0 := by simpa using hv
  have hqne : u * conj u ≠ 0 := mul_ne_zero hu hcu
  have hq'ne : v * conj v ≠ 0 := mul_ne_zero hv hcv
  -- the relation cleared of denominators
  have key : ((c : ℂ) * u) * v ^ 2
      + ((a : ℂ) * u ^ 2 + (b : ℂ) * (u * conj u)) * v
      + ((d : ℂ) * (v * conj v) * u) = 0 := by
    linear_combination (u * v) * h
  -- the three coefficients live in `L`
  have m2 : (c : ℂ) * u ∈ L := L.mul_mem (SubfieldClass.ratCast_mem L c) huL
  have m1 : (a : ℂ) * u ^ 2 + (b : ℂ) * (u * conj u) ∈ L :=
    L.add_mem (L.mul_mem (SubfieldClass.ratCast_mem L a) (L.pow_mem huL 2))
      (L.mul_mem (SubfieldClass.ratCast_mem L b) (hKL _ hq))
  have m0 : (d : ℂ) * (v * conj v) * u ∈ L :=
    L.mul_mem (L.mul_mem (SubfieldClass.ratCast_mem L d) (hKL _ hq')) huL
  set p : Polynomial (↥L) :=
    Polynomial.C ⟨_, m2⟩ * Polynomial.X ^ 2
      + Polynomial.C ⟨_, m1⟩ * Polynomial.X + Polynomial.C ⟨_, m0⟩ with hp
  have hroot : (Polynomial.aeval v) p = 0 := by
    simp only [hp, map_add, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
    exact key
  have hp0 : p = 0 := by
    by_contra hne
    exact hvt ⟨p, hne, hroot⟩
  -- read off the coefficients
  have e2 := congrArg (fun r => (Polynomial.coeff r 2 : ↥L)) hp0
  have e1 := congrArg (fun r => (Polynomial.coeff r 1 : ↥L)) hp0
  have e0 := congrArg (fun r => (Polynomial.coeff r 0 : ↥L)) hp0
  simp only [hp, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_C, Polynomial.coeff_X, Polynomial.coeff_zero, Subtype.ext_iff,
    Subfield.coe_zero, Subfield.coe_add, Subfield.coe_mul] at e2 e1 e0
  norm_num at e2 e1 e0
  have hc0 : c = 0 := e2.resolve_right hu
  have hd0 : d = 0 := (e0.resolve_right hu).resolve_right hv
  -- with `c = d = 0` the relation is `a u + b ū = 0`
  have hab : (a : ℂ) * u + (b : ℂ) * conj u = 0 := by
    rw [hc0, hd0] at h
    push_cast at h
    linear_combination h
  obtain ⟨ha0, hb0⟩ := Diaz.indep hut hq hab
  exact ⟨ha0, hb0, hc0, hd0⟩
