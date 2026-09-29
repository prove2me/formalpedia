-- Prove2me | solution 1 for Diaz.indep_quadruple
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T07:27:04.022103+00:00
-- url     : https://prove2.me/submissions/feeb0e4e-e183-462b-b29f-fdad3ebf4b5a

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

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
  -- `a = 0`, else `u` would be algebraic over `K`
  have ha0 : a = 0 := by
    by_contra hane
    have hane' : ((a : ℂ)) ≠ 0 := by exact_mod_cast hane
    have hmem : ((b / a : ℚ) : ℂ) * (u * conj u) ∈ K :=
      K.mul_mem (SubfieldClass.ratCast_mem K _) hq
    refine hut ⟨Polynomial.X ^ 2 + Polynomial.C ⟨_, hmem⟩, ?_, ?_⟩
    · intro hz
      have := congrArg (fun r => (Polynomial.coeff r 2 : ↥K)) hz
      simp at this
    · simp only [map_add, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
      show u ^ 2 + ((b / a : ℚ) : ℂ) * (u * conj u) = 0
      push_cast
      field_simp
      linear_combination e1
  have hb0 : b = 0 := by
    subst ha0
    push_cast at e1
    have hbz : (b : ℂ) * (u * conj u) = 0 := by linear_combination e1
    rcases mul_eq_zero.1 hbz with hz | hz
    · exact_mod_cast hz
    · exact absurd hz hqne
  exact ⟨ha0, hb0, hc0, hd0⟩

