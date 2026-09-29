-- Prove2me | solution 1 for DoubleComplex.subsingleton_HTot_of_colContraction
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/60ca7c41-16c5-51cf-a47a-e1bc66821d56

import Mathlib
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import Definitions.Def_AlgebraicGeometry_BoundedCochainTensor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DoubleComplex_subsingleton_HTot_of_colContraction

set_option autoImplicit false

universe u

namespace ColContraction

open DoubleComplex

set_option maxHeartbeats 3200000 in
theorem main
    {R : Type u} [CommRing R] (T : DoubleComplex.Bounded R)
    (s : ∀ p q : ℕ, T.C p (q + 1) →ₗ[R] T.C p q)
    (h0 : ∀ (p : ℕ) (x : T.C p 0), s p 0 (T.dV p 0 x) = x)
    (hs : ∀ (p q : ℕ) (x : T.C p (q + 1)), s p (q + 1) (T.dV p (q + 1) x) + T.dV p q (s p q x) = x)
    (hsH : ∀ (p q : ℕ) (x : T.C p (q + 1)), s (p + 1) q (T.dH p (q + 1) x) = T.dH p q (s p q x))
    (n : ℕ) :
    Subsingleton (DoubleComplex.HTot T n) := by
  classical
  have hsq : ∀ p' : ℕ, ((-1 : ℤ) ^ p') * (-1) ^ p' = 1 := fun p' => by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [Submodule.Quotient.mk_eq_zero]
  obtain ⟨c, hc⟩ := c
  have hc' : ∀ i : Diag (n + 1), dTot T n c i = 0 := fun i => by rw [LinearMap.mem_ker.mp hc]; rfl
  cases n with
  | zero =>
    change (⟨c, hc⟩ : LinearMap.ker (dTot T 0)) ∈ (⊥ : Submodule R _)
    rw [Submodule.mem_bot]
    apply Subtype.ext
    funext i
    obtain ⟨⟨p, q⟩, h⟩ := i
    have hp : p = 0 := by omega
    have hq : q = 0 := by omega
    subst hp hq
    have h1 : T.dV 0 0 (c ⟨(0, 0), h⟩) = 0 := by
      have := hc' ⟨(0, 1), by omega⟩
      rw [dTot_apply_zero_succ] at this
      exact this
    change c ⟨(0, 0), h⟩ = 0
    rw [← h0 0 (c ⟨(0, 0), h⟩), h1, map_zero]
  | succ m =>
    change (⟨c, hc⟩ : LinearMap.ker (dTot T (m + 1))) ∈ (LinearMap.range (dTot T m)).comap (LinearMap.ker (dTot T (m + 1))).subtype
    rw [Submodule.mem_comap, LinearMap.mem_range]
    let b : Tot T m := fun i => ((-1 : ℤ) ^ i.1.1) • s i.1.1 i.1.2 (c ⟨(i.1.1, i.1.2 + 1), by have := i.2; omega⟩)
    refine ⟨b, ?_⟩
    change dTot T m b = c
    funext i
    obtain ⟨⟨pp, q⟩, h⟩ := i
    match pp, q, h with
    | 0, 0, h => exact absurd h (by omega)
    | 0, q' + 1, h =>
      rw [dTot_apply_zero_succ]
      change T.dV 0 q' (((-1 : ℤ) ^ 0) • s 0 q' (c ⟨(0, q' + 1), by omega⟩)) = c ⟨(0, q' + 1), h⟩
      rw [pow_zero, one_smul]
      have hcoc := hc' ⟨(0, q' + 2), by omega⟩
      rw [dTot_apply_zero_succ] at hcoc
      have e1 : c ⟨(0, q' + 1), (by omega : 0 + (q' + 1) = m + 1)⟩ = c ⟨(0, q' + 1), h⟩ := rfl
      rw [e1] at hcoc
      have := hs 0 q' (c ⟨(0, q' + 1), h⟩)
      rw [hcoc, map_zero, zero_add] at this
      exact this
    | p' + 1, 0, h =>
      rw [dTot_apply_succ_zero]
      change T.dH p' 0 (((-1 : ℤ) ^ p') • s p' 0 (c ⟨(p', 1), by omega⟩)) = c ⟨(p' + 1, 0), h⟩
      have hcoc := hc' ⟨(p' + 1, 1), by omega⟩
      rw [dTot_apply_succ_succ] at hcoc

      have e1 : c ⟨(p' + 1, 0), (by omega : p' + 1 + 0 = m + 1)⟩ = c ⟨(p' + 1, 0), h⟩ := rfl
      rw [e1] at hcoc
      have hdh : T.dH p' 1 (c ⟨(p', 1), by omega⟩) = ((-1 : ℤ) ^ p') • T.dV (p' + 1) 0 (c ⟨(p' + 1, 0), h⟩) := by
        have := eq_neg_of_add_eq_zero_left hcoc
        rw [this, ← neg_smul, pow_succ]
        congr 1; ring
      rw [map_zsmul, ← hsH, hdh, map_zsmul, smul_smul, hsq, one_smul, h0]
    | p' + 1, q' + 1, h =>
      rw [dTot_apply_succ_succ]
      change T.dH p' (q' + 1) (((-1 : ℤ) ^ p') • s p' (q' + 1) (c ⟨(p', q' + 2), by omega⟩)) +
          ((-1 : ℤ) ^ (p' + 1)) • T.dV (p' + 1) q' (((-1 : ℤ) ^ (p' + 1)) • s (p' + 1) q' (c ⟨(p' + 1, q' + 1), by omega⟩)) =
        c ⟨(p' + 1, q' + 1), h⟩
      have hcoc := hc' ⟨(p' + 1, q' + 2), by omega⟩
      rw [dTot_apply_succ_succ] at hcoc

      have e1 : c ⟨(p' + 1, q' + 1), (by omega : p' + 1 + (q' + 1) = m + 1)⟩ = c ⟨(p' + 1, q' + 1), h⟩ := rfl
      rw [e1] at hcoc
      have hdh : T.dH p' (q' + 2) (c ⟨(p', q' + 2), by omega⟩) =
          ((-1 : ℤ) ^ p') • T.dV (p' + 1) (q' + 1) (c ⟨(p' + 1, q' + 1), h⟩) := by
        have := eq_neg_of_add_eq_zero_left hcoc
        rw [this, ← neg_smul, pow_succ]
        congr 1; ring
      rw [map_zsmul, ← hsH, hdh, map_zsmul, smul_smul, hsq, one_smul, map_zsmul, smul_smul, hsq, one_smul]
      exact hs (p' + 1) q' (c ⟨(p' + 1, q' + 1), h⟩)

end ColContraction

theorem solution
    {R : Type u} [CommRing R] (T : DoubleComplex.Bounded R)
    (s : ∀ p q : ℕ, T.C p (q + 1) →ₗ[R] T.C p q)
    (h0 : ∀ (p : ℕ) (x : T.C p 0), s p 0 (T.dV p 0 x) = x)
    (hs : ∀ (p q : ℕ) (x : T.C p (q + 1)), s p (q + 1) (T.dV p (q + 1) x) + T.dV p q (s p q x) = x)
    (hsH : ∀ (p q : ℕ) (x : T.C p (q + 1)), s (p + 1) q (T.dH p (q + 1) x) = T.dH p q (s p q x))
    (n : ℕ) :
    Subsingleton (DoubleComplex.HTot T n) :=
  ColContraction.main T s h0 hs hsH n

end S_DoubleComplex_subsingleton_HTot_of_colContraction
end P2MW
export P2MW.S_DoubleComplex_subsingleton_HTot_of_colContraction (solution)
