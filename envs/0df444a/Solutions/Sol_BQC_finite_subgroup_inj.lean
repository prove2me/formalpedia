-- Prove2me | solution 1 for BQC.finite_subgroup_inj
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T01:05:58.822993+00:00
-- url     : https://prove2.me/submissions/dcb34d1d-7220-4471-bd8e-d247318c2cfd

import Mathlib
import Definitions.Def_BQC_alg
import Definitions.Def_BQC_tor
open BQC

theorem solution {d : Nat} {Cry Ph : Type*} [Group Cry] [Group Ph] [Fintype Ph]
    (W : CryWorld d Cry Ph) {K : Type} [Group K] [Fintype K] (f : K →* Cry)
    (finj : ∀ x y : K, f x = f y → x = y) (x y : K)
    (hxy : W.proj (f x) = W.proj (f y)) : x = y := by
  have hk : W.proj (f (x⁻¹ * y)) = 1 := by
    rw [map_mul, map_inv, map_mul, map_inv, hxy, inv_mul_cancel]
  obtain ⟨z, hz⟩ := (W.ex _).1 hk
  have hpow : (x⁻¹ * y) ^ Fintype.card K = 1 := pow_card_eq_one
  have h1 : W.inj (Multiplicative.ofAdd z) ^ Fintype.card K = W.inj 1 := by
    rw [hz, ← map_pow, hpow, map_one, map_one]
  rw [← map_pow] at h1
  have h2 := W.inj_inj _ _ h1
  have h3 : (Fintype.card K) • z = 0 := by
    have := congrArg Multiplicative.toAdd h2
    simpa [toAdd_pow] using this
  have h4 : z = 0 := by
    have hc : (Fintype.card K) ≠ 0 := Fintype.card_ne_zero
    funext i
    have := congrFun h3 i
    simp only [Pi.smul_apply, nsmul_eq_mul, Pi.zero_apply] at this
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (by exact_mod_cast h) hc
    · simpa using h
  have h5 : f (x⁻¹ * y) = f 1 := by
    rw [← hz, h4, map_one]; simp
  have := finj _ _ h5
  rw [inv_mul_eq_one] at this
  exact this
