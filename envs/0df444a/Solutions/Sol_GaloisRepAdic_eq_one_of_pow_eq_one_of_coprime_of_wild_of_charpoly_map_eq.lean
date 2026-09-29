-- Prove2me | solution 1 for GaloisRepAdic.eq_one_of_pow_eq_one_of_coprime_of_wild_of_charpoly_map_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/27cebc98-6940-5d49-b3c6-2ecc09d98b27

import Definitions.Def_GaloisRep_Adic
import Theorems.Thm_GaloisRepAdic_exists_pow_prime_pow_eq_one_of_wild
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Data.Int.GCD
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_eq_one_of_pow_eq_one_of_coprime_of_wild_of_charpoly_map_eq

set_option autoImplicit false
open Polynomial

open scoped TensorProduct

theorem solution
    {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (ρ : GaloisRepAdic A)
    {p : ℕ} (hp : p.Prime) (hpA : (p : A) ∈ IsLocalRing.maximalIdeal A) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hwild : ∀ z : AlgebraicClosure ℚ, z ≠ 0 → σ z * z⁻¹ - 1 ∈ P.nonunits)
    {B : Type} [CommRing B] [IsDomain B] (j : A →+* B) (hj : Function.Injective j)
    (a : Bˣ) (ha : (LinearMap.charpoly (ρ.ρ σ)).map j = (X - C ((a : Bˣ) : B)) * (X - C (((a⁻¹ : Bˣ) : B))))
    {n : ℕ} (hn : n.Coprime q) (han : a ^ n = 1) :
    a = 1 := by
  classical
  obtain ⟨k, hk⟩ := GaloisRepAdic.exists_pow_prime_pow_eq_one_of_wild ρ hp hpA hq hqp P hP hwild
  letI : Algebra A B := j.toAlgebra

  have hchar : ((ρ.ρ σ).baseChange B).charpoly = (X - C ((a : Bˣ) : B)) * (X - C (((a⁻¹ : Bˣ) : B))) := by
    rw [LinearMap.charpoly_baseChange]
    exact ha
  have hroot : ((ρ.ρ σ).baseChange B).charpoly.IsRoot ((a : Bˣ) : B) := by
    rw [hchar, IsRoot.def, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul]
  have hev : Module.End.HasEigenvalue ((ρ.ρ σ).baseChange B) ((a : Bˣ) : B) :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly ((ρ.ρ σ).baseChange B) _).mpr hroot
  obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
  have hfpow : ((ρ.ρ σ).baseChange B) ^ q ^ k = 1 := by
    rw [← LinearMap.baseChange_pow, hk, LinearMap.baseChange_one]
  have h1 : (((a : Bˣ) : B) ^ q ^ k) • v = v := by
    rw [← hv.pow_apply, hfpow, Module.End.one_apply]
  have hak : ((a : Bˣ) : B) ^ q ^ k = 1 := by
    have h2 := sub_smul (((a : Bˣ) : B) ^ q ^ k) (1 : B) v
    rw [h1, one_smul, sub_self] at h2
    rcases smul_eq_zero.mp h2 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hv.2
  have haku : a ^ q ^ k = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hak, Units.val_one])
  have hg : n.gcd (q ^ k) = 1 := Nat.Coprime.pow_right k hn
  have h := (pow_gcd_eq_one (a := a) (m := n) (n := q ^ k)).mpr ⟨han, haku⟩
  rwa [hg, pow_one] at h

end S_GaloisRepAdic_eq_one_of_pow_eq_one_of_coprime_of_wild_of_charpoly_map_eq
end P2MW
export P2MW.S_GaloisRepAdic_eq_one_of_pow_eq_one_of_coprime_of_wild_of_charpoly_map_eq (solution)
