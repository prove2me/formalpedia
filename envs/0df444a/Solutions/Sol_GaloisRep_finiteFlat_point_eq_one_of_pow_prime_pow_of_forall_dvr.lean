-- Prove2me | solution 1 for GaloisRep.finiteFlat_point_eq_one_of_pow_prime_pow_of_forall_dvr
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/25da8b7c-f667-5ea2-8092-19748c327781

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_ValuationSubring_exists_dvr_subring_of_forall_mem_decompositionSubgroup
import Theorems.Thm_AlgHom_liftEquiv_symm_withConv_mul
import Theorems.Thm_HopfAlgebra_isUnit_withConv_algHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_finiteFlat_point_eq_one_of_pow_prime_pow_of_forall_dvr

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 800000

open scoped TensorProduct
open WithConv

namespace CTc

theorem algebraMap_rat_mem_of_den_coprime (ℓ : ℕ) [Fact ℓ.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (q : ℚ) (hq : q.den.Coprime ℓ) : algebraMap ℚ (AlgebraicClosure ℚ) q ∈ A := by
  rw [← ValuationSubring.valuation_le_one_iff]
  have hℓ : A.valuation ((ℓ : ℕ) : AlgebraicClosure ℚ) < 1 := (ValuationSubring.mem_nonunits_iff A).mp hA
  have hint : ∀ n : ℤ, A.valuation (n : AlgebraicClosure ℚ) ≤ 1 := fun n => by
    rw [ValuationSubring.valuation_le_one_iff]
    exact intCast_mem A.toSubring n
  have hnat : ∀ n : ℕ, A.valuation (n : AlgebraicClosure ℚ) ≤ 1 := fun n => by
    rw [ValuationSubring.valuation_le_one_iff]
    exact natCast_mem A.toSubring n
  have hden : A.valuation (q.den : AlgebraicClosure ℚ) = 1 := by
    apply le_antisymm (hnat q.den)
    by_contra hlt
    rw [not_le] at hlt
    have hg : Int.gcd (q.den : ℤ) (ℓ : ℤ) = 1 := by
      rw [Int.gcd_natCast_natCast]; exact hq
    have hab : (q.den : ℤ) * Int.gcdA (q.den : ℤ) (ℓ : ℤ) + (ℓ : ℤ) * Int.gcdB (q.den : ℤ) (ℓ : ℤ) = 1 := by
      have := Int.gcd_eq_gcd_ab (q.den : ℤ) (ℓ : ℤ)
      rw [hg] at this
      exact_mod_cast this.symm
    have hcast : (q.den : AlgebraicClosure ℚ) * (Int.gcdA (q.den : ℤ) (ℓ : ℤ) : AlgebraicClosure ℚ) +
        ((ℓ : ℕ) : AlgebraicClosure ℚ) * (Int.gcdB (q.den : ℤ) (ℓ : ℤ) : AlgebraicClosure ℚ) = 1 := by
      exact_mod_cast congrArg (fun z : ℤ => (z : AlgebraicClosure ℚ)) hab
    have h1 : A.valuation (1 : AlgebraicClosure ℚ) < 1 := by
      rw [← hcast]
      refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
      · rw [Valuation.map_mul]
        calc A.valuation (q.den : AlgebraicClosure ℚ) * A.valuation (Int.gcdA (q.den : ℤ) (ℓ : ℤ) : AlgebraicClosure ℚ)
            ≤ A.valuation (q.den : AlgebraicClosure ℚ) * 1 := by gcongr; exact hint _
          _ < 1 := by rw [mul_one]; exact hlt
      · rw [Valuation.map_mul]
        calc A.valuation ((ℓ : ℕ) : AlgebraicClosure ℚ) * A.valuation (Int.gcdB (q.den : ℤ) (ℓ : ℤ) : AlgebraicClosure ℚ)
            ≤ A.valuation ((ℓ : ℕ) : AlgebraicClosure ℚ) * 1 := by gcongr; exact hint _
          _ < 1 := by rw [mul_one]; exact hℓ
    simp at h1
  have hq' : algebraMap ℚ (AlgebraicClosure ℚ) q = (q.num : AlgebraicClosure ℚ) / (q.den : AlgebraicClosure ℚ) := by
    rw [eq_ratCast, Rat.cast_def]
  rw [hq', map_div₀, hden, div_one]
  exact hint q.num

theorem algebraMap_ratLocalizedAt_mem (ℓ : ℕ) [Fact ℓ.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ) (r : GaloisRep.ratLocalizedAt ℓ) :
    algebraMap (GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ) r ∈ A :=
  algebraMap_rat_mem_of_den_coprime ℓ A hA r r.2

theorem apply_mem_valuationSubring (ℓ : ℕ) [Fact ℓ.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (H : Type) [CommRing H] [Algebra (GaloisRep.ratLocalizedAt ℓ) H] [Module.Finite (GaloisRep.ratLocalizedAt ℓ) H]
    (f : H →ₐ[GaloisRep.ratLocalizedAt ℓ] AlgebraicClosure ℚ) (h : H) : f h ∈ A := by
  have h1 : IsIntegral (GaloisRep.ratLocalizedAt ℓ) (f h) := (Algebra.IsIntegral.isIntegral h).map f
  obtain ⟨p, hpm, hpe⟩ := h1
  let ψ : GaloisRep.ratLocalizedAt ℓ →+* A :=
    { toFun := fun r => ⟨algebraMap (GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ) r,
        algebraMap_ratLocalizedAt_mem ℓ A hA r⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  have hψ : (algebraMap A (AlgebraicClosure ℚ)).comp ψ = algebraMap (GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ) :=
    RingHom.ext fun r => rfl
  have h2 : IsIntegral A (f h) := by
    refine ⟨p.map ψ, hpm.map ψ, ?_⟩
    rw [Polynomial.eval₂_map, hψ]
    exact hpe
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
  rw [← hy]; exact y.2

section Conv
variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C] [Bialgebra R C]
  [Algebra R A] [Algebra R B]

def postComp (g : A →ₐ[R] B) (f : WithConv (C →ₐ[R] A)) : WithConv (C →ₐ[R] B) :=
  toConv (g.comp f.ofConv)

theorem postComp_mul (g : A →ₐ[R] B) (f₁ f₂ : WithConv (C →ₐ[R] A)) :
    postComp g (f₁ * f₂) = postComp g f₁ * postComp g f₂ := by
  unfold postComp
  rw [AlgHom.comp_convMul_distrib, WithConv.toConv_ofConv]

theorem postComp_one (g : A →ₐ[R] B) : postComp g (1 : WithConv (C →ₐ[R] A)) = 1 := by
  unfold postComp
  have h1 : (1 : WithConv (C →ₐ[R] A)).ofConv = (Algebra.ofId R A).comp (Bialgebra.counitAlgHom R C) := by
    rw [AlgHom.convOne_def (R := R) (A := A) (C := C), WithConv.ofConv_toConv]
  have h2 : (1 : WithConv (C →ₐ[R] B)) = toConv ((Algebra.ofId R B).comp (Bialgebra.counitAlgHom R C)) :=
    AlgHom.convOne_def
  rw [h1, h2]
  congr 1
  ext c
  simp [Algebra.ofId_apply]

theorem postComp_pow (g : A →ₐ[R] B) (f : WithConv (C →ₐ[R] A)) (n : ℕ) :
    postComp g (f ^ n) = postComp g f ^ n := by
  induction n with
  | zero => exact postComp_one g
  | succ n ih =>
      change postComp g (f ^ n * f) = postComp g f ^ n * postComp g f
      rw [postComp_mul, ih]

theorem postComp_injective (g : A →ₐ[R] B) (hg : Function.Injective g) :
    Function.Injective (postComp (C := C) g) := by
  intro f₁ f₂ h
  have h' := congrArg WithConv.ofConv h
  unfold postComp at h'
  rw [WithConv.ofConv_toConv, WithConv.ofConv_toConv] at h'
  have : f₁.ofConv = f₂.ofConv := AlgHom.ext fun c => hg (by simpa using congrArg (fun φ => φ c) h')
  simpa using congrArg WithConv.toConv this

end Conv

end CTc

open CTc in
theorem solution
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ 2)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (hR : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O], Irreducible (ℓ : O) →
      ∀ (H' : Type) [CommRing H'] [HopfAlgebra O H'] [Module.Finite O H'] [Module.Flat O H'] [Coalgebra.IsCocomm O H']
        (x : WithConv (H' →ₐ[O] O)),
        (∀ h : H', x h - algebraMap O O (Coalgebra.counit h) ∈ IsLocalRing.maximalIdeal O) →
        ∀ k : ℕ, x ^ ℓ ^ k = 1 → x = 1)
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt ℓ) H]
    [Module.Finite (GaloisRep.ratLocalizedAt ℓ) H] [Module.Flat (GaloisRep.ratLocalizedAt ℓ) H] [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt ℓ) H]
    (φ : WithConv (H →ₐ[GaloisRep.ratLocalizedAt ℓ] AlgebraicClosure ℚ)) (hφ : (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.decompositionSubgroup ℚ → ∀ h : H, σ (φ h) = φ h)) (hφ1 : (∀ h : H, A.valuation (φ h - algebraMap (GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ) (Coalgebra.counit h)) < 1)) (k : ℕ) (hφk : φ ^ ℓ ^ k = 1) :
    φ = 1 := by
  classical

  have hφapp : ∀ h : H, φ h = φ.ofConv h := fun _ => rfl

  obtain ⟨s, hs⟩ : (⊤ : Submodule (GaloisRep.ratLocalizedAt ℓ) H).FG := Module.finite_def.mp inferInstance
  let S : Finset (AlgebraicClosure ℚ) := s.image fun h => φ h
  have hS : ∀ x ∈ S, x ∈ A ∧ ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      σ ∈ A.decompositionSubgroup ℚ → σ x = x := by
    intro x hx
    obtain ⟨h, -, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨apply_mem_valuationSubring ℓ A hA H φ.ofConv h, fun σ hσ => hφ σ hσ h⟩

  obtain ⟨O, hSO, hOA, hRO, hdvr, hirr, hmax⟩ :=
    ValuationSubring.exists_dvr_subring_of_forall_mem_decompositionSubgroup ℓ A hA S hS
  haveI : IsDiscreteValuationRing O := hdvr

  have hval : ∀ h : H, φ h ∈ O := by
    intro h
    have hmem : h ∈ Submodule.span (GaloisRep.ratLocalizedAt ℓ) (s : Set H) := by rw [hs]; trivial
    induction hmem using Submodule.span_induction with
    | mem y hy => exact hSO (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨y, hy, rfl⟩))
    | zero => rw [map_zero]; exact O.zero_mem
    | add y z _ _ hy hz => rw [map_add]; exact O.add_mem hy hz
    | smul r y _ hy =>
        rw [map_smul,
          show r • φ.ofConv y = algebraMap (GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ) r * φ.ofConv y from
            Algebra.smul_def r _]
        exact O.mul_mem (hRO (r : ℚ) r.2) hy

  letI algRO : Algebra (GaloisRep.ratLocalizedAt ℓ) O := RingHom.toAlgebra
    { toFun := fun r => ⟨algebraMap (GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ) r, hRO (r : ℚ) r.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  let ι : O →ₐ[GaloisRep.ratLocalizedAt ℓ] AlgebraicClosure ℚ :=
    { toFun := fun o => (o : AlgebraicClosure ℚ)
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  have hι : Function.Injective ι := fun a b h => Subtype.ext h

  let φO : H →ₐ[GaloisRep.ratLocalizedAt ℓ] O :=
    { toFun := fun h => ⟨φ h, hval h⟩
      map_one' := Subtype.ext (map_one φ.ofConv)
      map_mul' := fun a b => Subtype.ext (map_mul φ.ofConv a b)
      map_zero' := Subtype.ext (map_zero φ.ofConv)
      map_add' := fun a b => Subtype.ext (map_add φ.ofConv a b)
      commutes' := fun r => Subtype.ext (φ.ofConv.commutes r) }
  have hφO : postComp ι (toConv φO) = φ := by
    show toConv (ι.comp (toConv φO).ofConv) = φ
    rw [WithConv.ofConv_toConv, ← WithConv.toConv_ofConv φ]
    exact congrArg WithConv.toConv (AlgHom.ext fun h => rfl)
  have hφOk : (toConv φO) ^ ℓ ^ k = 1 := by
    apply postComp_injective ι hι
    rw [postComp_pow, hφO, hφk, postComp_one]

  let E := AlgHom.liftEquiv (GaloisRep.ratLocalizedAt ℓ) O H O
  let x : WithConv (O ⊗[GaloisRep.ratLocalizedAt ℓ] H →ₐ[O] O) := toConv (E φO)
  let Es : WithConv (O ⊗[GaloisRep.ratLocalizedAt ℓ] H →ₐ[O] O) → WithConv (H →ₐ[GaloisRep.ratLocalizedAt ℓ] O) :=
    fun y => toConv (E.symm y.ofConv)
  have hEs_mul : ∀ y z, Es (y * z) = Es y * Es z := fun y z =>
    AlgHom.liftEquiv_symm_withConv_mul (GaloisRep.ratLocalizedAt ℓ) O H O y z
  have hEs_one : Es 1 = 1 := by
    refine WithConv.ext (AlgHom.ext fun h => ?_)
    rw [AlgHom.convOne_apply]
    show (E.symm (WithConv.ofConv (1 : WithConv (O ⊗[GaloisRep.ratLocalizedAt ℓ] H →ₐ[O] O)))) h
      = algebraMap (GaloisRep.ratLocalizedAt ℓ) O (Coalgebra.counit h)
    have h1 : (E.symm (WithConv.ofConv (1 : WithConv (O ⊗[GaloisRep.ratLocalizedAt ℓ] H →ₐ[O] O)))) h
        = (WithConv.ofConv (1 : WithConv (O ⊗[GaloisRep.ratLocalizedAt ℓ] H →ₐ[O] O))) (1 ⊗ₜ h) := by
      simp [E, AlgHom.liftEquiv]
    rw [h1, AlgHom.convOne_apply]
    simp [Algebra.smul_def]
  have hEs_pow : ∀ y (n : ℕ), Es (y ^ n) = Es y ^ n := fun y n => by
    induction n with
    | zero => exact hEs_one
    | succ n ih =>
        change Es (y ^ n * y) = Es y ^ n * Es y
        rw [hEs_mul, ih]
  have hEs_x : Es x = toConv φO := by
    show toConv (E.symm (toConv (E φO)).ofConv) = toConv φO
    rw [WithConv.ofConv_toConv, Equiv.symm_apply_apply]
  have hEs_inj : Function.Injective Es := by
    intro y z h
    have h1 : E.symm y.ofConv = E.symm z.ofConv := by
      simpa [Es] using congrArg WithConv.ofConv h
    have h2 : y.ofConv = z.ofConv := E.symm.injective h1
    simpa using congrArg WithConv.toConv h2
  have hxk : x ^ ℓ ^ k = 1 := by
    apply hEs_inj
    rw [hEs_pow, hEs_x, hφOk, hEs_one]

  have hxapp : ∀ t, x t = (E φO) t := fun _ => rfl
  have hx1 : ∀ t : O ⊗[GaloisRep.ratLocalizedAt ℓ] H,
      x t - algebraMap O O (Coalgebra.counit t) ∈ IsLocalRing.maximalIdeal O := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp [hxapp]
    | add a b ha hb =>
        have : x (a + b) - algebraMap O O (Coalgebra.counit (a + b)) =
            (x a - algebraMap O O (Coalgebra.counit a)) + (x b - algebraMap O O (Coalgebra.counit b)) := by
          rw [hxapp, hxapp, hxapp, map_add, map_add, map_add]; ring
        rw [this]; exact Ideal.add_mem _ ha hb
    | tmul o h =>
        have h1 : x (o ⊗ₜ[GaloisRep.ratLocalizedAt ℓ] h) = o * φO h := by
          rw [hxapp]; simp [E, AlgHom.liftEquiv, Algebra.smul_def]
        have h2 : algebraMap O O (Coalgebra.counit (R := O) (o ⊗ₜ[GaloisRep.ratLocalizedAt ℓ] h)) =
            o * algebraMap (GaloisRep.ratLocalizedAt ℓ) O (Coalgebra.counit h) := by
          simp [Algebra.smul_def, mul_comm]
        rw [h1, h2, ← mul_sub]
        apply Ideal.mul_mem_left
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        apply hmax
        exact hφ1 h

  have hx : x = 1 := hR O hirr (O ⊗[GaloisRep.ratLocalizedAt ℓ] H) x hx1 k hxk

  have hφO1 : toConv φO = 1 := by rw [← hEs_x, hx, hEs_one]
  rw [← hφO, hφO1, postComp_one]

end S_GaloisRep_finiteFlat_point_eq_one_of_pow_prime_pow_of_forall_dvr
end P2MW
export P2MW.S_GaloisRep_finiteFlat_point_eq_one_of_pow_prime_pow_of_forall_dvr (solution)
