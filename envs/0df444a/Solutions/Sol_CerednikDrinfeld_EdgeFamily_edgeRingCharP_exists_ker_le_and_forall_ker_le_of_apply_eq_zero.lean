-- Prove2me | solution 1 for CerednikDrinfeld.EdgeFamily.edgeRingCharP.exists_ker_le_and_forall_ker_le_of_apply_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/0e80e6c8-cc7f-5dd5-aa58-015325dad92b

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_CerednikDrinfeld_EdgeFamilyConstants
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_EdgeFamily_edgeRingCharP_exists_ker_le_and_forall_ker_le_of_apply_eq_zero

set_option autoImplicit false

open CerednikDrinfeld
open Polynomial

namespace Ws28H7

variable (p : ℕ) [hp : Fact p.Prime] (k : Type) [Field k]

noncomputable abbrev d : k[X] := X ^ (p - 1) - 1

theorem d_ne_zero : d p k ≠ 0 := by
  intro h
  have hp1 : p - 1 ≠ 0 := by have := hp.out.two_le; omega
  have h2 : (X ^ (p - 1) - 1 : k[X]).eval 0 = 0 := by
    have : (X ^ (p - 1) - 1 : k[X]) = 0 := h
    rw [this, eval_zero]
  rw [eval_sub, eval_pow, eval_X, eval_one, zero_pow hp1, zero_sub, neg_eq_zero] at h2
  exact one_ne_zero h2

abbrev A : Type := Localization.Away (d p k)

scoped instance : IsDomain (A p k) :=
  IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors (d_ne_zero p k))

theorem isUnit_d : IsUnit (algebraMap k[X] (A p k) X ^ (p - 1) - 1) := by
  have : IsUnit (algebraMap k[X] (A p k) (X ^ (p - 1) - 1)) := IsLocalization.Away.algebraMap_isUnit (S := A p k) (d p k)
  rwa [map_sub, map_pow, map_one] at this

theorem isUnit_zero_pow_sub_one : IsUnit ((0 : A p k) ^ (p - 1) - 1) := by
  have hp1 : p - 1 ≠ 0 := by have := hp.out.two_le; omega
  rw [zero_pow hp1, zero_sub]; exact isUnit_one.neg

noncomputable def ptξ : (FormalOmega.chartE k (0 : k) p).obj (A p k) :=
  ⟨(algebraMap k[X] (A p k) X, 0), by rw [mul_zero, map_zero], isUnit_d p k, isUnit_zero_pow_sub_one p k⟩

noncomputable def ptη : (FormalOmega.chartE k (0 : k) p).obj (A p k) :=
  ⟨(0, algebraMap k[X] (A p k) X), by rw [zero_mul, map_zero], isUnit_zero_pow_sub_one p k, isUnit_d p k⟩

noncomputable def gξ : EdgeFamily.edgeRingCharP p k →ₐ[k] A p k := FormalOmega.chartERing.lift (ptξ p k)
noncomputable def gη : EdgeFamily.edgeRingCharP p k →ₐ[k] A p k := FormalOmega.chartERing.lift (ptη p k)

theorem ker_gξ_le {κ' : Type} [Field κ'] (f' : EdgeFamily.edgeRingCharP p k →+* κ')
    (hη : f' (EdgeFamily.edgeRingCharP.η p k) = 0) :
    RingHom.ker (gξ p k : EdgeFamily.edgeRingCharP p k →+* A p k) ≤ RingHom.ker f' := by
  letI : Algebra k κ' := (f'.comp (algebraMap k (EdgeFamily.edgeRingCharP p k))).toAlgebra
  let f'A : EdgeFamily.edgeRingCharP p k →ₐ[k] κ' := { f' with commutes' := fun r => rfl }

  have hu : IsUnit (f' (EdgeFamily.edgeRingCharP.ξ p k) ^ (p - 1) - 1) :=
    (FormalOmega.chartERing.corepEquiv k (0 : k) p κ' f'A).2.2.1

  have hψu : ∀ y : Submonoid.powers (d p k), IsUnit ((Polynomial.aeval (R := k) (f' (EdgeFamily.edgeRingCharP.ξ p k))) y) := by
    rintro ⟨_, n, rfl⟩
    rw [map_pow]
    refine IsUnit.pow n ?_
    have : (Polynomial.aeval (R := k) (f' (EdgeFamily.edgeRingCharP.ξ p k))) (d p k)
        = f' (EdgeFamily.edgeRingCharP.ξ p k) ^ (p - 1) - 1 := by
      show (Polynomial.aeval (R := k) _) (X ^ (p - 1) - 1) = _
      rw [map_sub, map_pow, map_one, Polynomial.aeval_X]
    rw [this]; exact hu
  let ψ : A p k →ₐ[k] κ' := IsLocalization.liftAlgHom (M := Submonoid.powers (d p k)) hψu

  have hcomp : ψ.comp (gξ p k) = f'A := by
    apply (FormalOmega.chartERing.corepEquiv k (0 : k) p κ').injective
    apply Subtype.ext
    rw [FormalOmega.chartERing.corepEquiv_apply_val, FormalOmega.chartERing.corepEquiv_apply_val]
    refine Prod.ext ?_ ?_
    · show ψ (gξ p k (FormalOmega.chartERing.ξ k (0 : k) p)) = f' (EdgeFamily.edgeRingCharP.ξ p k)
      rw [gξ, FormalOmega.chartERing.lift_ξ]
      show ψ (algebraMap k[X] (A p k) X) = _
      rw [IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
      exact Polynomial.aeval_X _
    · show ψ (gξ p k (FormalOmega.chartERing.η k (0 : k) p)) = f' (EdgeFamily.edgeRingCharP.η p k)
      rw [gξ, FormalOmega.chartERing.lift_η, hη]
      show ψ 0 = 0
      exact map_zero ψ
  intro e he
  rw [RingHom.mem_ker] at he ⊢
  have : f' e = ψ (gξ p k e) := by
    show f'A e = (ψ.comp (gξ p k)) e
    rw [hcomp]
  rw [this, show (gξ p k) e = (gξ p k : EdgeFamily.edgeRingCharP p k →+* A p k) e from rfl, he, map_zero]

theorem ker_gη_le {κ' : Type} [Field κ'] (f' : EdgeFamily.edgeRingCharP p k →+* κ')
    (hξ : f' (EdgeFamily.edgeRingCharP.ξ p k) = 0) :
    RingHom.ker (gη p k : EdgeFamily.edgeRingCharP p k →+* A p k) ≤ RingHom.ker f' := by
  letI : Algebra k κ' := (f'.comp (algebraMap k (EdgeFamily.edgeRingCharP p k))).toAlgebra
  let f'A : EdgeFamily.edgeRingCharP p k →ₐ[k] κ' := { f' with commutes' := fun r => rfl }
  have hu : IsUnit (f' (EdgeFamily.edgeRingCharP.η p k) ^ (p - 1) - 1) :=
    (FormalOmega.chartERing.corepEquiv k (0 : k) p κ' f'A).2.2.2
  have hψu : ∀ y : Submonoid.powers (d p k), IsUnit ((Polynomial.aeval (R := k) (f' (EdgeFamily.edgeRingCharP.η p k))) y) := by
    rintro ⟨_, n, rfl⟩
    rw [map_pow]
    refine IsUnit.pow n ?_
    have : (Polynomial.aeval (R := k) (f' (EdgeFamily.edgeRingCharP.η p k))) (d p k)
        = f' (EdgeFamily.edgeRingCharP.η p k) ^ (p - 1) - 1 := by
      show (Polynomial.aeval (R := k) _) (X ^ (p - 1) - 1) = _
      rw [map_sub, map_pow, map_one, Polynomial.aeval_X]
    rw [this]; exact hu
  let ψ : A p k →ₐ[k] κ' := IsLocalization.liftAlgHom (M := Submonoid.powers (d p k)) hψu
  have hcomp : ψ.comp (gη p k) = f'A := by
    apply (FormalOmega.chartERing.corepEquiv k (0 : k) p κ').injective
    apply Subtype.ext
    rw [FormalOmega.chartERing.corepEquiv_apply_val, FormalOmega.chartERing.corepEquiv_apply_val]
    refine Prod.ext ?_ ?_
    · show ψ (gη p k (FormalOmega.chartERing.ξ k (0 : k) p)) = f' (EdgeFamily.edgeRingCharP.ξ p k)
      rw [gη, FormalOmega.chartERing.lift_ξ, hξ]
      show ψ 0 = 0
      exact map_zero ψ
    · show ψ (gη p k (FormalOmega.chartERing.η k (0 : k) p)) = f' (EdgeFamily.edgeRingCharP.η p k)
      rw [gη, FormalOmega.chartERing.lift_η]
      show ψ (algebraMap k[X] (A p k) X) = _
      rw [IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
      exact Polynomial.aeval_X _
  intro e he
  rw [RingHom.mem_ker] at he ⊢
  have : f' e = ψ (gη p k e) := by
    show f'A e = (ψ.comp (gη p k)) e
    rw [hcomp]
  rw [this, show (gη p k) e = (gη p k : EdgeFamily.edgeRingCharP p k →+* A p k) e from rfl, he, map_zero]

end Ws28H7
p2m_reactivate "P2MW.S_CerednikDrinfeld_EdgeFamily_edgeRingCharP_exists_ker_le_and_forall_ker_le_of_apply_eq_zero.Ws28H7"

open Ws28H7 in
theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    (κ : Type) [Field κ] (f : EdgeFamily.edgeRingCharP p k →+* κ) :
    ∃ (L : Type) (_ : Field L) (h : EdgeFamily.edgeRingCharP p k →+* L),
      RingHom.ker h ≤ RingHom.ker f ∧
      ∀ (κ₀ : Type) [Field κ₀] (f₀ : EdgeFamily.edgeRingCharP p k →+* κ₀),
        f₀ (EdgeFamily.edgeRingCharP.ξ p k) = 0 → f₀ (EdgeFamily.edgeRingCharP.η p k) = 0 →
        RingHom.ker h ≤ RingHom.ker f₀ := by
  classical

  have hmul : f (EdgeFamily.edgeRingCharP.ξ p k) * f (EdgeFamily.edgeRingCharP.η p k) = 0 := by
    rw [← map_mul, EdgeFamily.edgeRingCharP.ξ_mul_η, map_zero]
  let L := FractionRing (A p k)
  have hinj : Function.Injective (algebraMap (A p k) L) := IsFractionRing.injective (A p k) L
  rcases mul_eq_zero.mp hmul with hξ | hη
  ·
    refine ⟨L, inferInstance, (algebraMap (A p k) L).comp (gη p k : EdgeFamily.edgeRingCharP p k →+* A p k), ?_, ?_⟩
    · intro e he
      refine ker_gη_le p k f hξ ?_
      rw [RingHom.mem_ker] at he ⊢
      exact hinj (by rw [map_zero]; exact he)
    · intro κ₀ _ f₀ h0ξ _ e he
      refine ker_gη_le p k f₀ h0ξ ?_
      rw [RingHom.mem_ker] at he ⊢
      exact hinj (by rw [map_zero]; exact he)
  ·
    refine ⟨L, inferInstance, (algebraMap (A p k) L).comp (gξ p k : EdgeFamily.edgeRingCharP p k →+* A p k), ?_, ?_⟩
    · intro e he
      refine ker_gξ_le p k f hη ?_
      rw [RingHom.mem_ker] at he ⊢
      exact hinj (by rw [map_zero]; exact he)
    · intro κ₀ _ f₀ _ h0η e he
      refine ker_gξ_le p k f₀ h0η ?_
      rw [RingHom.mem_ker] at he ⊢
      exact hinj (by rw [map_zero]; exact he)

end S_CerednikDrinfeld_EdgeFamily_edgeRingCharP_exists_ker_le_and_forall_ker_le_of_apply_eq_zero
end P2MW
export P2MW.S_CerednikDrinfeld_EdgeFamily_edgeRingCharP_exists_ker_le_and_forall_ker_le_of_apply_eq_zero (solution)
