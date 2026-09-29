-- Prove2me | solution 1 for CartierDual.isLocalRing_baseChange_and_isLocalRing_cartierDual_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/30b35eb3-3d80-529d-8998-b822ad08bfc3

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_HopfAlgebra_CharacterClosure
import Theorems.Thm_CartierDual_dualBaseChangeLin_bijective_integral
import Theorems.Thm_GaloisRep_ratLocalizedAt_isLocalRing
import Theorems.Thm_GaloisRep_ratLocalizedAt_maximalIdeal_eq_span_natCast
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CartierDual_isLocalRing_baseChange_and_isLocalRing_cartierDual_baseChange

set_option autoImplicit false

open scoped TensorProduct

namespace SolLBC

open IsLocalRing

theorem isLocalRing_baseChange_of_retraction {O : Type*} [CommRing O] [IsLocalRing O]
    {H : Type*} [CommRing H] [Algebra O H] [Module.Finite O H] [IsLocalRing H]
    (ε : H →ₐ[O] O) {k : Type*} [Field k] [Algebra O k]
    (hk : ∀ x ∈ maximalIdeal O, algebraMap O k x = 0) :
    IsLocalRing (k ⊗[O] H) := by
  classical

  let εk : k ⊗[O] H →ₐ[k] k :=
    (Algebra.TensorProduct.rid O k k).toAlgHom.comp (Algebra.TensorProduct.map (AlgHom.id k k) ε)
  have hεk : ∀ (c : k) (h : H), εk (c ⊗ₜ[O] h) = c * algebraMap O k (ε h) := by
    intro c h
    show Algebra.TensorProduct.rid O k k (Algebra.TensorProduct.map (AlgHom.id k k) ε (c ⊗ₜ[O] h)) = _
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.rid_tmul, Algebra.smul_def, mul_comm]
  have hsurj : Function.Surjective εk := fun c => ⟨c ⊗ₜ[O] 1, by rw [hεk, map_one, map_one, mul_one]⟩
  let J : Ideal (k ⊗[O] H) := RingHom.ker εk.toRingHom
  have hJmax : J.IsMaximal := RingHom.ker_isMaximal_of_surjective εk.toRingHom hsurj

  let I : Ideal H := RingHom.ker ε.toRingHom
  let Ie : Ideal (k ⊗[O] H) := I.map (Algebra.TensorProduct.includeRight : H →ₐ[O] k ⊗[O] H)

  have hdiff : ∀ x : k ⊗[O] H, x - algebraMap k (k ⊗[O] H) (εk x) ∈ Ie := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero, sub_zero]; exact Ie.zero_mem
    | tmul c h =>
      rw [hεk]
      have h1 : algebraMap k (k ⊗[O] H) (c * algebraMap O k (ε h)) = c ⊗ₜ[O] algebraMap O H (ε h) := by
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
          mul_comm, ← Algebra.smul_def, TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
      rw [h1, ← TensorProduct.tmul_sub]
      have hmem : h - algebraMap O H (ε h) ∈ I := by
        rw [RingHom.mem_ker]
        show ε (h - algebraMap O H (ε h)) = 0
        rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
      have : c ⊗ₜ[O] (h - algebraMap O H (ε h)) =
          (c ⊗ₜ[O] (1 : H)) * (Algebra.TensorProduct.includeRight : H →ₐ[O] k ⊗[O] H) (h - algebraMap O H (ε h)) := by
        rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [this]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hmem)
    | add x y hx hy =>
      have : x + y - algebraMap k (k ⊗[O] H) (εk (x + y)) =
          (x - algebraMap k (k ⊗[O] H) (εk x)) + (y - algebraMap k (k ⊗[O] H) (εk y)) := by
        rw [map_add, map_add]; abel
      rw [this]; exact Ie.add_mem hx hy
  have hJIe : J ≤ Ie := by
    intro x hx
    have h0 : εk x = 0 := hx
    have := hdiff x
    rwa [h0, map_zero, sub_zero] at this

  let mOH : Ideal H := (maximalIdeal O).map (algebraMap O H)
  have hmOH_ne_top : mOH ≠ ⊤ := by
    intro htop

    have h1 : (1 : H) ∈ mOH := by rw [htop]; exact Submodule.mem_top
    have hle : mOH ≤ (maximalIdeal O).comap ε.toRingHom := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      show ε (algebraMap O H x) ∈ maximalIdeal O
      rwa [AlgHom.commutes]
    have := hle h1
    rw [Ideal.mem_comap] at this
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_one] at this
    exact (maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).mpr this)
  haveI : Nontrivial (H ⧸ mOH) := Ideal.Quotient.nontrivial_iff.mpr hmOH_ne_top
  haveI : IsLocalRing (H ⧸ mOH) := IsLocalRing.of_surjective' (Ideal.Quotient.mk mOH) Ideal.Quotient.mk_surjective

  haveI : IsArtinianRing (H ⧸ mOH) := by
    letI : Algebra (ResidueField O) (H ⧸ mOH) :=
      Ideal.Quotient.algebraQuotientOfLEComap (by
        intro x hx
        rw [Ideal.mem_comap]
        exact Ideal.mem_map_of_mem _ hx)
    haveI : IsScalarTower O (ResidueField O) (H ⧸ mOH) := IsScalarTower.of_algebraMap_eq (fun x => rfl)
    haveI : Module.Finite (ResidueField O) (H ⧸ mOH) :=
      Module.Finite.of_restrictScalars_finite O (ResidueField O) (H ⧸ mOH)
    exact IsArtinianRing.of_finite (ResidueField O) (H ⧸ mOH)
  obtain ⟨N, hN⟩ : IsNilpotent (maximalIdeal (H ⧸ mOH)) := by
    rw [← IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact IsArtinianRing.isNilpotent_jacobson_bot
  have hpow : ∀ i ∈ maximalIdeal H, i ^ N ∈ mOH := by
    intro i hi
    have hbar : Ideal.Quotient.mk mOH i ∈ maximalIdeal (H ⧸ mOH) := by
      haveI : IsLocalHom (Ideal.Quotient.mk mOH) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
      exact map_nonunit (Ideal.Quotient.mk mOH) i hi
    have : (Ideal.Quotient.mk mOH i) ^ N ∈ (maximalIdeal (H ⧸ mOH)) ^ N := Ideal.pow_mem_pow hbar N
    rw [hN] at this
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_pow]
    exact (Submodule.mem_bot _).mp this

  have hkill : ∀ x ∈ mOH, (1 : k) ⊗ₜ[O] x = 0 := by
    intro x hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨m, hm, rfl⟩
      rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one, hk m hm,
        TensorProduct.zero_tmul]
    · exact TensorProduct.tmul_zero _ _
    · intro x y _ _ hx hy; rw [TensorProduct.tmul_add, hx, hy, add_zero]
    · intro a x _ hx
      rw [smul_eq_mul, show (1 : k) ⊗ₜ[O] (a * x) = ((1 : k) ⊗ₜ[O] a) * ((1 : k) ⊗ₜ[O] x) by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one], hx, mul_zero]
  have hIe_nil : Ie ≤ nilradical (k ⊗[O] H) := by
    rw [Ideal.map_le_iff_le_comap]
    intro i hi
    rw [Ideal.mem_comap, mem_nilradical]
    refine ⟨N, ?_⟩
    have hiM : i ∈ maximalIdeal H := by
      apply IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top ε.toRingHom) hi
    rw [← map_pow, Algebra.TensorProduct.includeRight_apply]
    exact hkill _ (hpow i hiM)

  apply IsLocalRing.of_unique_max_ideal
  refine ⟨J, hJmax, fun 𝔫 h𝔫 => ?_⟩
  have hle : J ≤ 𝔫 := hJIe.trans (hIe_nil.trans (nilradical_le_prime 𝔫))
  exact (hJmax.eq_of_le h𝔫.ne_top hle).symm

end SolLBC

set_option maxHeartbeats 6400000 in
open scoped TensorProduct in
theorem solution
    (p : ℕ) [Fact p.Prime]
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Free (GaloisRep.ratLocalizedAt p) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H]
    (k₀ : Type) [Field k₀] [CharP k₀ p] [Algebra (GaloisRep.ratLocalizedAt p) k₀] :
    (IsLocalRing H → IsLocalRing (k₀ ⊗[GaloisRep.ratLocalizedAt p] H)) ∧
      (IsLocalRing (CartierDual (GaloisRep.ratLocalizedAt p) H) →
        IsLocalRing (CartierDual k₀ (k₀ ⊗[GaloisRep.ratLocalizedAt p] H))) := by
  classical
  haveI : IsLocalRing (GaloisRep.ratLocalizedAt p) := GaloisRep.ratLocalizedAt.isLocalRing Fact.out
  have hk : ∀ x ∈ IsLocalRing.maximalIdeal (GaloisRep.ratLocalizedAt p),
      algebraMap (GaloisRep.ratLocalizedAt p) k₀ x = 0 := by
    intro x hx
    rw [GaloisRep.ratLocalizedAt.maximalIdeal_eq_span_natCast p Fact.out, Ideal.mem_span_singleton] at hx
    obtain ⟨y, rfl⟩ := hx
    rw [map_mul, map_natCast, CharP.cast_eq_zero k₀ p, zero_mul]
  refine ⟨fun hH => ?_, fun hD => ?_⟩
  · haveI := hH
    exact SolLBC.isLocalRing_baseChange_of_retraction (Bialgebra.counitAlgHom (GaloisRep.ratLocalizedAt p) H) hk
  · haveI := hD
    have hloc : IsLocalRing (k₀ ⊗[GaloisRep.ratLocalizedAt p] CartierDual (GaloisRep.ratLocalizedAt p) H) :=
      SolLBC.isLocalRing_baseChange_of_retraction
        (Bialgebra.counitAlgHom (GaloisRep.ratLocalizedAt p) (CartierDual (GaloisRep.ratLocalizedAt p) H)) hk
    obtain ⟨hbij, h1, hmul, -, -⟩ := CartierDual.dualBaseChangeLin_bijective_integral (GaloisRep.ratLocalizedAt p) k₀ H
    let β := CartierDual.dualBaseChangeLin (GaloisRep.ratLocalizedAt p) k₀ H
    let f : k₀ ⊗[GaloisRep.ratLocalizedAt p] CartierDual (GaloisRep.ratLocalizedAt p) H →+*
        CartierDual k₀ (k₀ ⊗[GaloisRep.ratLocalizedAt p] H) :=
      { toFun := β, map_one' := h1, map_mul' := hmul, map_zero' := map_zero β, map_add' := map_add β }
    haveI : Nontrivial (CartierDual k₀ (k₀ ⊗[GaloisRep.ratLocalizedAt p] H)) :=
      hbij.1.nontrivial
    exact IsLocalRing.of_surjective' f hbij.2

end S_CartierDual_isLocalRing_baseChange_and_isLocalRing_cartierDual_baseChange
end P2MW
export P2MW.S_CartierDual_isLocalRing_baseChange_and_isLocalRing_cartierDual_baseChange (solution)
