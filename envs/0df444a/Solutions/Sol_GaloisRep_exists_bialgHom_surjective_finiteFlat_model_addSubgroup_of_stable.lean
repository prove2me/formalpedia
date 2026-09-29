-- Prove2me | solution 1 for GaloisRep.exists_bialgHom_surjective_finiteFlat_model_addSubgroup_of_stable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/13fad635-fe4a-51d9-8f05-6c58bce47718

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_HopfAlgebra_exists_finiteFlat_pointClosure_of_isGaloisInvariant_rat_algebraicClosure
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Theorems.Thm_GaloisRep_ratLocalizedAt_isLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_exists_bialgHom_surjective_finiteFlat_model_addSubgroup_of_stable

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

theorem solution
    (p : ℕ) [Fact p.Prime]
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Free (GaloisRep.ratLocalizedAt p) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H]
    {N : Type} [AddCommGroup N] [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) N]
    (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ N)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_gal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ h : H, g h = σ (f h)) → e g = σ • e f)
    {T : Type} (act : T → (N →+ N)) (φ : T → (H →ₐ[GaloisRep.ratLocalizedAt p] H))
    (hφ : ∀ (t : T) (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ h : H, g h = f (φ t h)) → e g = act t (e f))
    (N' : AddSubgroup N)
    (hN'gal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), ∀ x ∈ N', σ • x ∈ N')
    (hN'act : ∀ t : T, ∀ x ∈ N', act t x ∈ N') :
    ∃ (H' : Type) (_ : CommRing H') (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) H')
      (_ : Module.Finite (GaloisRep.ratLocalizedAt p) H') (_ : Module.Free (GaloisRep.ratLocalizedAt p) H')
      (_ : Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H')
      (π : H →ₐc[GaloisRep.ratLocalizedAt p] H')
      (e' : WithConv (H' →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ ↥N')
      (φ' : T → (H' →ₐ[GaloisRep.ratLocalizedAt p] H')),
      Function.Surjective π ∧
      (∀ f : WithConv (H' →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        ((e' f : ↥N') : N) =
          e (WithConv.toConv ((WithConv.ofConv f).comp (π : H →ₐ[GaloisRep.ratLocalizedAt p] H')))) ∧
      (∀ t : T, (φ' t).comp (π : H →ₐ[GaloisRep.ratLocalizedAt p] H') =
        (π : H →ₐ[GaloisRep.ratLocalizedAt p] H').comp (φ t)) := by
  classical
  have hp : p.Prime := Fact.out

  haveI hPI : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hp)
  haveI hlocz := GaloisRep.isLocalization_ratLocalizedAt hp
  haveI : IsLocalRing (GaloisRep.ratLocalizedAt p) := GaloisRep.ratLocalizedAt.isLocalRing hp
  haveI : IsFractionRing (GaloisRep.ratLocalizedAt p) ℚ :=
    IsFractionRing.isFractionRing_of_isLocalization (Ideal.span {(p : ℤ)}).primeCompl _ _
      (Ideal.primeCompl_le_nonZeroDivisors _)
  haveI : IsDiscreteValuationRing (GaloisRep.ratLocalizedAt p) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain ℤ
      (P := Ideal.span {(p : ℤ)}) (by
        rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hp.ne_zero) (GaloisRep.ratLocalizedAt p)

  have he_one : e 1 = 0 := by
    have h := he_add 1 1
    rw [one_mul] at h
    have : e 1 + e 1 = e 1 + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel this

  let Γ : Submonoid (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)) :=
    { carrier := {ν | e ν ∈ N'}
      one_mem' := by show e 1 ∈ N'; rw [he_one]; exact N'.zero_mem
      mul_mem' := fun {a b} ha hb => by show e (a * b) ∈ N'; rw [he_add]; exact N'.add_mem ha hb }
  have hΓ : ∀ ν, ν ∈ Γ ↔ e ν ∈ N' := fun _ => Iff.rfl
  have hgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (ν : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)), ν ∈ Γ →
      WithConv.toConv (((σ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ).restrictScalars
        (GaloisRep.ratLocalizedAt p)).comp (WithConv.ofConv ν)) ∈ Γ := by
    intro σ ν hν
    rw [hΓ] at hν ⊢
    rw [he_gal σ ν _ (fun h => rfl)]
    exact hN'gal σ _ hν
  obtain ⟨H', _instCR, _instHopf, π, hπ, hfin, hflat, hcocomm, hker, huniv⟩ :=
    HopfAlgebra.exists_finiteFlat_pointClosure_of_isGaloisInvariant_rat_algebraicClosure
      (GaloisRep.ratLocalizedAt p) H Γ hgal
  haveI := hfin
  haveI := hflat
  haveI := hcocomm
  haveI hfree : Module.Free (GaloisRep.ratLocalizedAt p) H' := Module.free_of_flat_of_isLocalRing

  have huniv' := huniv (AlgebraicClosure ℚ) (AlgHom.id (GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))
    Function.injective_id

  let fwd : WithConv (H' →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) → ↥N' := fun f =>
    ⟨e (WithConv.toConv ((WithConv.ofConv f).comp (π : H →ₐ[GaloisRep.ratLocalizedAt p] H'))), by
      rw [← hΓ]
      have h := (huniv' ((WithConv.ofConv f).comp (π : H →ₐ[GaloisRep.ratLocalizedAt p] H'))).mp
        ⟨WithConv.ofConv f, rfl⟩
      simpa using h⟩
  have hfwd : ∀ f, ((fwd f : ↥N') : N) =
      e (WithConv.toConv ((WithConv.ofConv f).comp (π : H →ₐ[GaloisRep.ratLocalizedAt p] H'))) := fun _ => rfl
  have hinj : Function.Injective fwd := by
    intro f g hfg
    have h := congrArg (fun x : ↥N' => e.symm (x : N)) hfg
    simp only [hfwd, Equiv.symm_apply_apply] at h
    have h' := congrArg WithConv.ofConv h
    simp only [WithConv.ofConv_toConv] at h'
    apply WithConv.ofConv_injective
    apply AlgHom.ext; intro y
    obtain ⟨x, rfl⟩ := hπ y
    exact congrArg (fun F : H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ => F x) h'
  have hsurj : Function.Surjective fwd := by
    intro n
    have hmem : e.symm (n : N) ∈ Γ := by rw [hΓ, Equiv.apply_symm_apply]; exact n.2
    have h := (huniv' (WithConv.ofConv (e.symm (n : N)))).mpr (by simpa using hmem)
    obtain ⟨f', hf'⟩ := h
    refine ⟨WithConv.toConv f', ?_⟩
    apply Subtype.ext
    rw [hfwd, WithConv.ofConv_toConv, hf', WithConv.toConv_ofConv, Equiv.apply_symm_apply]
  let e' : WithConv (H' →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ ↥N' := Equiv.ofBijective fwd ⟨hinj, hsurj⟩

  have hkerle : ∀ t : T, RingHom.ker (π : H →ₐ[GaloisRep.ratLocalizedAt p] H').toRingHom ≤
      RingHom.ker (((π : H →ₐ[GaloisRep.ratLocalizedAt p] H').comp (φ t)).toRingHom) := by
    intro t x hx
    rw [RingHom.mem_ker] at hx ⊢
    show π (φ t x) = 0
    have hx' : x ∈ RingHom.ker π := hx
    rw [hker] at hx'
    have : φ t x ∈ RingHom.ker π := by
      rw [hker]
      simp only [Ideal.mem_iInf] at hx' ⊢
      intro ν hν
      have hνφ : WithConv.toConv ((WithConv.ofConv ν).comp (φ t)) ∈ Γ := by
        show e (WithConv.toConv ((WithConv.ofConv ν).comp (φ t))) ∈ N'
        rw [hφ t ν _ (fun h => rfl)]
        exact hN'act t _ hν
      have := hx' _ hνφ
      simpa [RingHom.mem_ker] using this
    exact this
  let φ'r : T → (H' →+* H') := fun t =>
    (π : H →ₐ[GaloisRep.ratLocalizedAt p] H').toRingHom.liftOfSurjective hπ
      ⟨((π : H →ₐ[GaloisRep.ratLocalizedAt p] H').comp (φ t)).toRingHom, hkerle t⟩
  have hφ'r : ∀ (t : T) (x : H), φ'r t (π x) = π (φ t x) := fun t x =>
    (π : H →ₐ[GaloisRep.ratLocalizedAt p] H').toRingHom.liftOfSurjective_comp_apply hπ _ x
  let φ' : T → (H' →ₐ[GaloisRep.ratLocalizedAt p] H') := fun t =>
    { toRingHom := φ'r t
      commutes' := fun r => by
        have h1 : algebraMap (GaloisRep.ratLocalizedAt p) H' r = π (algebraMap (GaloisRep.ratLocalizedAt p) H r) :=
          ((π : H →ₐ[GaloisRep.ratLocalizedAt p] H').commutes r).symm
        rw [h1]
        show φ'r t (π (algebraMap (GaloisRep.ratLocalizedAt p) H r)) = π (algebraMap (GaloisRep.ratLocalizedAt p) H r)
        rw [hφ'r, AlgHom.commutes] }
  refine ⟨H', _instCR, _instHopf, hfin, hfree, hcocomm, π, e', φ', hπ, fun f => rfl, ?_⟩
  intro t
  apply AlgHom.ext; intro x
  exact hφ'r t x

end S_GaloisRep_exists_bialgHom_surjective_finiteFlat_model_addSubgroup_of_stable
end P2MW
export P2MW.S_GaloisRep_exists_bialgHom_surjective_finiteFlat_model_addSubgroup_of_stable (solution)
