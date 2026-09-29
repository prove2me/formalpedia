-- Prove2me | solution 1 for CuspForm.isReduced_of_adjoin_range_heckeAlgebra_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/c2af4e60-18d2-5b61-92cf-cac1e99ca7a9

import Mathlib
import Definitions.Def_CuspForm_HeckeAlgebra
import Theorems.Thm_CuspForm_isReduced_heckeAlgebra_of_primeFactors_subset
import Theorems.Thm_CuspForm_moduleFinite_heckeAlgebra_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_isReduced_of_adjoin_range_heckeAlgebra_eq_top
p2m_attr_erase "simp" "PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU"

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RtRed

section SemisimpleGenerators

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪]
  {T : Type} [CommRing T] [Algebra 𝒪 T] [Module.Free 𝒪 T] [Module.Finite 𝒪 T]

theorem isReduced_of_free_of_adjoin_eq_top (G : Set T) (hadj : Algebra.adjoin 𝒪 G = ⊤)
    (hG : ∀ g ∈ G, ∃ P : ℤ[X], Squarefree (P.map (Int.castRingHom ℚ)) ∧ aeval g P = 0) :
    IsReduced T := by
  classical
  let K := FractionRing 𝒪
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective 𝒪 K)
  let ι := Module.Free.ChooseBasisIndex 𝒪 T
  let b : Module.Basis ι 𝒪 T := Module.Free.chooseBasis 𝒪 T

  let Φ : T →ₐ[𝒪] Matrix ι ι K :=
    ((Algebra.ofId 𝒪 K).mapMatrix.comp
      (LinearMap.toMatrixAlgEquiv b : Module.End 𝒪 T ≃ₐ[𝒪] Matrix ι ι 𝒪).toAlgHom).comp
      (Algebra.lmul 𝒪 T)
  have hΦ : Function.Injective Φ := by
    refine (Matrix.map_injective (IsFractionRing.injective 𝒪 K)).comp
      ((LinearMap.toMatrixAlgEquiv b).injective.comp (Algebra.lmul_injective (R := 𝒪) (A := T)))

  let Ψ : T →+* Module.End K (ι → K) :=
    (Matrix.toLinAlgEquiv' : Matrix ι ι K ≃ₐ[K] Module.End K (ι → K)).toRingEquiv.toRingHom.comp
      Φ.toRingHom
  have hΨ : ∀ x, Ψ x = Matrix.toLin' (Φ x) := fun x => rfl
  have hΨinj : Function.Injective Ψ :=
    (Matrix.toLinAlgEquiv' : Matrix ι ι K ≃ₐ[K] Module.End K (ι → K)).injective.comp hΦ

  have hΨc : ∀ x y, Commute (Ψ x) (Ψ y) := fun x y => by
    rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]
  have hss : ∀ x, (Ψ x).IsSemisimple := by
    intro x
    have hx : x ∈ Algebra.adjoin 𝒪 G := hadj ▸ Algebra.mem_top
    induction hx using Algebra.adjoin_induction with
    | mem g hg =>
      obtain ⟨P, hP, hP0⟩ := hG g hg
      refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero
        (p := P.map (Int.castRingHom K)) ?_ ?_
      · rw [← PerfectField.separable_iff_squarefree] at hP ⊢
        have := hP.map (f := algebraMap ℚ K)
        rwa [Polynomial.map_map, RingHom.eq_intCast' ((algebraMap ℚ K).comp (Int.castRingHom ℚ))]
          at this
      · have h2 : aeval (Ψ g) P = Ψ.toIntAlgHom (aeval g P) :=
          (Polynomial.aeval_algHom_apply Ψ.toIntAlgHom g P)
        rw [aeval_def, eval₂_map, RingHom.ext_int ((algebraMap K _).comp (Int.castRingHom K))
          (algebraMap ℤ _), ← aeval_def, h2, hP0, map_zero]
    | algebraMap r =>
      have : Ψ (algebraMap 𝒪 T r) = algebraMap 𝒪 K r • (1 : Module.End K (ι → K)) := by
        rw [hΨ, AlgHom.commutes, IsScalarTower.algebraMap_apply 𝒪 K (Matrix ι ι K),
          Algebra.algebraMap_eq_smul_one, map_smul, Matrix.toLin'_one, Module.End.one_eq_id]
      rw [this]
      exact Module.End.IsSemisimple_smul _ Module.End.isSemisimple_id
    | add x y _ _ hx hy => rw [map_add]; exact hx.add_of_commute (hΨc x y) hy
    | mul x y _ _ hx hy => rw [map_mul]; exact hx.mul_of_commute (hΨc x y) hy
  refine ⟨fun x hx => hΨinj ?_⟩
  rw [map_zero]
  exact Module.End.eq_zero_of_isNilpotent_isSemisimple (hx.map Ψ) (hss x)

end SemisimpleGenerators

section SquarefreeMinpoly

variable {A : Type} [CommRing A] [IsReduced A]

theorem squarefree_map_minpoly_of_isReduced (t : A) (ht : IsIntegral ℤ t) :
    Squarefree ((minpoly ℤ t).map (Int.castRingHom ℚ)) := by
  classical
  nontriviality A
  set P := minpoly ℤ t with hPdef
  have hPm : P.Monic := minpoly.monic ht
  have hmapeq : (Int.castRingHom ℚ) = algebraMap ℤ ℚ := RingHom.eq_intCast' _ |>.symm
  rw [hmapeq]
  intro g hg
  by_contra hgu
  have hPQ0 : P.map (algebraMap ℤ ℚ) ≠ 0 := (hPm.map _).ne_zero
  have hg0 : g ≠ 0 := fun h => hPQ0 (by
    obtain ⟨s, hs⟩ := hg; rw [hs, h, zero_mul, zero_mul])

  set g₁ := g * C (leadingCoeff g)⁻¹ with hg₁
  have hg₁m : g₁.Monic := monic_mul_leadingCoeff_inv hg0
  have hg₁g : Associated g₁ g :=
    (associated_mul_isUnit_left_iff (isUnit_C.mpr
      (inv_ne_zero (leadingCoeff_ne_zero.mpr hg0)).isUnit)).mpr (Associated.refl g) |>.symm.symm
  have hdvd : g₁ * g₁ ∣ P.map (algebraMap ℤ ℚ) :=
    (Associated.dvd_iff_dvd_left (hg₁g.mul_mul hg₁g)).mpr hg
  obtain ⟨s, hs⟩ := hdvd

  obtain ⟨a, ha⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd (K := ℚ) hPm
    (⟨g₁ * s, by rw [hs, mul_assoc]⟩ : g₁ ∣ P.map (algebraMap ℤ ℚ))
  rw [hg₁m.leadingCoeff, C_1, mul_one] at ha
  have hsm : s.Monic := by
    have := (hPm.map (algebraMap ℤ ℚ)).leadingCoeff
    rw [hs, leadingCoeff_mul, leadingCoeff_mul, hg₁m.leadingCoeff, one_mul, one_mul] at this
    exact this
  obtain ⟨c, hc⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd (K := ℚ) hPm
    (⟨g₁ * g₁, by rw [hs, mul_comm]⟩ : s ∣ P.map (algebraMap ℤ ℚ))
  rw [hsm.leadingCoeff, C_1, mul_one] at hc
  have ham : a.Monic := monic_of_injective (algebraMap ℤ ℚ).injective_int (ha ▸ hg₁m)
  have hcm : c.Monic := monic_of_injective (algebraMap ℤ ℚ).injective_int (hc ▸ hsm)
  have hPeq : P = a * a * c := Polynomial.map_injective _ (algebraMap ℤ ℚ).injective_int (by
    rw [Polynomial.map_mul, Polynomial.map_mul, ha, hc, hs])

  have hq0 : aeval t (a * c) = 0 := by
    refine IsReduced.eq_zero _ ⟨2, ?_⟩
    rw [← map_pow, show (a * c) ^ 2 = P * c by rw [hPeq]; ring, map_mul, minpoly.aeval, zero_mul]
  have hmin := minpoly.min ℤ t (ham.mul hcm) hq0
  rw [← hPdef, hPeq, degree_mul, degree_mul, degree_mul] at hmin
  have hapos : 0 < degree a := by
    have : 0 < degree g₁ := degree_pos_of_ne_zero_of_nonunit hg₁m.ne_zero
      (fun hu => hgu (hg₁g.isUnit hu))
    rwa [← ha, degree_map_eq_of_injective (algebraMap ℤ ℚ).injective_int] at this
  have hafin : degree a ≠ ⊥ := degree_ne_bot.mpr ham.ne_zero
  have hcfin : degree c ≠ ⊥ := degree_ne_bot.mpr hcm.ne_zero
  revert hmin hapos hafin hcfin
  generalize degree a = da; generalize degree c = dc
  cases da with
  | bot => simp
  | coe da =>
    cases dc with
    | bot => simp
    | coe dc =>
      intro hmin hapos _ _
      have h1 : (0 : WithBot ℕ) < da := hapos
      norm_cast at hmin h1
      omega

end SquarefreeMinpoly

theorem isReduced_of_adjoin_range (N : ℕ) [NeZero N] (S : Set ℕ)
    (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪]
    {T : Type} [CommRing T] [Algebra 𝒪 T] [Module.Free 𝒪 T] [Module.Finite 𝒪 T]
    (π : CuspForm.heckeAlgebra N 2 S →+* T) (hadj : Algebra.adjoin 𝒪 (Set.range π) = ⊤) :
    IsReduced T := by
  haveI := CuspForm.isReduced_heckeAlgebra_of_primeFactors_subset N S hNS
  haveI := CuspForm.moduleFinite_heckeAlgebra_two N S
  refine isReduced_of_free_of_adjoin_eq_top (Set.range π) hadj ?_
  rintro _ ⟨t, rfl⟩
  have ht : IsIntegral ℤ t := Algebra.IsIntegral.isIntegral _
  refine ⟨minpoly ℤ t, squarefree_map_minpoly_of_isReduced t ht, ?_⟩
  have h := Polynomial.aeval_algHom_apply π.toIntAlgHom t (minpoly ℤ t)
  rw [minpoly.aeval, map_zero] at h
  exact h

end RtRed

theorem solution
    {N : ℕ} [NeZero N] {S : Set ℕ} (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪]
    {T : Type} [CommRing T] [Algebra 𝒪 T] [Module.Finite 𝒪 T] [Module.Free 𝒪 T]
    (π : CuspForm.heckeAlgebra N 2 S →+* T) (hadj : Algebra.adjoin 𝒪 (Set.range π) = ⊤) :
    IsReduced T :=
  RtRed.isReduced_of_adjoin_range N S hNS π hadj

end S_CuspForm_isReduced_of_adjoin_range_heckeAlgebra_eq_top
end P2MW
export P2MW.S_CuspForm_isReduced_of_adjoin_range_heckeAlgebra_eq_top (solution)
