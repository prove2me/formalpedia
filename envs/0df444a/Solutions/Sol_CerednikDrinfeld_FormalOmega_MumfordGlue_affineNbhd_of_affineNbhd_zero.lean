-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.MumfordGlue.affineNbhd_of_affineNbhd_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/6cb5e215-6718-573a-b7a6-bbcba23d7f42

import Definitions.Def_CerednikDrinfeld_MumfordGlue
import Theorems.Thm_AlgebraicGeometry_forall_finite_exists_isAffineOpen_of_isClosedImmersion_of_surjective
import Theorems.Thm_AlgebraicGeometry_isAffineOpen_of_isAffineOpen_preimage_of_isPullback_of_flat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_MumfordGlue_affineNbhd_of_affineNbhd_zero

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace AffNbhdTower29

theorem comap_factor_surjective {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) (k : ℕ) :
    Function.Surjective (PrimeSpectrum.comap (Ideal.Quotient.factor
      (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (k + 1))) :
        Ideal.span {π ^ (k + 1 + 1)} ≤ Ideal.span {π ^ (k + 1)}))) := by
  set φ := Ideal.Quotient.factor
      (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (k + 1))) :
        Ideal.span {π ^ (k + 1 + 1)} ≤ Ideal.span {π ^ (k + 1)}) with hφ
  have hsurj : Function.Surjective φ := Ideal.Quotient.factor_surjective _
  have hker : ∀ x ∈ RingHom.ker φ, IsNilpotent x := by
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have ha : a ∈ Ideal.span {π ^ (k + 1)} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      rw [RingHom.mem_ker, hφ, Ideal.Quotient.factor_mk] at hx
      exact hx
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    refine ⟨2, ?_⟩
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    refine Ideal.mem_span_singleton'.2 ⟨b * b * π ^ k, ?_⟩
    ring
  intro p
  have hp : p ∈ Set.range (PrimeSpectrum.comap φ) := by
    rw [range_comap_of_surjective _ φ hsurj]
    intro x hx
    obtain ⟨m, hm⟩ := hker x hx
    exact p.2.mem_of_pow_mem m (by rw [hm]; exact zero_mem _)
  exact hp

theorem surjective_specMap_factor {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) (k : ℕ) :
    Surjective (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
      (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (k + 1))) :
        Ideal.span {π ^ (k + 1 + 1)} ≤ Ideal.span {π ^ (k + 1)})))) :=
  ⟨comap_factor_surjective π k⟩

end AffNbhdTower29

open AffNbhdTower29

theorem solution
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
    (N : Subgroup (PGL(2, K₀)))
    (Gl : MumfordGlue 𝒪 π K₀ r g₁ N)
    (h0 : ∀ S : Set (Gl.Z 0), S.Finite → ∃ U : (Gl.Z 0).Opens, IsAffineOpen U ∧ S ⊆ (U : Set (Gl.Z 0))) :
    ∀ (n : ℕ) (S : Set (Gl.Z n)), S.Finite → ∃ U : (Gl.Z n).Opens, IsAffineOpen U ∧ S ⊆ (U : Set (Gl.Z n)) := by
  intro n
  induction n with
  | zero => exact h0
  | succ k ih =>
    have sq := (Gl.zt_isPullback k).flip
    haveI : IsClosedImmersion (Gl.zt k) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsClosedImmersion) sq
        (IsClosedImmersion.spec_of_surjective _ (Ideal.Quotient.factor_surjective
          (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (k + 1))))))
    haveI : Surjective (Gl.zt k) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Surjective) sq
        (surjective_specMap_factor π k)
    exact AlgebraicGeometry.forall_finite_exists_isAffineOpen_of_isClosedImmersion_of_surjective (Gl.zt k)
      (fun U hU => AlgebraicGeometry.isAffineOpen_of_isAffineOpen_preimage_of_isPullback_of_flat 𝒪 π hπ
        Gl.Z Gl.zb Gl.zt Gl.zt_isPullback Gl.zb_flat k U hU) ih

end S_CerednikDrinfeld_FormalOmega_MumfordGlue_affineNbhd_of_affineNbhd_zero
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_MumfordGlue_affineNbhd_of_affineNbhd_zero (solution)
