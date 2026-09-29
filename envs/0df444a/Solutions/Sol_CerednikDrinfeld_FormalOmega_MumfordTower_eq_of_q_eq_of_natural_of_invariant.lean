-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.MumfordTower.eq_of_q_eq_of_natural_of_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/41872093-a4b5-56ca-b34c-3aa0792a5bcb

import Mathlib
import Definitions.Def_CerednikDrinfeld_MumfordTower
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_MumfordTower_eq_of_q_eq_of_natural_of_invariant

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem solution
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] (r : ℕ)
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (N : Subgroup (PGL(2, K₀)))
    (D : MumfordTower 𝒪 π K₀ r g₁ N) (n : ℕ)
    (C : Type) [CommRing C] [Algebra 𝒪 C] (hC : (algebraMap 𝒪 C π) ^ (n + 1) = 0)
    (X' : Scheme.{0}) (p₁ : X' ⟶ D.Z n) (p₂ : X' ⟶ Spec (CommRingCat.of C))
    (s : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))
    (hs : s ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) = Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))
    (hX' : IsPullback p₁ p₂ (D.zb n) s)
    (T : Scheme.{0})
    (ρ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], (algebraMap 𝒪 B π) ^ (n + 1) = 0 → (C →ₐ[𝒪] B) →
      (Omega K₀ π).obj B → (Spec (CommRingCat.of B) ⟶ T))
    (hρnat : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B']
      (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (hB' : (algebraMap 𝒪 B' π) ^ (n + 1) = 0) (φ : B →ₐ[𝒪] B') (c : C →ₐ[𝒪] B)
      (P : (Omega K₀ π).obj B),
      ρ B' hB' (φ.comp c) ((Omega K₀ π).map φ P) = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ ρ B hB c P)
    (hρinv : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (c : C →ₐ[𝒪] B)
      (g : Matrix.GeneralLinearGroup (Fin 2) K₀), Matrix.ProjGenLinGroup.mk g ∈ N →
      ∀ P P' : (Omega K₀ π).obj B, DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ P P' → ρ B hB c P' = ρ B hB c P)
    (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (c : C →ₐ[𝒪] B)
    (P P' : (Omega K₀ π).obj B) (hq : D.q n B hB P = D.q n B hB P') :
    ρ B hB c P = ρ B hB c P' := by
  classical
  obtain ⟨ι, hfin, f, hspan, hloc⟩ := D.q_zarFib n B hB P P' hq

  let 𝒰 := (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of B) f hspan).openCover
  refine Scheme.Cover.hom_ext 𝒰 _ _ fun i => ?_

  let Ci : Type := Localization.Away (f i)
  have hCi : (algebraMap 𝒪 Ci π) ^ (n + 1) = 0 := by
    rw [IsScalarTower.algebraMap_apply 𝒪 B Ci, ← map_pow, hB, map_zero]
  let φ : B →ₐ[𝒪] Ci := IsScalarTower.toAlgHom 𝒪 B Ci
  obtain ⟨g, hgN, hpb⟩ := hloc i Ci
  have hnat := hρnat B Ci hB hCi φ c P
  have hnat' := hρnat B Ci hB hCi φ c P'
  have hinv := hρinv Ci hCi (φ.comp c) g hgN _ _ hpb

  have hf : 𝒰.f i = Spec.map (CommRingCat.ofHom φ.toRingHom) := rfl
  rw [hf]
  exact hnat.symm.trans (hinv.symm.trans hnat')

end S_CerednikDrinfeld_FormalOmega_MumfordTower_eq_of_q_eq_of_natural_of_invariant
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_MumfordTower_eq_of_q_eq_of_natural_of_invariant (solution)
