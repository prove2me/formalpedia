-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.dualLattice_repr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:51.542359+00:00
-- url     : https://prove2.me/submissions/b58f1c77-121c-49ac-9629-bf950fe73732

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
variable [StarRing K]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hs : h.IsSymm) (b : Basis ι K V) (bs : ι → V)
    (hbs : ∀ i j, h (b i) (bs j) = if i = j then 1 else 0) (L : Submodule R V)
    (hb : ∀ i, b i ∈ L) (d : R) (hd : d ≠ 0)
    (hdL : ∀ y ∈ L, d • y ∈ Submodule.span R (Set.range b)) (f : L →ₗ[R] R) :
    ∃ w : V, ∀ y (hy : y ∈ L), h w y = algebraMap R K (f ⟨y, hy⟩) := by
  classical
  let w : V := ∑ j, star (algebraMap R K (f ⟨b j, hb j⟩)) • bs j
  have hsym : ∀ i j, h (bs j) (b i) = if i = j then 1 else 0 := by
    intro i j
    rw [← hs.eq (b i) (bs j), hbs]
    split_ifs <;> simp
  have hwb : ∀ i, h w (b i) = algebraMap R K (f ⟨b i, hb i⟩) := by
    intro i
    simp [w, map_sum, LinearMap.map_smulₛₗ₂, hsym, starRingEnd_apply, star_star, Algebra.smul_def]
  have hspL : Submodule.span R (Set.range b) ≤ L :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hb i)
  have hspan : ∀ z ∈ Submodule.span R (Set.range b), ∀ hz : z ∈ L,
      h w z = algebraMap R K (f ⟨z, hz⟩) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      intro _
      exact hwb i
    | zero =>
      intro hz
      have e : (⟨0, hz⟩ : L) = 0 := rfl
      rw [e, map_zero, map_zero, map_zero]
    | add x y hx hy ihx ihy =>
      intro hxy
      have e : (⟨x + y, hxy⟩ : L) = ⟨x, hspL hx⟩ + ⟨y, hspL hy⟩ := rfl
      rw [e, map_add, map_add, map_add, ihx (hspL hx), ihy (hspL hy)]
    | smul r x hx ih =>
      intro hrx
      have e1 : h w (r • x) = algebraMap R K r * h w x := by
        rw [← algebraMap_smul K r x, LinearMap.map_smul, smul_eq_mul]
      have e2 : (⟨r • x, hrx⟩ : L) = r • ⟨x, hspL hx⟩ := rfl
      rw [e1, e2, map_smul, smul_eq_mul, map_mul, ih (hspL hx)]
  refine ⟨w, fun y hy => ?_⟩
  have h1 := hspan _ (hdL y hy) (L.smul_mem d hy)
  have e1 : h w (d • y) = algebraMap R K d * h w y := by
    rw [← algebraMap_smul K d y, LinearMap.map_smul, smul_eq_mul]
  have e2 : (⟨d • y, L.smul_mem d hy⟩ : L) = d • ⟨y, hy⟩ := rfl
  rw [e1, e2, map_smul, smul_eq_mul, map_mul] at h1
  have hne : algebraMap R K d ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap R K)]
    exact fun h0 => hd (IsFractionRing.injective R K h0)
  exact mul_left_cancel₀ hne h1
end Formalism.HermitianLatticesTheory
