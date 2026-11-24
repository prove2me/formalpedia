-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.indexBasic_dual_le_fg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:16.440399+00:00
-- url     : https://prove2.me/submissions/0b28781b-7ac4-4c49-a432-950aff60cb5e

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualBasic_mem_dual


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
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module R V] [IsScalarTower R K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (hnd : h.Nondegenerate) (A : Submodule R V)
    (hA : Submodule.span K (A : Set V) = ⊤) :
    ∃ F : Submodule R V, F.FG ∧ dual h A ≤ F := by
  classical
  obtain ⟨b, hbA, hspan, hli⟩ := exists_linearIndependent K (A : Set V)
  have htop : ⊤ ≤ Submodule.span K (Set.range ((↑) : b → V)) := by
    rw [Subtype.range_coe, hspan, hA]
  let e : Module.Basis b K V := Module.Basis.mk hli htop
  have : Finite b := Module.Finite.finite_basis e
  have : Fintype b := Fintype.ofFinite b
  let φ : V →ₗ[K] (b → K) := LinearMap.pi (fun i => h (e i))
  have hφ : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    rw [Submodule.mem_bot]
    have h0 : h.flip x = 0 := e.ext (fun i => by
      have := congr_fun hx i
      simpa [φ] using this)
    exact hnd.2 x (fun z => by
      have := LinearMap.congr_fun h0 z
      simpa using this)
  have hφs : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      rw [Module.finrank_fintype_fun_eq_card, Module.finrank_eq_card_basis e])).mp hφ
  let ψ := LinearEquiv.ofBijective φ ⟨hφ, hφs⟩
  refine ⟨Submodule.span R (Set.range (fun j : b => ψ.symm (Pi.single j 1))),
    Submodule.fg_span (Set.finite_range _), ?_⟩
  intro x hx
  rw [dualBasic_mem_dual] at hx
  have hxj : ∀ j : b, ∃ r : R, algebraMap R K r = h (e j) x := fun j => by
    have := hx (e j) (by rw [Module.Basis.mk_apply]; exact hbA j.2)
    rwa [Submodule.mem_one] at this
  choose r hr using hxj
  have hψ : ∀ y, ψ y = φ y := fun y => LinearEquiv.ofBijective_apply φ y
  have hx' : x = ∑ j, (algebraMap R K (r j)) • ψ.symm (Pi.single j 1) := by
    apply ψ.injective
    rw [map_sum]
    simp only [map_smul, LinearEquiv.apply_symm_apply]
    ext i
    rw [hψ]
    simp [Finset.sum_apply, Pi.single_apply, hr, φ]
  rw [hx']
  simp_rw [algebraMap_smul]
  exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
end Formalism.HermitianLatticesTheory
