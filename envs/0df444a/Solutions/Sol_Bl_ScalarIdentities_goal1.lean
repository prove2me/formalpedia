-- Prove2me | solution 1 for Bl.ScalarIdentities.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:25:24.459819+00:00
-- url     : https://prove2.me/submissions/c43d6653-5c63-4f47-bae1-9404edbc7bea

import Mathlib
import Definitions.Def_Lemmata_ScalarExtension_Scal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Polynomial
namespace Bl.ScalarIdentities
private lemma scal {K A : Type} [Field K] [IsAlgClosed K] [Ring A] [Algebra K A]
    (S0 : Type) [AddCommGroup S0] [Module K S0] [Module A S0] [IsScalarTower K A S0]
    [FiniteDimensional K S0] [IsSimpleModule A S0] (g : S0 →ₗ[A] S0) :
    ∃ c : K, ∀ v : S0, g v = c • v := by
  have : Nontrivial S0 := IsSimpleModule.nontrivial A S0
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (g.restrictScalars K)
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  let h : S0 →ₗ[A] S0 :=
    { toFun := fun w => g w - c • w
      map_add' := fun x y => by simp only [map_add, smul_add]; abel
      map_smul' := fun a w => by
        simp only [map_smul, RingHom.id_apply, smul_sub]
        rw [smul_comm c a w] }
  have h0 : h v = 0 := by
    have := hv.apply_eq_smul
    simp only [LinearMap.restrictScalars_apply] at this
    show g v - c • v = 0
    rw [this, sub_self]
  have hni : ¬ Function.Injective h := by
    intro hi
    exact hv.2 (hi (h0.trans h.map_zero.symm))
  have hz : h = 0 := (LinearMap.injective_or_eq_zero h).resolve_left hni
  refine ⟨c, fun w => ?_⟩
  have := LinearMap.congr_fun hz w
  exact sub_eq_zero.mp this
end Bl.ScalarIdentities
end

set_option autoImplicit false
open Polynomial
open Bl Bl.ScalarIdentities
namespace Bl.ScalarIdentities
theorem _root_.solution {K A : Type} [Field K] [IsAlgClosed K] [Ring A] [Algebra K A]
    (S0 : Type) [AddCommGroup S0] [Module K S0] [Module A S0] [IsScalarTower K A S0]
    [FiniteDimensional K S0] [IsSimpleModule A S0] (φ : S0 →ₗ[K] S0) :
    ∃ u : A, ∀ v : S0, u • v = φ v := by
  classical
  let f : Module.End (Module.End A S0) S0 :=
    { toFun := φ
      map_add' := φ.map_add
      map_smul' := fun g v => by
        obtain ⟨c, hc⟩ := scal (K := K) S0 g
        simp only [Module.End.smul_def, RingHom.id_apply, hc, φ.map_smul] }
  let b := Module.finBasis K S0
  obtain ⟨r, hr⟩ := jacobson_density f (Finset.univ.image b)
  refine ⟨r, fun v => ?_⟩
  let ψ : S0 →ₗ[K] S0 :=
    { toFun := fun w => r • w
      map_add' := smul_add r
      map_smul' := fun c w => (smul_comm c r w).symm }
  have hψ : ψ = φ := b.ext fun i => (hr (b i) (Finset.mem_image_of_mem b (Finset.mem_univ i))).symm
  exact LinearMap.congr_fun hψ v
end Bl.ScalarIdentities
