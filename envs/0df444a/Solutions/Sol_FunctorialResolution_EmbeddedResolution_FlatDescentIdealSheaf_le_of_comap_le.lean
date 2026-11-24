-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.FlatDescentIdealSheaf.le_of_comap_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:46:37.830537+00:00
-- url     : https://prove2.me/submissions/363938dd-65a8-489f-9adb-2e0a2b09fcd4

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_IdealSheafFlatComapInjective
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_ideal_eq_map_appLE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory AlgebraicGeometry TensorProduct
namespace FunctorialResolution.EmbeddedResolution.FlatDescentIdealSheaf
variable {W Y : Scheme.{u}}
private theorem one_mem_map_colon_of_mem_map {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : RingHom.Flat φ) (L : Ideal R) (a : R) (h : φ a ∈ L.map φ) :
    (1 : S) ∈ Ideal.map φ (Submodule.comap (LinearMap.lsmul R R a) L) := by
  let _ : Algebra R S := φ.toAlgebra
  have : Module.Flat R S := hφ
  have halg : (algebraMap R S) = φ := rfl
  have hex : Function.Exact (Submodule.subtype (Submodule.comap (LinearMap.lsmul R R a) L))
      ((L.mkQ).comp (LinearMap.lsmul R R a)) := by
    rw [LinearMap.exact_iff, LinearMap.ker_comp, Submodule.ker_mkQ, Submodule.range_subtype]
  have hex2 := Module.Flat.lTensor_exact (M := S) hex
  have key : ∀ s : S, s ∈ L.map φ → s ⊗ₜ[R] (L.mkQ (1 : R)) = 0 := by
    intro s hs
    let ψ : S →ₗ[S] S ⊗[R] (R ⧸ L) :=
      { toFun := fun t => t ⊗ₜ[R] (L.mkQ (1 : R))
        map_add' := fun x y => TensorProduct.add_tmul x y _
        map_smul' := fun c x => TensorProduct.smul_tmul' c x _ }
    have hψ : ∀ t : S, ψ t = t ⊗ₜ[R] (L.mkQ (1 : R)) := fun _ => rfl
    have hsub : L.map φ ≤ LinearMap.ker ψ := by
      rw [Ideal.map_le_iff_le_comap]
      intro l hl
      have h0 : l • (L.mkQ (1 : R)) = 0 := by
        rw [← map_smul]
        simp only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, smul_eq_mul, mul_one]
        exact hl
      simp only [Ideal.mem_comap, LinearMap.mem_ker, hψ]
      rw [show φ l = l • (1 : S) from by rw [Algebra.smul_def, halg, mul_one],
        TensorProduct.smul_tmul, h0, TensorProduct.tmul_zero]
    have hker := LinearMap.mem_ker.mp (hsub hs)
    rwa [hψ] at hker
  have hzero : (LinearMap.lTensor S ((L.mkQ).comp (LinearMap.lsmul R R a)))
      ((1 : S) ⊗ₜ[R] (1 : R)) = 0 := by
    rw [LinearMap.lTensor_tmul]
    show (1 : S) ⊗ₜ[R] (L.mkQ (a * (1 : R))) = 0
    rw [mul_one]
    have h1 : (L.mkQ a) = a • (L.mkQ (1 : R)) := by
      rw [← map_smul]; simp
    rw [h1, ← TensorProduct.smul_tmul,
      show a • (1 : S) = φ a from by rw [Algebra.smul_def, halg, mul_one]]
    exact key _ h
  obtain ⟨v, hv⟩ := (hex2 ((1 : S) ⊗ₜ[R] (1 : R))).mp hzero
  have hrange : ∀ u : S ⊗[R] (Submodule.comap (LinearMap.lsmul R R a) L),
      (TensorProduct.rid R S) (LinearMap.lTensor S
        (Submodule.subtype (Submodule.comap (LinearMap.lsmul R R a) L)) u)
      ∈ Ideal.map φ (Submodule.comap (LinearMap.lsmul R R a) L) := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul s c =>
        rw [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, Algebra.smul_def, halg]
        exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem φ c.2)
    | add u₁ u₂ h₁ h₂ =>
        rw [map_add, map_add]
        exact Submodule.add_mem _ h₁ h₂
  have hfin := hrange v
  rw [hv, TensorProduct.rid_tmul, one_smul] at hfin
  exact hfin
private theorem exists_not_mem_basicOpen_of_ne_top {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (C : Ideal Γ(X, U)) (hC : C ≠ ⊤) :
    ∃ x ∈ U, ∀ c ∈ C, x ∉ X.basicOpen c := by
  obtain ⟨m, hm, hCm⟩ := C.exists_le_maximal hC
  let p : PrimeSpectrum Γ(X, U) := ⟨m, hm.isPrime⟩
  refine ⟨hU.fromSpec.base p, ?_, ?_⟩
  · have hr : hU.fromSpec.base p ∈ Set.range hU.fromSpec.base := ⟨p, rfl⟩
    rw [hU.range_fromSpec] at hr
    exact hr
  · intro c hc hmem
    have h1 : p ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen c := hmem
    rw [hU.fromSpec_preimage_basicOpen] at h1
    have h2 : c ∉ m := h1
    exact h2 (hCm hc)
private theorem exists_mem_basicOpen_of_span_eq_top {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (s : Set Γ(X, U)) (hs : Ideal.span s = ⊤) (x : X) (hx : x ∈ U) :
    ∃ c ∈ s, x ∈ X.basicOpen c := by
  have hxr : x ∈ Set.range hU.fromSpec.base := by
    rw [hU.range_fromSpec]; exact hx
  obtain ⟨p, hp⟩ := hxr
  by_contra hcon
  push Not at hcon
  have hsub : s ⊆ (p.asIdeal : Set Γ(X, U)) := by
    intro c hcs
    have h1 : ¬ (p ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen c) := by
      intro hmem
      exact hcon c hcs (by rw [← hp]; exact hmem)
    rw [hU.fromSpec_preimage_basicOpen] at h1
    have h2 : c ∈ p.asIdeal := by
      by_contra hcc
      exact h1 hcc
    simpa using h2
  have hle := Ideal.span_le.mpr hsub
  rw [hs] at hle
  exact p.2.ne_top (top_le_iff.mp hle)
private theorem flat_appLE (g : W ⟶ Y) [AlgebraicGeometry.Flat g] (U : Y.affineOpens)
    (V : W.affineOpens) (e : (V : W.Opens) ≤ g ⁻¹ᵁ (U : Y.Opens)) :
    RingHom.Flat (g.appLE (U : Y.Opens) (V : W.Opens) e).hom := by
  apply AlgebraicGeometry.HasRingHomProperty.appLE (P := @AlgebraicGeometry.Flat)
  all_goals assumption
private theorem colon_eq_top_of_comap_le (g : W ⟶ Y) [AlgebraicGeometry.Flat g]
    [AlgebraicGeometry.Surjective g] (I J : Y.IdealSheafData)
    (h : I.comap g ≤ J.comap g) (U : Y.affineOpens) (a : Γ(Y, (U : Y.Opens)))
    (ha : a ∈ I.ideal U) (C : Ideal Γ(Y, (U : Y.Opens)))
    (hCdef : C = Submodule.comap
      (LinearMap.lsmul Γ(Y, (U : Y.Opens)) Γ(Y, (U : Y.Opens)) a) (J.ideal U)) :
    C = ⊤ := by
  by_contra hCtop
  obtain ⟨x, hxU, hx⟩ := exists_not_mem_basicOpen_of_ne_top U.2 C hCtop
  obtain ⟨w, hw⟩ := AlgebraicGeometry.Surjective.surj (f := g) x
  have hwU : w ∈ g ⁻¹ᵁ (U : Y.Opens) := by
    show g.base w ∈ (U : Y.Opens)
    rw [hw]; exact hxU
  obtain ⟨V, hV, hwV, hVU⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp W.isBasis_affineOpens) hwU
  have hV' : IsAffineOpen V := hV
  have hcomap0 := Scheme.IdealSheafData.le_def.mp h ⟨V, hV'⟩
  rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE I g U ⟨V, hV'⟩ hVU,
    Scheme.IdealSheafData.comap_ideal_eq_map_appLE J g U ⟨V, hV'⟩ hVU] at hcomap0
  have hcomap : Ideal.map (g.appLE (U : Y.Opens) V hVU).hom (I.ideal U) ≤
      Ideal.map (g.appLE (U : Y.Opens) V hVU).hom (J.ideal U) := hcomap0
  have hflat : RingHom.Flat (g.appLE (U : Y.Opens) V hVU).hom := flat_appLE g U ⟨V, hV'⟩ hVU
  have hone := one_mem_map_colon_of_mem_map (g.appLE (U : Y.Opens) V hVU).hom hflat (J.ideal U) a
    (hcomap (Ideal.mem_map_of_mem _ ha))
  rw [← hCdef] at hone
  have htop : Ideal.map (g.appLE (U : Y.Opens) V hVU).hom C = ⊤ :=
    (Ideal.eq_top_iff_one _).mpr hone
  have hspan : Ideal.span (((g.appLE (U : Y.Opens) V hVU).hom) ''
      (C : Set Γ(Y, (U : Y.Opens)))) = ⊤ := by
    rw [← Ideal.map_span, Ideal.span_eq]
    exact htop
  obtain ⟨f, hf, hwf⟩ := exists_mem_basicOpen_of_span_eq_top hV' _ hspan w hwV
  obtain ⟨c, hc, hcf⟩ := hf
  have hwb : w ∈ W.basicOpen ((g.appLE (U : Y.Opens) V hVU).hom c) := by
    rw [hcf]; exact hwf
  have hbeta : W.basicOpen ((g.appLE (U : Y.Opens) V hVU).hom c) ≤ g ⁻¹ᵁ (Y.basicOpen c) := by
    rw [Scheme.preimage_basicOpen]
    simp [Scheme.Hom.appLE]
  have hmem := hbeta hwb
  exact hx c hc (by rw [← hw]; exact hmem)
end FunctorialResolution.EmbeddedResolution.FlatDescentIdealSheaf
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TensorProduct
open FunctorialResolution FunctorialResolution.EmbeddedResolution FunctorialResolution.EmbeddedResolution.FlatDescentIdealSheaf
variable {W Y : Scheme.{u}}
namespace FunctorialResolution.EmbeddedResolution.FlatDescentIdealSheaf
theorem _root_.solution (g : W ⟶ Y) [AlgebraicGeometry.Flat g]
    [AlgebraicGeometry.Surjective g] (I J : Y.IdealSheafData)
    (h : I.comap g ≤ J.comap g) : I ≤ J := by
  rw [Scheme.IdealSheafData.le_def]
  intro U a ha
  have hC := colon_eq_top_of_comap_le g I J h U a ha _ rfl
  have h1 : (1 : Γ(Y, (U : Y.Opens))) ∈ Submodule.comap
      (LinearMap.lsmul Γ(Y, (U : Y.Opens)) Γ(Y, (U : Y.Opens)) a) (J.ideal U) := by
    rw [hC]; exact Submodule.mem_top
  have h2 : a * (1 : Γ(Y, (U : Y.Opens))) ∈ J.ideal U := h1
  simpa using h2
end FunctorialResolution.EmbeddedResolution.FlatDescentIdealSheaf
