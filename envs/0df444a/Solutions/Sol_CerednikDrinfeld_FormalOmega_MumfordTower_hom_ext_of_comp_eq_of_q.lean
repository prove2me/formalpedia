-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.MumfordTower.hom_ext_of_comp_eq_of_q
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/f2ac2762-c3fe-565d-aaa0-63ad2b55ad92

import Mathlib
import Definitions.Def_CerednikDrinfeld_MumfordTower
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_MumfordTower_hom_ext_of_comp_eq_of_q

set_option autoImplicit false

noncomputable section

open scoped TensorProduct MatrixGroups
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace U1aC

theorem ringHom_eq_of_spec_eq {R S : Type} [CommRing R] [CommRing S] (f g : R →+* S)
    (h : Spec.map (CommRingCat.ofHom f) = Spec.map (CommRingCat.ofHom g)) : f = g := by
  have := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom this |> fun e => by simpa using e

end U1aC

open U1aC in
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
    (w w' : X' ⟶ T)
    (h : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (c : C →ₐ[𝒪] B)
      (P : (Omega K₀ π).obj B) (x : Spec (CommRingCat.of B) ⟶ X'),
      x ≫ p₁ = D.q n B hB P → x ≫ p₂ = Spec.map (CommRingCat.ofHom c.toRingHom) → x ≫ w = x ≫ w') :
    w = w' := by
  classical

  let A : Type := (chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}
  have hA : (algebraMap 𝒪 A π) ^ (n + 1) = 0 := by
    have e : algebraMap 𝒪 A π =
        Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) (algebraMap 𝒪 (chartERing 𝒪 π r) π) := rfl
    rw [e, ← RingHom.map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl

  have hcov := fun z : ↥(D.Z n) => D.cover n hA z
  choose hh dd PP hchart hpb hx using hcov
  haveI hopen : ∀ z : ↥(D.Z n), IsOpenImmersion (D.q n A hA (PP z)) :=
    fun z => D.chart_isOpenImmersion (hh z) n hA (dd z) (PP z) (hchart z) (hpb z)

  let 𝒰 : (D.Z n).OpenCover := Scheme.Cover.mkOfCovers (↥(D.Z n)) (fun _ => Spec (CommRingCat.of A))
    (fun z => D.q n A hA (PP z)) (fun z => by obtain ⟨y, hy⟩ := hx z; exact ⟨z, y, hy⟩) (fun z => hopen z)

  haveI : IsAffineHom s := inferInstance
  haveI hp₁aff : IsAffineHom p₁ := MorphismProperty.of_isPullback hX'.flip inferInstance
  haveI hUaff : ∀ z, IsAffine (𝒰.X z) := fun _ => (inferInstance : IsAffine (Spec (CommRingCat.of A)))
  haveI hWaff : ∀ z, IsAffine ((𝒰.pullback₁ p₁).X z) := fun z => by
    haveI := hUaff z; exact (inferInstance : IsAffine (pullback p₁ (𝒰.f z)))

  let pbH : ∀ z, (𝒰.pullback₁ p₁).X z ⟶ Spec (CommRingCat.of A) := fun z => 𝒰.pullbackHom p₁ z
  have pc : ∀ z, pbH z ≫ D.q n A hA (PP z) = (𝒰.pullback₁ p₁).f z ≫ p₁ := fun z => Scheme.Cover.pullbackHom_map 𝒰 p₁ z
  let Γz : ↥(D.Z n) → CommRingCat := fun z => Γ((𝒰.pullback₁ p₁).X z, ⊤)
  let e : ∀ z, (𝒰.pullback₁ p₁).X z ≅ Spec (Γz z) := fun z => ((𝒰.pullback₁ p₁).X z).isoSpec
  let ψ : ∀ z, CommRingCat.of C ⟶ Γz z := fun z => Spec.preimage ((e z).inv ≫ (𝒰.pullback₁ p₁).f z ≫ p₂)
  let φ : ∀ z, CommRingCat.of A ⟶ Γz z := fun z => Spec.preimage ((e z).inv ≫ pbH z)
  have hψ : ∀ z, Spec.map (ψ z) = (e z).inv ≫ (𝒰.pullback₁ p₁).f z ≫ p₂ := fun z => Spec.map_preimage _
  have hφ : ∀ z, Spec.map (φ z) = (e z).inv ≫ pbH z := fun z => Spec.map_preimage _

  have hcompat : ∀ z, (φ z).hom.comp (algebraMap 𝒪 A) = (ψ z).hom.comp (algebraMap 𝒪 C) := by
    intro z
    apply ringHom_eq_of_spec_eq
    have e1 : CommRingCat.ofHom ((φ z).hom.comp (algebraMap 𝒪 A)) = CommRingCat.ofHom (algebraMap 𝒪 A) ≫ φ z := rfl
    have e2 : CommRingCat.ofHom ((ψ z).hom.comp (algebraMap 𝒪 C)) = CommRingCat.ofHom (algebraMap 𝒪 C) ≫ ψ z := rfl
    rw [e1, e2, Spec.map_comp, Spec.map_comp, hφ, hψ, ← D.q_over n A hA (PP z), ← hs]
    have key : pbH z ≫ D.q n A hA (PP z) ≫ D.zb n ≫
        Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) =
        (𝒰.pullback₁ p₁).f z ≫ p₂ ≫ s ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) := by
      rw [← Category.assoc, pc z, Category.assoc, hX'.w_assoc]
    simp only [Category.assoc] at key ⊢
    rw [key]

  letI algz : ∀ z, Algebra 𝒪 (Γz z) := fun z => ((ψ z).hom.comp (algebraMap 𝒪 C)).toAlgebra
  let cz : ∀ z, C →ₐ[𝒪] (Γz z) := fun z => { toRingHom := (ψ z).hom, commutes' := fun _ => rfl }
  let az : ∀ z, A →ₐ[𝒪] (Γz z) := fun z =>
    { toRingHom := (φ z).hom, commutes' := fun o => by
        show (φ z).hom (algebraMap 𝒪 A o) = (ψ z).hom (algebraMap 𝒪 C o)
        exact congrArg (fun f : 𝒪 →+* (Γz z) => f o) (hcompat z) }
  have hRz : ∀ z, (algebraMap 𝒪 (Γz z) π) ^ (n + 1) = 0 := by
    intro z; show ((ψ z).hom (algebraMap 𝒪 C π)) ^ (n + 1) = 0
    rw [← map_pow, hC, map_zero]
  let Pz : ∀ z, (Omega K₀ π).obj (Γz z) := fun z => (Omega K₀ π).map (az z) (PP z)

  have hqPz : ∀ z, D.q n (Γz z) (hRz z) (Pz z) = (e z).inv ≫ pbH z ≫ D.q n A hA (PP z) := by
    intro z
    show D.q n (Γz z) (hRz z) ((Omega K₀ π).map (az z) (PP z)) = _
    rw [D.q_natural n A (Γz z) hA (hRz z) (az z) (PP z), ← Category.assoc, ← hφ]; rfl

  refine Scheme.Cover.hom_ext (𝒰.pullback₁ p₁) w w' (fun z => ?_)
  have hx1 : ((e z).inv ≫ (𝒰.pullback₁ p₁).f z) ≫ p₁ = D.q n (Γz z) (hRz z) (Pz z) := by
    rw [hqPz z, Category.assoc, ← pc z]
  have hx2 : ((e z).inv ≫ (𝒰.pullback₁ p₁).f z) ≫ p₂ = Spec.map (CommRingCat.ofHom (cz z).toRingHom) := by
    rw [Category.assoc, ← hψ z]; rfl
  have key := h (Γz z) (hRz z) (cz z) (Pz z) ((e z).inv ≫ (𝒰.pullback₁ p₁).f z) hx1 hx2
  simp only [Category.assoc] at key
  exact (cancel_epi (e z).inv).1 key

end
end S_CerednikDrinfeld_FormalOmega_MumfordTower_hom_ext_of_comp_eq_of_q
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_MumfordTower_hom_ext_of_comp_eq_of_q (solution)
