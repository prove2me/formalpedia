-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.ker_eq_comap_ker_of_isPullback_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:02:42.86092+00:00
-- url     : https://prove2.me/submissions/354f50cd-4998-4649-a48c-85f7a6834ac8

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_KernelFlatBaseChange
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_ker_includeRight_eq_map_ker
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
namespace FunctorialResolution.EmbeddedResolution
private theorem algebraMap_tmul_one_eq_one_tmul_algebraMap {A B A' : Type*} [CommRing A] [CommRing B] [CommRing A']
    [Algebra A B] [Algebra A A'] (a : A) :
    (algebraMap A B a) ⊗ₜ[A] (1 : A') = (1 : B) ⊗ₜ[A] (algebraMap A A' a) := by
  calc (algebraMap A B a) ⊗ₜ[A] (1 : A') = (a • (1 : B)) ⊗ₜ[A] (1 : A') := by
        rw [Algebra.algebraMap_eq_smul_one]
    _ = a • ((1 : B) ⊗ₜ[A] (1 : A')) := TensorProduct.smul_tmul' a (1 : B) (1 : A')
    _ = (1 : B) ⊗ₜ[A] (a • (1 : A')) := (TensorProduct.tmul_smul a (1 : B) (1 : A')).symm
    _ = (1 : B) ⊗ₜ[A] (algebraMap A A' a) := by rw [Algebra.algebraMap_eq_smul_one]
private theorem exists_pow_mul_mem_of_map_le {A Af : Type*} [CommRing A] [CommRing Af]
    [Algebra A Af] (f : A) [IsLocalization.Away f Af] {I J : Ideal A}
    (hle : I.map (algebraMap A Af) ≤ J.map (algebraMap A Af)) {x : A} (hx : x ∈ I) :
    ∃ n : ℕ, f ^ n * x ∈ J := by
  have hmem : algebraMap A Af x ∈ J.map (algebraMap A Af) :=
    hle (Ideal.mem_map_of_mem _ hx)
  rw [IsLocalization.mem_map_algebraMap_iff (Submonoid.powers f) Af] at hmem
  obtain ⟨⟨⟨y, hy⟩, ⟨m, hm⟩⟩, hxy⟩ := hmem
  obtain ⟨k, hk⟩ := hm
  have hk' : f ^ k = m := hk
  rw [← map_mul] at hxy
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers f) Af).mp hxy
  obtain ⟨l, hl⟩ := c.2
  have hl' : f ^ l = (c : A) := hl
  have hc' : (c : A) * (x * m) = (c : A) * y := hc
  refine ⟨l + k, ?_⟩
  have key : f ^ (l + k) * x = (c : A) * (x * m) := by
    rw [pow_add, hl', ← hk']; ring
  rw [key, hc']
  exact Ideal.mul_mem_left _ _ hy
private theorem ideal_eq_of_span_eq_top {A : Type*} [CommRing A] {I J : Ideal A} {s : Set A}
    (hspan : Ideal.span s = ⊤)
    (hIJ : ∀ f ∈ s, ∀ x ∈ I, ∃ n : ℕ, f ^ n * x ∈ J)
    (hJI : ∀ f ∈ s, ∀ x ∈ J, ∃ n : ℕ, f ^ n * x ∈ I) : I = J := by
  apply le_antisymm
  · intro x hx
    refine Submodule.mem_of_span_eq_top_of_smul_pow_mem J s hspan x ?_
    rintro ⟨f, hf⟩
    obtain ⟨n, hn⟩ := hIJ f hf x hx
    exact ⟨n, by simpa [smul_eq_mul] using hn⟩
  · intro x hx
    refine Submodule.mem_of_span_eq_top_of_smul_pow_mem I s hspan x ?_
    rintro ⟨f, hf⟩
    obtain ⟨n, hn⟩ := hJI f hf x hx
    exact ⟨n, by simpa [smul_eq_mul] using hn⟩
private theorem ideal_eq_of_ideal_affineBasicOpen_eq {X : Scheme.{u}} (I J : X.IdealSheafData) (V : X.affineOpens)
    (s : Set Γ(X, (V : X.Opens))) (hspan : Ideal.span s = ⊤)
    (hs : ∀ f ∈ s, I.ideal (X.affineBasicOpen f) = J.ideal (X.affineBasicOpen f)) :
    I.ideal V = J.ideal V := by
  have key : ∀ I J : X.IdealSheafData,
      (∀ f ∈ s, I.ideal (X.affineBasicOpen f) = J.ideal (X.affineBasicOpen f)) →
      ∀ f ∈ s, ∀ x ∈ I.ideal V, ∃ n : ℕ, f ^ n * x ∈ J.ideal V := by
    intro I J hs f hf x hx
    have := V.2.isLocalization_basicOpen f
    have hmap : (I.ideal V).map (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
        = (J.ideal V).map (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom := by
      rw [I.map_ideal_basicOpen V f, J.map_ideal_basicOpen V f, hs f hf]
    exact exists_pow_mul_mem_of_map_le (Af := ↑Γ(X, X.basicOpen f)) f (le_of_eq hmap) hx
  exact ideal_eq_of_span_eq_top hspan (key I J hs) (key J I fun f hf => (hs f hf).symm)
private theorem span_eq_top_of_le_iSup_basicOpen {X : Scheme.{u}} (V : X.affineOpens)
    (s : Set ↑Γ(X, (V : X.Opens)))
    (hcov : (V : X.Opens) ≤ ⨆ f : s, X.basicOpen (f : ↑Γ(X, (V : X.Opens)))) :
    Ideal.span s = ⊤ :=
  (V.2.self_le_iSup_basicOpen_iff (s := s)).mp hcov
private theorem appLE_congr_of_eq {X Y : Scheme.{u}} {f f' : X ⟶ Y} (hf : f = f')
    (U : Y.Opens) (W : X.Opens) (e : W ≤ f ⁻¹ᵁ U) (e' : W ≤ f' ⁻¹ᵁ U) :
    f.appLE U W e = f'.appLE U W e' := by
  subst hf; rfl
private theorem pi_one_tmul_eq_zero_of_forall {R A' : Type*} [CommRing R] [CommRing A'] [Algebra R A']
    {ι : Type*} [Fintype ι] [DecidableEq ι] (B : ι → Type*) [∀ j, CommRing (B j)]
    [∀ j, Algebra R (B j)] (s : A') (hs : ∀ j, (1 : B j) ⊗ₜ[R] s = 0) :
    (1 : ∀ j, B j) ⊗ₜ[R] s = 0 := by
  have h1 : (1 : ∀ j, B j) = ∑ j : ι, Pi.single j (1 : B j) := by
    ext k
    simp [Finset.sum_apply]
  rw [h1, TensorProduct.sum_tmul]
  refine Finset.sum_eq_zero ?_
  intro j _
  have h2 : (Pi.single j (1 : B j)) ⊗ₜ[R] s
      = LinearMap.rTensor A' (LinearMap.single R B j) ((1 : B j) ⊗ₜ[R] s) := by
    simp
  rw [h2, hs j, map_zero]
private theorem mem_map_iInf_ker_of_forall_one_tmul_eq_zero {R A' : Type*} [CommRing R] [CommRing A']
    [Algebra R A'] [Module.Flat R A'] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : ι → Type*) [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)] (s : A')
    (hs : ∀ j, (1 : B j) ⊗ₜ[R] s = 0) :
    s ∈ Ideal.map (algebraMap R A') (⨅ j, RingHom.ker (algebraMap R (B j))) := by
  have h0 : (1 : ∀ j, B j) ⊗ₜ[R] s = 0 := pi_one_tmul_eq_zero_of_forall B s hs
  have hk : RingHom.ker (algebraMap R (∀ j, B j)) = ⨅ j, RingHom.ker (algebraMap R (B j)) := by
    ext r
    simp [RingHom.mem_ker, Submodule.mem_iInf, funext_iff]
  rw [← hk, ← ker_includeRight_eq_map_ker R (∀ j, B j) A']
  simpa [RingHom.mem_ker] using h0
private theorem exists_affineOpen_le_of_mem {Z : Scheme.{u}} (K : Z.Opens) (z : Z) (hz : z ∈ K) :
    ∃ W : Z.affineOpens, (W : Z.Opens) ≤ K ∧ z ∈ (W : Z.Opens) := by
  obtain ⟨y, hy⟩ := Z.affineCover.covers z
  have hWaff : IsAffineOpen (Z.affineCover.f (Z.affineCover.idx z)).opensRange :=
    isAffineOpen_opensRange _
  have hz1 : z ∈ (Z.affineCover.f (Z.affineCover.idx z)).opensRange := ⟨y, hy⟩
  obtain ⟨f, hfle, hzf⟩ := hWaff.exists_basicOpen_le (V := K) ⟨z, hz⟩ hz1
  exact ⟨⟨Z.basicOpen f, hWaff.basicOpen f⟩, hfle, hzf⟩
private theorem appLE_top_comp_ΓSpecIso_hom {Y : Scheme.{u}} {V : Y.Opens} (hV : IsAffineOpen V)
    {S : CommRingCat.{u}} (ρ : Γ(Y, V) ⟶ S) (q : Spec S ⟶ Y)
    (hqe : q = Spec.map ρ ≫ hV.fromSpec) (e : (⊤ : (Spec S).Opens) ≤ q ⁻¹ᵁ V) :
    q.appLE V ⊤ e ≫ (Scheme.ΓSpecIso S).hom = ρ := by
  subst hqe
  have : IsOpenImmersion hV.fromSpec := hV.isOpenImmersion_fromSpec
  have h1 : Spec.map ((Spec.map ρ ≫ hV.fromSpec).appLE V ⊤ e) ≫ hV.fromSpec
      = (isAffineOpen_top (Spec S)).fromSpec ≫ (Spec.map ρ ≫ hV.fromSpec) :=
    IsAffineOpen.SpecMap_appLE_fromSpec _ hV (isAffineOpen_top (Spec S)) e
  have h2 : (isAffineOpen_top (Spec S)).fromSpec = Spec.map (Scheme.ΓSpecIso S).inv := by
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
  rw [h2, ← Category.assoc, ← Spec.map_comp] at h1
  have h3 := (cancel_mono hV.fromSpec).mp h1
  have h4 := Spec.map_injective h3
  rw [h4, Category.assoc, Iso.inv_hom_id, Category.comp_id]
private theorem one_tmul_eq_zero_of_app_eq_zero {Z X X' Z' : Scheme.{u}} {h : Z ⟶ X} {g : X' ⟶ X}
    {g' : Z' ⟶ Z} {h' : Z' ⟶ X'} (H : IsPullback g' h' h g)
    (U : X.affineOpens) (V : X'.affineOpens) (e : (V : X'.Opens) ≤ g ⁻¹ᵁ (U : X.Opens))
    (W : Z.affineOpens) (hW : (W : Z.Opens) ≤ h ⁻¹ᵁ (U : X.Opens))
    [Algebra ↑Γ(X, (U : X.Opens)) ↑Γ(X', (V : X'.Opens))]
    [Algebra ↑Γ(X, (U : X.Opens)) ↑Γ(Z, (W : Z.Opens))]
    (hVa : (algebraMap ↑Γ(X, (U : X.Opens)) ↑Γ(X', (V : X'.Opens)))
        = (g.appLE (U : X.Opens) (V : X'.Opens) e).hom)
    (hWa : (algebraMap ↑Γ(X, (U : X.Opens)) ↑Γ(Z, (W : Z.Opens)))
        = (h.appLE (U : X.Opens) (W : Z.Opens) hW).hom)
    (s : ↑Γ(X', (V : X'.Opens))) (hs : (h'.app (V : X'.Opens)).hom s = 0) :
    (1 : ↑Γ(Z, (W : Z.Opens))) ⊗ₜ[↑Γ(X, (U : X.Opens))] s = 0 := by
  have hUaff : IsAffineOpen (U : X.Opens) := U.2
  have hVaff : IsAffineOpen (V : X'.Opens) := V.2
  have hWaff : IsAffineOpen (W : Z.Opens) := W.2
  set T : CommRingCat.{u} :=
    CommRingCat.of (↑Γ(Z, (W : Z.Opens)) ⊗[↑Γ(X, (U : X.Opens))] ↑Γ(X', (V : X'.Opens))) with hT
  set il : Γ(Z, (W : Z.Opens)) ⟶ T :=
    CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom) with hil
  set ir : Γ(X', (V : X'.Opens)) ⟶ T :=
    CommRingCat.ofHom (Algebra.TensorProduct.includeRight).toRingHom with hir
  have h3 : h.appLE (U : X.Opens) (W : Z.Opens) hW ≫ il
      = g.appLE (U : X.Opens) (V : X'.Opens) e ≫ ir := by
    ext a
    show ((h.appLE (U : X.Opens) (W : Z.Opens) hW).hom a) ⊗ₜ[↑Γ(X, (U : X.Opens))]
        (1 : ↑Γ(X', (V : X'.Opens)))
      = (1 : ↑Γ(Z, (W : Z.Opens))) ⊗ₜ[↑Γ(X, (U : X.Opens))]
        ((g.appLE (U : X.Opens) (V : X'.Opens) e).hom a)
    rw [← hWa, ← hVa]
    exact algebraMap_tmul_one_eq_one_tmul_algebraMap a
  set p : Spec T ⟶ Z := Spec.map il ≫ hWaff.fromSpec with hp
  set q : Spec T ⟶ X' := Spec.map ir ≫ hVaff.fromSpec with hq
  have hcomm : p ≫ h = q ≫ g := by
    have h1 : Spec.map (h.appLE (U : X.Opens) (W : Z.Opens) hW) ≫ hUaff.fromSpec
        = hWaff.fromSpec ≫ h := IsAffineOpen.SpecMap_appLE_fromSpec h hUaff hWaff hW
    have h2 : Spec.map (g.appLE (U : X.Opens) (V : X'.Opens) e) ≫ hUaff.fromSpec
        = hVaff.fromSpec ≫ g := IsAffineOpen.SpecMap_appLE_fromSpec g hUaff hVaff e
    calc p ≫ h = Spec.map il ≫ (hWaff.fromSpec ≫ h) := by rw [hp, Category.assoc]
      _ = Spec.map il ≫ Spec.map (h.appLE (U : X.Opens) (W : Z.Opens) hW) ≫ hUaff.fromSpec := by
          rw [h1]
      _ = Spec.map (h.appLE (U : X.Opens) (W : Z.Opens) hW ≫ il) ≫ hUaff.fromSpec := by
          rw [Spec.map_comp, Category.assoc]
      _ = Spec.map (g.appLE (U : X.Opens) (V : X'.Opens) e ≫ ir) ≫ hUaff.fromSpec := by rw [h3]
      _ = Spec.map ir ≫ Spec.map (g.appLE (U : X.Opens) (V : X'.Opens) e) ≫ hUaff.fromSpec := by
          rw [Spec.map_comp, Category.assoc]
      _ = Spec.map ir ≫ (hVaff.fromSpec ≫ g) := by rw [h2]
      _ = q ≫ g := by rw [hq, Category.assoc]
  have hr : H.lift p q hcomm ≫ h' = q := H.lift_snd p q hcomm
  have hqpre : q ⁻¹ᵁ (V : X'.Opens) = ⊤ := by
    rw [hq, Scheme.Hom.comp_preimage, hVaff.fromSpec_preimage_self, Scheme.Hom.preimage_top]
  have e1 : (⊤ : (Spec T).Opens) ≤ q ⁻¹ᵁ (V : X'.Opens) := hqpre.ge
  have hrp : H.lift p q hcomm ⁻¹ᵁ (h' ⁻¹ᵁ (V : X'.Opens)) = ⊤ := by
    rw [← Scheme.Hom.comp_preimage, hr, hqpre]
  have e2 : (⊤ : (Spec T).Opens) ≤ H.lift p q hcomm ⁻¹ᵁ (h' ⁻¹ᵁ (V : X'.Opens)) := hrp.ge
  have hsplit : q.appLE (V : X'.Opens) ⊤ e1
      = h'.appLE (V : X'.Opens) (h' ⁻¹ᵁ (V : X'.Opens)) le_rfl
        ≫ (H.lift p q hcomm).appLE (h' ⁻¹ᵁ (V : X'.Opens)) ⊤ e2 := by
    rw [Scheme.Hom.appLE_comp_appLE]
    exact appLE_congr_of_eq hr.symm _ _ _ _
  have hA : (q.appLE (V : X'.Opens) ⊤ e1).hom s = 0 := by
    rw [hsplit]
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
    rw [← Scheme.Hom.app_eq_appLE h' (U := (V : X'.Opens)), hs, map_zero]
  have hfin : q.appLE (V : X'.Opens) ⊤ e1 ≫ (Scheme.ΓSpecIso T).hom = ir :=
    appLE_top_comp_ΓSpecIso_hom hVaff ir q hq e1
  have step : ir.hom s = 0 := by
    rw [← hfin]
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
    rw [hA, map_zero]
  exact step
private theorem ker_app_eq_map_ker_of_isPullback_of_flat {Z X X' Z' : Scheme.{u}} {h : Z ⟶ X} {g : X' ⟶ X}
    {g' : Z' ⟶ Z} {h' : Z' ⟶ X'} (H : IsPullback g' h' h g) [QuasiCompact h]
    [AlgebraicGeometry.Flat g] (U : X.affineOpens) (V : X'.affineOpens)
    (e : (V : X'.Opens) ≤ g ⁻¹ᵁ (U : X.Opens)) :
    RingHom.ker (h'.app (V : X'.Opens)).hom =
      Ideal.map (g.appLE (U : X.Opens) (V : X'.Opens) e).hom
        (RingHom.ker (h.app (U : X.Opens)).hom) := by
  classical
  have hpre : h' ⁻¹ᵁ (V : X'.Opens) ≤ g' ⁻¹ᵁ (h ⁻¹ᵁ (U : X.Opens)) := by
    rw [← Scheme.Hom.comp_preimage, H.w, Scheme.Hom.comp_preimage]
    exact fun x hx => e hx
  have hcomm : h.appLE (U : X.Opens) (h ⁻¹ᵁ (U : X.Opens)) le_rfl
      ≫ g'.appLE (h ⁻¹ᵁ (U : X.Opens)) (h' ⁻¹ᵁ (V : X'.Opens)) hpre
      = g.appLE (U : X.Opens) (V : X'.Opens) e
        ≫ h'.appLE (V : X'.Opens) (h' ⁻¹ᵁ (V : X'.Opens)) le_rfl := by
    rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
    exact appLE_congr_of_eq H.w _ _ _ _
  apply le_antisymm
  · intro s hs
    have hs0 : (h'.app (V : X'.Opens)).hom s = 0 := RingHom.mem_ker.mp hs
    have hKc : IsCompact (((h ⁻¹ᵁ (U : X.Opens)) : Z.Opens) : Set Z) :=
      QuasiCompact.isCompact_preimage (f := h) (((U : X.Opens)) : Set X)
        (U : X.Opens).isOpen U.2.isCompact
    have hcov : (((h ⁻¹ᵁ (U : X.Opens)) : Z.Opens) : Set Z)
        ⊆ ⋃ W : {W : Z.affineOpens // (W : Z.Opens) ≤ h ⁻¹ᵁ (U : X.Opens)},
            (((W.1 : Z.affineOpens) : Z.Opens) : Set Z) := by
      intro z hz
      obtain ⟨W, hW1, hW2⟩ := exists_affineOpen_le_of_mem (h ⁻¹ᵁ (U : X.Opens)) z hz
      exact Set.mem_iUnion.mpr ⟨⟨W, hW1⟩, hW2⟩
    obtain ⟨t, ht⟩ := hKc.elim_finite_subcover
      (fun W : {W : Z.affineOpens // (W : Z.Opens) ≤ h ⁻¹ᵁ (U : X.Opens)} =>
        (((W.1 : Z.affineOpens) : Z.Opens) : Set Z))
      (fun W => ((W.1 : Z.affineOpens) : Z.Opens).isOpen) hcov
    let _ : Algebra ↑Γ(X, (U : X.Opens)) ↑Γ(X', (V : X'.Opens)) :=
      (g.appLE (U : X.Opens) (V : X'.Opens) e).hom.toAlgebra
    have hflat : RingHom.Flat (g.appLE (U : X.Opens) (V : X'.Opens) e).hom :=
      AlgebraicGeometry.HasRingHomProperty.appLE (P := @AlgebraicGeometry.Flat) g ‹_› U V e
    have : Module.Flat ↑Γ(X, (U : X.Opens)) ↑Γ(X', (V : X'.Opens)) := hflat
    let _ : ∀ j : {x // x ∈ t},
        Algebra ↑Γ(X, (U : X.Opens)) ↑Γ(Z, ((j.1.1 : Z.affineOpens) : Z.Opens)) :=
      fun j => (h.appLE (U : X.Opens) ((j.1.1 : Z.affineOpens) : Z.Opens) j.1.2).hom.toAlgebra
    have hzero : ∀ j : {x // x ∈ t},
        (1 : ↑Γ(Z, ((j.1.1 : Z.affineOpens) : Z.Opens)))
          ⊗ₜ[↑Γ(X, (U : X.Opens))] s = 0 := by
      intro j
      exact one_tmul_eq_zero_of_app_eq_zero H U V e j.1.1 j.1.2 rfl rfl s hs0
    have hmem := mem_map_iInf_ker_of_forall_one_tmul_eq_zero
      (fun j : {x // x ∈ t} => ↑Γ(Z, ((j.1.1 : Z.affineOpens) : Z.Opens))) s hzero
    have hcover2 : (h ⁻¹ᵁ (U : X.Opens))
        ≤ ⨆ j : {x // x ∈ t}, ((j.1.1 : Z.affineOpens) : Z.Opens) := by
      intro z hz
      obtain ⟨W, hW1, hW2⟩ := Set.mem_iUnion₂.mp (ht hz)
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨W, hW1⟩, hW2⟩
    have hker : (⨅ j : {x // x ∈ t}, RingHom.ker
          (algebraMap ↑Γ(X, (U : X.Opens)) ↑Γ(Z, ((j.1.1 : Z.affineOpens) : Z.Opens))))
        ≤ RingHom.ker (h.app (U : X.Opens)).hom := by
      intro a ha
      rw [RingHom.mem_ker]
      refine Z.sheaf.eq_of_locally_eq'
        (fun j : {x // x ∈ t} => ((j.1.1 : Z.affineOpens) : Z.Opens))
        (h ⁻¹ᵁ (U : X.Opens)) (fun j => homOfLE j.1.2) hcover2 _ 0 ?_
      intro j
      have ha' : (algebraMap ↑Γ(X, (U : X.Opens))
          ↑Γ(Z, ((j.1.1 : Z.affineOpens) : Z.Opens))) a = 0 :=
        RingHom.mem_ker.mp ((Submodule.mem_iInf _).mp ha j)
      have ha3 : (Z.presheaf.map (homOfLE j.1.2).op).hom
          ((h.app (U : X.Opens)).hom a) = 0 := ha'
      refine ha3.trans ?_
      exact (map_zero _).symm
    exact Ideal.map_mono hker hmem
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have h1 := congrArg (fun m : Γ(X, (U : X.Opens)) ⟶ Γ(Z', h' ⁻¹ᵁ (V : X'.Opens)) =>
      (CommRingCat.Hom.hom m) a) hcomm
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h1
    have hzero : (h.appLE (U : X.Opens) (h ⁻¹ᵁ (U : X.Opens)) le_rfl).hom a = 0 := by
      rw [← Scheme.Hom.app_eq_appLE h (U := (U : X.Opens))]
      exact RingHom.mem_ker.mp ha
    rw [Scheme.Hom.app_eq_appLE h' (U := (V : X'.Opens)), ← h1, hzero, map_zero]
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TensorProduct
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {Z X X' Z' : Scheme.{u}} {h : Z ⟶ X} {g : X' ⟶ X}
    {g' : Z' ⟶ Z} {h' : Z' ⟶ X'} (H : IsPullback g' h' h g)
    [QuasiCompact h] [QuasiCompact h'] [AlgebraicGeometry.Flat g] :
    h'.ker = h.ker.comap g := by
  classical
  apply Scheme.IdealSheafData.ext
  funext V
  set s : Set Γ(X', (V : X'.Opens)) :=
    {f | ∃ U : X.affineOpens, X'.basicOpen f ≤ g ⁻¹ᵁ (U : X.Opens)} with hsdef
  have hs : ∀ f ∈ s, h'.ker.ideal (X'.affineBasicOpen f)
      = (h.ker.comap g).ideal (X'.affineBasicOpen f) := by
    rintro f ⟨U, hU⟩
    have hV' : ((X'.affineBasicOpen f : X'.affineOpens) : X'.Opens) ≤ g ⁻¹ᵁ (U : X.Opens) := hU
    rw [AlgebraicGeometry.Scheme.IdealSheafData.comap_ideal_eq_map_appLE h.ker g U
      (X'.affineBasicOpen f) hV', Scheme.Hom.ker_apply, Scheme.Hom.ker_apply]
    exact ker_app_eq_map_ker_of_isPullback_of_flat H U (X'.affineBasicOpen f) hV'
  have hspan : Ideal.span s = ⊤ := by
    refine span_eq_top_of_le_iSup_basicOpen V s ?_
    intro x hx
    obtain ⟨y, hy⟩ := X.affineCover.covers (g.base x)
    have hUaff : IsAffineOpen (X.affineCover.f (X.affineCover.idx (g.base x))).opensRange :=
      isAffineOpen_opensRange _
    have hgx : g.base x ∈ (X.affineCover.f (X.affineCover.idx (g.base x))).opensRange := ⟨y, hy⟩
    have hx2 : x ∈ ((V : X'.Opens) ⊓
        g ⁻¹ᵁ (X.affineCover.f (X.affineCover.idx (g.base x))).opensRange) := ⟨hx, hgx⟩
    obtain ⟨f, hfle, hxf⟩ := V.2.exists_basicOpen_le
      (V := (V : X'.Opens) ⊓ g ⁻¹ᵁ (X.affineCover.f (X.affineCover.idx (g.base x))).opensRange)
      ⟨x, hx2⟩ hx
    have hfs : f ∈ s :=
      ⟨⟨(X.affineCover.f (X.affineCover.idx (g.base x))).opensRange, hUaff⟩,
        le_trans hfle inf_le_right⟩
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨f, hfs⟩, hxf⟩
  exact ideal_eq_of_ideal_affineBasicOpen_eq _ _ V s hspan hs
end FunctorialResolution.EmbeddedResolution
