-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.Omega.exists_opens_forall_edgeNondegAt_iff_mem_of_natural
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/f888148f-7267-54a1-9122-faf16a2a0c8b

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_isOpen_setOf_edgeNondegAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_Omega_exists_opens_forall_edgeNondegAt_iff_mem_of_natural

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

noncomputable section

namespace OPRE

section edgeBC

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
  {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (f : B →ₐ[𝒪] B')

theorem rTensor_mem_lineBaseChange_sup (L : FullLattice 𝒪 K) (N : Submodule B (latticeBaseChange 𝒪 K B L)) (𝔭' : Ideal B')
    (x : latticeBaseChange 𝒪 K B L)
    (hx : x ∈ N ⊔ (Ideal.comap f 𝔭' • ⊤ : Submodule B (latticeBaseChange 𝒪 K B L))) :
    LinearMap.rTensor (↥L.1) f.toLinearMap x ∈
      lineBaseChange f L N ⊔ (𝔭' • ⊤ : Submodule B' (latticeBaseChange 𝒪 K B' L)) := by
  obtain ⟨n, hn, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add]
  refine Submodule.add_mem_sup (Submodule.subset_span ⟨n, hn, rfl⟩) ?_
  refine Submodule.smul_induction_on (p := fun y => LinearMap.rTensor (↥L.1) f.toLinearMap y ∈
      (𝔭' • ⊤ : Submodule B' (latticeBaseChange 𝒪 K B' L))) hz (fun r hr y _ => ?_) (fun a b ha hb => ?_)
  · show LinearMap.rTensor (↥L.1) f.toLinearMap (r • y) ∈ _
    rw [rTensor_smul_left f L r y]
    exact Submodule.smul_mem_smul (Ideal.mem_comap.1 hr) Submodule.mem_top
  · show LinearMap.rTensor (↥L.1) f.toLinearMap (a + b) ∈ (𝔭' • ⊤ : Submodule B' (latticeBaseChange 𝒪 K B' L))
    rw [map_add]
    exact Submodule.add_mem _ ha hb

theorem one_tmul_not_mem_map_iff (d : DeligneDatum (K := K) π B) (𝔭' : Ideal B') [𝔭'.IsPrime] (L : FullLattice 𝒪 K) (v : ↥L.1) :
    ((1 : B') ⊗ₜ[𝒪] v ∉ (DeligneDatum.map π f d).line L ⊔ (𝔭' • ⊤ : Submodule B' (latticeBaseChange 𝒪 K B' L))) ↔
      ((1 : B) ⊗ₜ[𝒪] v ∉ d.line L ⊔ (Ideal.comap f 𝔭' • ⊤ : Submodule B (latticeBaseChange 𝒪 K B L))) := by
  constructor
  · intro h hv
    exact h (by rw [← rTensor_one_tmul f L v]; exact rTensor_mem_lineBaseChange_sup f L (d.line L) 𝔭' _ hv)
  · intro h
    rw [← rTensor_one_tmul f L v]
    exact rTensor_not_mem_lineBaseChange_sup f L (d.line L) (d.invertible L) 𝔭' _ h

theorem edgeNondegAt_map_iff (π : 𝒪) {B B' : Type} [CommRing B] [Algebra 𝒪 B] [CommRing B'] [Algebra 𝒪 B']
    (f : B →ₐ[𝒪] B') (d : DeligneDatum (K := K) π B) (𝔭' : Ideal B') [𝔭'.IsPrime] (M' M : FullLattice 𝒪 K) :
    (DeligneDatum.map π f d).EdgeNondegAt π 𝔭' M' M ↔ d.EdgeNondegAt π (Ideal.comap f 𝔭') M' M := by
  show (_ ∧ _ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _ ∧ _)
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr ?_ ?_))
  · exact forall_congr' fun v => imp_congr_right fun _ => one_tmul_not_mem_map_iff f d 𝔭' M v
  · exact forall_congr' fun v' => imp_congr_right fun _ => one_tmul_not_mem_map_iff f d 𝔭' M' v'

end edgeBC

section Charts

variable {C : Type} [CommRing C] {X : Scheme.{0}}

def A (fX : X ⟶ Spec (CommRingCat.of C)) (V : X.affineOpens) : Type := Γ(X, V)

variable (fX : X ⟶ Spec (CommRingCat.of C)) (V : X.affineOpens)

scoped instance : CommRing (A fX V) := inferInstanceAs (CommRing Γ(X, V))

def ι : Spec (CommRingCat.of (A fX V)) ⟶ X := V.2.fromSpec

scoped instance : IsOpenImmersion (ι fX V) := V.2.isOpenImmersion_fromSpec

theorem range_ι : Set.range (ι fX V).base = (V : Set X) := V.2.range_fromSpec

def chartHom : C →+* A fX V := (Spec.preimage (ι fX V ≫ fX)).hom

scoped instance algC : Algebra C (A fX V) := (chartHom fX V).toAlgebra

theorem ι_comp : ι fX V ≫ fX = Spec.map (CommRingCat.ofHom (algebraMap C (A fX V))) := by
  rw [RingHom.algebraMap_toAlgebra]
  show ι fX V ≫ fX = Spec.map (CommRingCat.ofHom (Spec.preimage (ι fX V ≫ fX)).hom)
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]

def τ : (Scheme.nilpPoints fX).obj (A fX V) := ⟨ι fX V, ι_comp fX V⟩

variable {𝒪 : Type} [CommRing 𝒪] [Algebra 𝒪 C]

scoped instance (priority := low) algO : Algebra 𝒪 (A fX V) := ((algebraMap C (A fX V)).comp (algebraMap 𝒪 C)).toAlgebra

scoped instance tower : IsScalarTower 𝒪 C (A fX V) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

scoped instance noeth [IsNoetherianRing C] [LocallyOfFiniteType fX] : IsNoetherianRing (A fX V) := by
  haveI : IsNoetherianRing Γ(Spec (CommRingCat.of C), ⊤) :=
    isNoetherianRing_of_ringEquiv C (Scheme.ΓSpecIso (CommRingCat.of C)).symm.commRingCatIsoToRingEquiv
  letI : Algebra Γ(Spec (CommRingCat.of C), ⊤) (A fX V) := (fX.appLE ⊤ V.1 le_top).hom.toAlgebra
  haveI : Algebra.FiniteType Γ(Spec (CommRingCat.of C), ⊤) (A fX V) :=
    fX.finiteType_appLE (isAffineOpen_top _) V.2 le_top
  exact Algebra.FiniteType.isNoetherianRing Γ(Spec (CommRingCat.of C), ⊤) (A fX V)

end Charts

end OPRE
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_Omega_exists_opens_forall_edgeNondegAt_iff_mem_of_natural.OPRE"

open OPRE in
theorem solution

    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (π : 𝒪) (hπ : Irreducible π) (q : ℕ) (hq : Nat.card (𝒪 ⧸ Ideal.span {π}) = q) [Finite (𝒪 ⧸ Ideal.span {π})]

    (C : Type) [CommRing C] [IsNoetherianRing C] [Algebra 𝒪 C] (hC : IsNilpotent (algebraMap 𝒪 C π))
    (X : Scheme.{0}) (fX : X ⟶ Spec (CommRingCat.of C)) [LocallyOfFiniteType fX]

    (θ : ∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S],
      (Scheme.nilpPoints fX).obj S → (Omega K₀ π).obj S)
    (hnat : ∀ (S S' : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
      [CommRing S'] [Algebra C S'] [IsNoetherianRing S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 C S']
      (g : S →ₐ[C] S') (x : (Scheme.nilpPoints fX).obj S),
      θ S' ((Scheme.nilpPoints fX).map g x) = (Omega K₀ π).map (g.restrictScalars 𝒪) (θ S x))

    (M' M : FullLattice 𝒪 K₀) (hle : M'.1 ≤ M.1) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K₀ π • v ∈ M'.1) :
    ∃ U : X.Opens,
      ∀ (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
        (x : (Scheme.nilpPoints fX).obj S) (𝔮 : Ideal S) (h𝔮 : 𝔮.IsPrime),
        DeligneDatum.EdgeNondegAt π (θ S x) 𝔮 M' M ↔ x.1.base ⟨𝔮, h𝔮⟩ ∈ U  := by
  classical

  have hB : ∀ V : X.affineOpens, IsNilpotent (algebraMap 𝒪 (A fX V) π) := fun V => by
    rw [IsScalarTower.algebraMap_apply 𝒪 C (A fX V)]; exact hC.map _
  let d : ∀ V : X.affineOpens, (Omega K₀ π).obj (A fX V) := fun V => θ (A fX V) (τ fX V)
  let locus : ∀ V : X.affineOpens, (Spec (CommRingCat.of (A fX V))).Opens := fun V =>
    ⟨{𝔭 : PrimeSpectrum (A fX V) | DeligneDatum.EdgeNondegAt π (d V) 𝔭.asIdeal M' M},
      DeligneDatum.isOpen_setOf_edgeNondegAt π (hB V) (d V) M' M⟩
  refine ⟨⨆ V : X.affineOpens, (ι fX V) ''ᵁ (locus V), ?_⟩
  intro S _ _ _ _ _ x 𝔮 h𝔮
  haveI : 𝔮.IsPrime := h𝔮

  have key : ∀ V : X.affineOpens, x.1.base ⟨𝔮, h𝔮⟩ ∈ (V : Set X) →
      (DeligneDatum.EdgeNondegAt π (θ S x) 𝔮 M' M ↔
        x.1.base ⟨𝔮, h𝔮⟩ ∈ (((ι fX V) ''ᵁ (locus V) : X.Opens) : Set X)) := by
    intro V hyV

    have hopen : IsOpen (x.1.base ⁻¹' (V : Set X)) := (V : X.Opens).isOpen.preimage x.1.base.hom.continuous
    obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, h𝔮r, hrV⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open
        (show (⟨𝔮, h𝔮⟩ : PrimeSpectrum S) ∈ x.1.base ⁻¹' (V : Set X) from hyV) hopen

    let Sr : Type := Localization.Away r
    let lS : S →ₐ[C] Sr := IsScalarTower.toAlgHom C S Sr
    let xr : (Scheme.nilpPoints fX).obj Sr := (Scheme.nilpPoints fX).map lS x
    have hxr : xr.1 = Spec.map (CommRingCat.ofHom (algebraMap S Sr)) ≫ x.1 := rfl

    have hrange : Set.range xr.1.base ⊆ Set.range (ι fX V).base := by
      rw [range_ι, hxr]
      rintro _ ⟨z, rfl⟩
      apply hrV
      show (Spec.map (CommRingCat.ofHom (algebraMap S Sr))).base z ∈ (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum S))
      rw [← PrimeSpectrum.localization_away_comap_range Sr r]
      exact ⟨z, rfl⟩
    let l : Spec (CommRingCat.of Sr) ⟶ Spec (CommRingCat.of (A fX V)) := IsOpenImmersion.lift (ι fX V) xr.1 hrange
    have hl : l ≫ ι fX V = xr.1 := IsOpenImmersion.lift_fac _ _ _
    let g₀ : A fX V →+* Sr := (Spec.preimage l).hom
    have hg₀ : Spec.map (CommRingCat.ofHom g₀) = l := by
      show Spec.map (CommRingCat.ofHom (Spec.preimage l).hom) = l
      rw [CommRingCat.ofHom_hom, Spec.map_preimage]

    have hgC : g₀.comp (algebraMap C (A fX V)) = algebraMap C Sr := by
      have h1 : Spec.map (CommRingCat.ofHom (g₀.comp (algebraMap C (A fX V)))) =
          Spec.map (CommRingCat.ofHom (algebraMap C Sr)) := by
        rw [CommRingCat.ofHom_comp, Spec.map_comp, hg₀, ← ι_comp, ← Category.assoc, hl]
        exact xr.2
      have h2 := Spec.map_injective h1
      rw [← CommRingCat.hom_ofHom (g₀.comp (algebraMap C (A fX V))), h2, CommRingCat.hom_ofHom]
    let g : A fX V →ₐ[C] Sr :=
      { toRingHom := g₀, commutes' := fun c => by
          show g₀ (algebraMap C (A fX V) c) = algebraMap C Sr c
          rw [← RingHom.comp_apply, hgC] }
    have hτ : (Scheme.nilpPoints fX).map g (τ fX V) = xr := by
      apply Subtype.ext
      rw [Scheme.nilpPoints_map_val]
      show Spec.map (CommRingCat.ofHom g₀) ≫ ι fX V = xr.1
      rw [hg₀, hl]

    have hdisj : Disjoint (↑(Submonoid.powers r) : Set S) ↑𝔮 := by
      rw [Set.disjoint_left]
      rintro _ ⟨n, rfl⟩ hn
      exact h𝔮r (h𝔮.mem_of_pow_mem n hn)
    let 𝔮r : Ideal Sr := Ideal.map (algebraMap S Sr) 𝔮
    haveI h𝔮r : 𝔮r.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers r) Sr 𝔮 h𝔮 hdisj
    have hunder : 𝔮r.comap (algebraMap S Sr) = 𝔮 :=
      IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers r) Sr h𝔮 hdisj

    have n1 : θ Sr xr = (Omega K₀ π).map (lS.restrictScalars 𝒪) (θ S x) := hnat S Sr lS x
    have n2 : θ Sr xr = (Omega K₀ π).map (g.restrictScalars 𝒪) (d V) := by
      rw [← hτ]; exact hnat (A fX V) Sr g (τ fX V)

    have e1 : DeligneDatum.EdgeNondegAt π (θ S x) 𝔮 M' M ↔ DeligneDatum.EdgeNondegAt π (θ Sr xr) 𝔮r M' M := by
      rw [n1]
      have := OPRE.edgeNondegAt_map_iff (K := K₀) π (lS.restrictScalars 𝒪) (θ S x) 𝔮r M' M
      have hc : 𝔮r.comap (lS.restrictScalars 𝒪) = 𝔮 := hunder
      rw [hc] at this
      exact this.symm
    have e2 : DeligneDatum.EdgeNondegAt π (θ Sr xr) 𝔮r M' M ↔
        DeligneDatum.EdgeNondegAt π (d V) (𝔮r.comap g₀) M' M := by
      rw [n2]
      exact OPRE.edgeNondegAt_map_iff (K := K₀) π (g.restrictScalars 𝒪) (d V) 𝔮r M' M

    have hpt : (ι fX V).base ⟨𝔮r.comap g₀, Ideal.IsPrime.comap g₀⟩ = x.1.base ⟨𝔮, h𝔮⟩ := by
      have h1 : l.base ⟨𝔮r, h𝔮r⟩ = ⟨𝔮r.comap g₀, Ideal.IsPrime.comap g₀⟩ := by rw [← hg₀]; rfl
      have h2 : (ι fX V).base (l.base ⟨𝔮r, h𝔮r⟩) = (l ≫ ι fX V).base ⟨𝔮r, h𝔮r⟩ := rfl
      have h3 : (Spec.map (CommRingCat.ofHom (algebraMap S Sr)) ≫ x.1).base ⟨𝔮r, h𝔮r⟩ =
          x.1.base ((Spec.map (CommRingCat.ofHom (algebraMap S Sr))).base ⟨𝔮r, h𝔮r⟩) := rfl
      have h4 : (Spec.map (CommRingCat.ofHom (algebraMap S Sr))).base ⟨𝔮r, h𝔮r⟩ = ⟨𝔮, h𝔮⟩ :=
        PrimeSpectrum.ext hunder
      rw [← h1, h2, hl, hxr, h3, h4]
    rw [e1, e2]
    constructor
    · intro h
      exact ⟨⟨𝔮r.comap g₀, Ideal.IsPrime.comap g₀⟩, h, hpt⟩
    · rintro ⟨p, hp, hpy⟩
      have : p = ⟨𝔮r.comap g₀, Ideal.IsPrime.comap g₀⟩ :=
        (ι fX V).isOpenEmbedding.injective (hpy.trans hpt.symm)
      subst this
      exact hp

  constructor
  · intro h
    obtain ⟨V, hV, hyV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (x.1.base ⟨𝔮, h𝔮⟩)) isOpen_univ
    obtain ⟨W, hW, rfl⟩ := hV
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨W, hW⟩, (key ⟨W, hW⟩ hyV.1).mp h⟩
  · intro h
    obtain ⟨V, hV⟩ := TopologicalSpace.Opens.mem_iSup.mp h
    have hyV : x.1.base ⟨𝔮, h𝔮⟩ ∈ (V : Set X) := by
      rw [← range_ι fX V]
      obtain ⟨p, _, hp⟩ := hV
      exact ⟨p, hp⟩
    exact (key V hyV).mpr hV

end
end S_CerednikDrinfeld_FormalOmega_Omega_exists_opens_forall_edgeNondegAt_iff_mem_of_natural
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_Omega_exists_opens_forall_edgeNondegAt_iff_mem_of_natural (solution)
