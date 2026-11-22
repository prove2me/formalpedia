-- Prove2me | solution 1 for CGWH.regular
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T15:46:26.809995+00:00
-- url     : https://prove2.me/submissions/f05b7861-1cf1-4f10-8bc6-8ceb463618be

import Definitions.Def_CGWH_WeakHausdorff
import Theorems.Thm_CGWH_isRightAdjoint_forgetToCG_and_hasLimits_and_hasColimits
import Theorems.Thm_CGWH_mono_epi_isRegularMono_isRegularEpi_iff
import Theorems.Thm_CGWH_isQuotientMap_snd_pullback
import Theorems.Thm_CGWH_weaklyHausdorffSpace_subtype_and_compactlyGenerated
import Theorems.Thm_CGWH_weaklyHausdorffSpace_pi_and_prod

open CategoryTheory Topology TopologicalSpace

set_option autoImplicit false

universe u

namespace Sol_CGWH_regular

open CGWH CategoryTheory.Limits

/-! ### The `k`-ification -/

/-- The `k`-ification of a topology is finer than the topology. -/
theorem compactlyGenerated_le (W : Type u) [t : TopologicalSpace W] :
    compactlyGenerated.{u} W ≤ t := by
  simp only [compactlyGenerated, ← continuous_iff_coinduced_le, continuous_sigma_iff,
    Sigma.forall]
  exact fun S f ↦ f.2

/-- A continuous map from a compact Hausdorff space (of the universe of `W`) to `W` is continuous
for the `k`-ified topology of `W`. -/
theorem continuous_kTop_of_compact {K W : Type u} [TopologicalSpace K] [CompactSpace K]
    [T2Space K] [t : TopologicalSpace W] {φ : K → W} (hφ : Continuous φ) :
    Continuous[inferInstance, compactlyGenerated.{u} W] φ := by
  let f : (Σ (i : (S : CompHaus.{u}) × C(S, W)), i.fst) → W := fun ⟨⟨_, i⟩, s⟩ ↦ i s
  suffices h : ∀ (i : (T : CompHaus.{u}) × C(T, W)),
      Continuous[inferInstance, compactlyGenerated.{u} W] (fun (a : i.fst) ↦ f ⟨i, a⟩) from
    h ⟨CompHaus.of K, ⟨φ, hφ⟩⟩
  rw [← @continuous_sigma_iff]
  apply continuous_coinduced_rng

/-- The `k`-ification of a topological space is compactly generated. -/
theorem compactlyGeneratedSpace_kTop (W : Type u) [t : TopologicalSpace W] :
    @CompactlyGeneratedSpace W (compactlyGenerated.{u} W) := by
  refine @uCompactlyGeneratedSpace_of_continuous_maps W (compactlyGenerated.{u} W)
    fun {Y} tY f h => ?_
  refine @continuous_from_compactlyGenerated W Y t tY f fun S g => ?_
  exact h S (@ContinuousMap.mk _ _ _ (compactlyGenerated.{u} W) g
    (continuous_kTop_of_compact (t := t) g.continuous))

/-! ### The fibre product of `CGWH` -/

/-- The set-theoretic fibre product `B ×_S A` of two maps `φ : B → S` and `ψ : A → S`. -/
def FibProd {B A S : Type u} (φ : B → S) (ψ : A → S) : Type u :=
  {p : B × A // φ p.1 = ψ p.2}

/-- The fibre product carries the `k`-ification of the subspace topology of `B × A`. -/
instance instTopFibProd {B A S : Type u} [TopologicalSpace B] [TopologicalSpace A]
    (φ : B → S) (ψ : A → S) : TopologicalSpace (FibProd φ ψ) :=
  compactlyGenerated.{u} {p : B × A // φ p.1 = ψ p.2}

instance instCGFibProd {B A S : Type u} [TopologicalSpace B] [TopologicalSpace A]
    (φ : B → S) (ψ : A → S) : CompactlyGeneratedSpace (FibProd φ ψ) :=
  compactlyGeneratedSpace_kTop {p : B × A // φ p.1 = ψ p.2}

instance instWHFibProd {B A S : Type u} [TopologicalSpace B] [TopologicalSpace A]
    [WeaklyHausdorffSpace B] [WeaklyHausdorffSpace A]
    (φ : B → S) (ψ : A → S) : WeaklyHausdorffSpace (FibProd φ ψ) := by
  have h1 : WeaklyHausdorffSpace (B × A) := weaklyHausdorffSpace_pi_and_prod.2 B A
  have h2 : WeaklyHausdorffSpace {p : B × A // φ p.1 = ψ p.2} :=
    (weaklyHausdorffSpace_subtype_and_compactlyGenerated (B × A)).1 {p | φ p.1 = ψ p.2}
  exact (weaklyHausdorffSpace_subtype_and_compactlyGenerated
    {p : B × A // φ p.1 = ψ p.2}).2

theorem continuous_fst_fibProd {B A S : Type u} [TopologicalSpace B] [TopologicalSpace A]
    (φ : B → S) (ψ : A → S) : Continuous (fun p : FibProd φ ψ => p.1.1) := by
  have h : Continuous (fun p : {p : B × A // φ p.1 = ψ p.2} => p.1.1) :=
    continuous_fst.comp continuous_subtype_val
  exact continuous_le_dom (compactlyGenerated_le {p : B × A // φ p.1 = ψ p.2}) h

theorem continuous_snd_fibProd {B A S : Type u} [TopologicalSpace B] [TopologicalSpace A]
    (φ : B → S) (ψ : A → S) : Continuous (fun p : FibProd φ ψ => p.1.2) := by
  have h : Continuous (fun p : {p : B × A // φ p.1 = ψ p.2} => p.1.2) :=
    continuous_snd.comp continuous_subtype_val
  exact continuous_le_dom (compactlyGenerated_le {p : B × A // φ p.1 = ψ p.2}) h

/-! ### Objects and morphisms of `CGWH` -/

instance instWeaklyHausdorffSpaceObj (X : CGWHCat.{u}) : WeaklyHausdorffSpace X.obj := X.property

/-- The object of `CGWH` defined by a compactly generated weakly Hausdorff space. -/
abbrev obj (T : Type u) [TopologicalSpace T] [CompactlyGeneratedSpace T]
    [WeaklyHausdorffSpace T] : CGWHCat.{u} :=
  ⟨CompactlyGenerated.of T, ‹WeaklyHausdorffSpace T›⟩

/-- The morphism of `CGWH` defined by a continuous map. -/
abbrev homOf {X Y : CGWHCat.{u}} (φ : C(X.obj, Y.obj)) : X ⟶ Y :=
  ObjectProperty.homMk (ConcreteCategory.ofHom φ)

theorem hom_ext_fun {X Y : CGWHCat.{u}} {f g : X ⟶ Y}
    (h : ∀ x : X.obj, ConcreteCategory.hom f.hom x = ConcreteCategory.hom g.hom x) : f = g := by
  apply ObjectProperty.hom_ext
  exact ConcreteCategory.hom_ext _ _ h

theorem congr_fun_hom {X Y : CGWHCat.{u}} {f g : X ⟶ Y} (h : f = g) (x : X.obj) :
    ConcreteCategory.hom f.hom x = ConcreteCategory.hom g.hom x := by
  rw [h]

/-! ### Regular epimorphisms are stable under base change -/

/-- In a pullback square of `CGWH`, the base change of a regular epimorphism is a regular
epimorphism. -/
theorem isRegularEpi_of_isPullback {P A B S : CGWHCat.{u}} {fst : P ⟶ B} {snd : P ⟶ A}
    {g : B ⟶ S} {f : A ⟶ S} (sq : IsPullback fst snd g f) (hg : IsRegularEpi g) :
    IsRegularEpi snd := by
  have hq : IsQuotientMap (ConcreteCategory.hom g.hom) :=
    ((mono_epi_isRegularMono_isRegularEpi_iff g).2.2.2).1 hg
  let φ : B.obj → S.obj := ConcreteCategory.hom g.hom
  let ψ : A.obj → S.obj := ConcreteCategory.hom f.hom
  have hψ : Continuous ψ := (ConcreteCategory.hom f.hom).continuous
  let E : CGWHCat.{u} := obj (FibProd φ ψ)
  let e₁ : E ⟶ B := homOf ⟨fun p : FibProd φ ψ => p.1.1, continuous_fst_fibProd φ ψ⟩
  let e₂ : E ⟶ A := homOf ⟨fun p : FibProd φ ψ => p.1.2, continuous_snd_fibProd φ ψ⟩
  have hw : e₁ ≫ g = e₂ ≫ f := hom_ext_fun fun p => p.2
  let l : E ⟶ P := sq.lift e₁ e₂ hw
  have hl : l ≫ snd = e₂ := sq.lift_snd e₁ e₂ hw
  have hcomp : (ConcreteCategory.hom snd.hom) ∘ (ConcreteCategory.hom l.hom) =
      fun p : FibProd φ ψ => p.1.2 := by
    funext p
    exact congr_fun_hom hl p
  have hE : IsQuotientMap (fun p : FibProd φ ψ => p.1.2) :=
    isQuotientMap_snd_pullback (X := B.obj) (Y := S.obj) (T := A.obj) hq hψ
  rw [← hcomp] at hE
  have hsnd : IsQuotientMap (ConcreteCategory.hom snd.hom) :=
    IsQuotientMap.of_comp (ConcreteCategory.hom l.hom).continuous
      (ConcreteCategory.hom snd.hom).continuous hE
  exact ((mono_epi_isRegularMono_isRegularEpi_iff snd).2.2.2).2 hsnd

end Sol_CGWH_regular

open CGWH Sol_CGWH_regular in
theorem solution : Regular CGWHCat.{u} := by
  have hlim := (isRightAdjoint_forgetToCG_and_hasLimits_and_hasColimits.{u}).2.1
  have hcolim := (isRightAdjoint_forgetToCG_and_hasLimits_and_hasColimits.{u}).2.2
  have := hlim
  have := hcolim
  exact
    { toHasFiniteLimits := inferInstance
      hasCoequalizer_of_isKernelPair := fun _ => inferInstance
      regularEpiIsStableUnderBaseChange :=
        ⟨fun {_ _ _ _} {_ _ _ _} sq hg => isRegularEpi_of_isPullback sq hg⟩ }
