-- Prove2me | solution 1 for CGWH.isQuotientMap_effectiveEpi_universallyEffectiveEpi_tfae
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T15:46:44.222113+00:00
-- url     : https://prove2.me/submissions/ee1db820-b6d8-4982-93e5-19c608991325

import Definitions.Def_CGWH_WeakHausdorff
import Theorems.Thm_CGWH_isQuotientMap_snd_pullback
import Theorems.Thm_CGWH_mono_epi_isRegularMono_isRegularEpi_iff
import Theorems.Thm_CGWH_isRightAdjoint_forgetToCG_and_hasLimits_and_hasColimits
import Theorems.Thm_CGWH_weaklyHausdorffSpace_pi_and_prod

open CategoryTheory Topology TopologicalSpace

set_option autoImplicit false

universe u

namespace Sol_CGWH_isQuotientMap_effectiveEpi_universallyEffectiveEpi_tfae

open CGWH

/-! ### The `k`-ification -/

/-- The `k`-ification of a topology is finer than the topology. -/
theorem compactlyGenerated_le (W : Type u) [t : TopologicalSpace W] :
    compactlyGenerated.{u} W ≤ t := by
  simp only [compactlyGenerated, ← continuous_iff_coinduced_le, continuous_sigma_iff,
    Sigma.forall]
  exact fun S f ↦ f.2

/-- A continuous map from a compact Hausdorff space to `W` is continuous for the `k`-ified
topology of `W`. -/
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

/-- A continuous map is continuous for the `k`-ified topology of its domain. -/
theorem continuous_of_kTop {W Z : Type u} [TopologicalSpace W] [TopologicalSpace Z] {φ : W → Z}
    (h : Continuous φ) : Continuous[compactlyGenerated.{u} W, inferInstance] φ :=
  continuous_le_dom (compactlyGenerated_le W) h

/-- The `k`-ification of a weakly Hausdorff space is weakly Hausdorff. -/
theorem weaklyHausdorffSpace_kTop (W : Type u) [t : TopologicalSpace W]
    [WeaklyHausdorffSpace W] : @WeaklyHausdorffSpace W (compactlyGenerated.{u} W) := by
  refine @WeaklyHausdorffSpace.mk W (compactlyGenerated.{u} W) fun K _ _ _ c hc => ?_
  have hc' : Continuous c := continuous_le_rng (compactlyGenerated_le W) hc
  exact (WeaklyHausdorffSpace.isClosed_range K c hc').mono (compactlyGenerated_le W)

/-- A subspace of a weakly Hausdorff space is weakly Hausdorff. -/
theorem weaklyHausdorffSpace_subtype {X : Type u} [TopologicalSpace X] [WeaklyHausdorffSpace X]
    (s : Set X) : WeaklyHausdorffSpace s := by
  refine ⟨fun K _ _ _ f hf => ?_⟩
  have h : IsClosed (Set.range fun k => (f k : X)) :=
    WeaklyHausdorffSpace.isClosed_range K (fun k => (f k : X)) (continuous_subtype_val.comp hf)
  have hrange : Set.range f = Subtype.val ⁻¹' Set.range (fun k => (f k : X)) := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, rfl⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext hk⟩
  rw [hrange]
  exact h.preimage continuous_subtype_val

/-! ### Objects and morphisms of `CGWH` -/

instance instWeaklyHausdorffSpaceObj (X : CGWHCat.{u}) : WeaklyHausdorffSpace X.obj := X.property

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

/-- The subspace `{(x, t) | f x = g t}` of `X × T`, as a set. -/
abbrev FibreSet {X Y T : CGWHCat.{u}} (f : X ⟶ Y) (g : T ⟶ Y) : Type u :=
  {p : X.obj × T.obj // ConcreteCategory.hom f.hom p.1 = ConcreteCategory.hom g.hom p.2}

instance instWeaklyHausdorffSpaceFibreSet {X Y T : CGWHCat.{u}} (f : X ⟶ Y) (g : T ⟶ Y) :
    WeaklyHausdorffSpace (FibreSet f g) := by
  have : WeaklyHausdorffSpace (X.obj × T.obj) := weaklyHausdorffSpace_pi_and_prod.2 _ _
  exact weaklyHausdorffSpace_subtype _

/-- The `k`-ified fibre product `k({(x, t) | f x = g t})` as an object of `CGWH`. -/
noncomputable def fibreObj {X Y T : CGWHCat.{u}} (f : X ⟶ Y) (g : T ⟶ Y) : CGWHCat.{u} :=
  ⟨@CompactlyGenerated.mk (@TopCat.of (FibreSet f g) (compactlyGenerated.{u} (FibreSet f g)))
    (compactlyGeneratedSpace_kTop (FibreSet f g)), weaklyHausdorffSpace_kTop (FibreSet f g)⟩

/-- The first projection of the `k`-ified fibre product. -/
noncomputable def fibreFst {X Y T : CGWHCat.{u}} (f : X ⟶ Y) (g : T ⟶ Y) : fibreObj f g ⟶ X :=
  homOf ⟨fun p : (fibreObj f g).obj => (p : FibreSet f g).1.1,
    by exact continuous_of_kTop (W := FibreSet f g) (continuous_fst.comp continuous_subtype_val)⟩

/-- The second projection of the `k`-ified fibre product. -/
noncomputable def fibreSnd {X Y T : CGWHCat.{u}} (f : X ⟶ Y) (g : T ⟶ Y) : fibreObj f g ⟶ T :=
  homOf ⟨fun p : (fibreObj f g).obj => (p : FibreSet f g).1.2,
    by exact continuous_of_kTop (W := FibreSet f g) (continuous_snd.comp continuous_subtype_val)⟩

theorem fibre_condition {X Y T : CGWHCat.{u}} (f : X ⟶ Y) (g : T ⟶ Y) :
    fibreFst f g ≫ f = fibreSnd f g ≫ g :=
  hom_ext_fun fun p => by exact p.2

/-- In `CGWH`, the base change of a quotient map along any morphism is a quotient map. -/
theorem isQuotientMap_snd_of_isPullback {X Y P T : CGWHCat.{u}} (f : X ⟶ Y)
    (hf : IsQuotientMap (ConcreteCategory.hom f.hom)) (fst : P ⟶ X) (snd : P ⟶ T) (g : T ⟶ Y)
    (sq : IsPullback fst snd f g) : IsQuotientMap (ConcreteCategory.hom snd.hom) := by
  let ψ : fibreObj f g ⟶ P := sq.lift (fibreFst f g) (fibreSnd f g) (fibre_condition f g)
  have hψ : ψ ≫ snd = fibreSnd f g := sq.lift_snd _ _ _
  have hq : IsQuotientMap (ConcreteCategory.hom (fibreSnd f g).hom) :=
    by exact isQuotientMap_snd_pullback hf (ConcreteCategory.hom g.hom).continuous
  have hcomp : (ConcreteCategory.hom snd.hom) ∘ (ConcreteCategory.hom ψ.hom) =
      ConcreteCategory.hom (fibreSnd f g).hom := by
    funext p
    exact congr_fun_hom hψ p
  rw [← hcomp] at hq
  exact IsQuotientMap.of_comp (ConcreteCategory.hom ψ.hom).continuous
    (ConcreteCategory.hom snd.hom).continuous hq

end Sol_CGWH_isQuotientMap_effectiveEpi_universallyEffectiveEpi_tfae

open Sol_CGWH_isQuotientMap_effectiveEpi_universallyEffectiveEpi_tfae CGWH

theorem solution {X Y : CGWHCat.{u}} (f : X ⟶ Y) :
    [IsQuotientMap (ConcreteCategory.hom f.hom),
      EffectiveEpi f,
      ∀ ⦃P T : CGWHCat.{u}⦄ (fst : P ⟶ X) (snd : P ⟶ T) (g : T ⟶ Y),
        IsPullback fst snd f g → EffectiveEpi snd].TFAE := by
  have : Limits.HasLimits CGWHCat.{u} :=
    isRightAdjoint_forgetToCG_and_hasLimits_and_hasColimits.{u}.2.1
  tfae_have 1 → 3 := by
    intro hf P T fst snd g sq
    have : IsRegularEpi snd :=
      ((mono_epi_isRegularMono_isRegularEpi_iff snd).2.2.2).mpr
        (isQuotientMap_snd_of_isPullback f hf fst snd g sq)
    infer_instance
  tfae_have 3 → 2 := fun h3 => h3 (𝟙 X) f (𝟙 Y) (IsPullback.id_horiz f)
  tfae_have 2 → 1 := by
    intro h2
    have : IsRegularEpi f := inferInstance
    exact ((mono_epi_isRegularMono_isRegularEpi_iff f).2.2.2).mp inferInstance
  tfae_finish
