-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.DrinfeldDatum.isQuadrupleOf_of_forall_isBaseChangeAlong_away
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/c7a6cb8c-aa5a-548a-b8fc-11c499cdb561

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_isQuadrupleOf_of_forall_isBaseChangeAlong_away

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace B24X4e

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
variable {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B']

theorem tmul_mem_map_line_sup (f : B →ₐ[𝒪] B') (d : DeligneDatum (K := K) π B) (𝔮 : Ideal B') (M : FullLattice 𝒪 K)
    (v : ↥M.1) (h : (1 : B) ⊗ₜ[𝒪] v ∈ d.line M ⊔ (Ideal.comap f 𝔮 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M))) :
    (1 : B') ⊗ₜ[𝒪] v ∈ (d.map π f).line M ⊔ (𝔮 • ⊤ : Submodule B' (latticeBaseChange 𝒪 K B' M)) := by
  rw [← rTensor_one_tmul f M v]
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h
  rw [← hab, map_add]
  refine Submodule.mem_sup.mpr ⟨_, ?_, _, ?_, rfl⟩
  · show _ ∈ lineBaseChange f M (d.line M)
    exact Submodule.subset_span ⟨a, ha, rfl⟩
  · refine Submodule.smul_induction_on hb (fun r hr n _ => ?_) (fun x y hx hy => ?_)
    · rw [rTensor_smul_left f M r n]
      exact Submodule.smul_mem_smul hr Submodule.mem_top
    · rw [map_add]
      exact Submodule.add_mem _ hx hy

theorem edgeNondegAt_of_map (f : B →ₐ[𝒪] B') (d : DeligneDatum (K := K) π B) (𝔮 : Ideal B') (M' M : FullLattice 𝒪 K)
    (h : (d.map π f).EdgeNondegAt π 𝔮 M' M) : d.EdgeNondegAt π (Ideal.comap f 𝔮) M' M := by
  obtain ⟨hle, hπ, h1, h2⟩ := h
  exact ⟨hle, hπ, fun v hv hmem => h1 v hv (tmul_mem_map_line_sup f d 𝔮 M v hmem),
    fun v' hv' hmem => h2 v' hv' (tmul_mem_map_line_sup f d 𝔮 M' v' hmem)⟩

theorem exists_not_mem {k : ℕ} (f : Fin k → B) (hf : Ideal.span (Set.range f) = ⊤) (x : PrimeSpectrum B) :
    ∃ i : Fin k, f i ∉ x.asIdeal := by
  by_contra h
  push_neg at h
  apply x.isPrime.ne_top
  rw [eq_top_iff, ← hf]
  exact Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact h i)

theorem comap_toAlgHom (C : Type) [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C] (I : Ideal C) :
    Ideal.comap (IsScalarTower.toAlgHom 𝒪 B C) I = Ideal.comap (algebraMap B C) I :=
  Ideal.ext fun _ => Iff.rfl

theorem pointUnder_toAlgHom (C : Type) [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C]
    (y : PrimeSpectrum C) :
    DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B C) y = PrimeSpectrum.comap (algebraMap B C) y := rfl

end B24X4e

namespace B24X4e

theorem isLocalization_atPrime_locRing {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]
    {C : Type} [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C] (g : B) [IsLocalization.Away g C] (y : PrimeSpectrum C) :
    haveI : IsScalarTower B C (locRing C y) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    IsLocalization.AtPrime (locRing C y) (PrimeSpectrum.comap (algebraMap B C) y).asIdeal :=
  haveI : IsScalarTower B C (locRing C y) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  IsLocalization.isLocalization_isLocalization_atPrime_isLocalization (Submonoid.powers g) (locRing C y) y.asIdeal

def τB {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]
    {C : Type} [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C] (T : Type) [AddCommGroup T] [Module B T] [Module.Invertible B T]
    (T' : Type) [AddCommGroup T'] [Module C T'] [Module.Invertible C T']
    (τ : T →ₛₗ[((IsScalarTower.toAlgHom 𝒪 B C : B →ₐ[𝒪] C) : B →+* C)] T') :
    letI : Module B T' := Module.compHom T' (algebraMap B C); T →ₗ[B] T' :=
  letI : Module B T' := Module.compHom T' (algebraMap B C)
  { toFun := τ, map_add' := fun a b => map_add τ a b, map_smul' := fun b t => by
      rw [LinearMap.map_smulₛₗ]; rfl }

theorem τB_apply {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]
    {C : Type} [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C] (T : Type) [AddCommGroup T] [Module B T] [Module.Invertible B T]
    (T' : Type) [AddCommGroup T'] [Module C T'] [Module.Invertible C T']
    (τ : T →ₛₗ[((IsScalarTower.toAlgHom 𝒪 B C : B →ₐ[𝒪] C) : B →+* C)] T') (t : T) : τB T T' τ t = τ t := rfl

theorem isBaseChange_τB {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]
    {C : Type} [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C] (T : Type) [AddCommGroup T] [Module B T] [Module.Invertible B T]
    (T' : Type) [AddCommGroup T'] [Module C T'] [Module.Invertible C T']
    (τ : T →ₛₗ[((IsScalarTower.toAlgHom 𝒪 B C : B →ₐ[𝒪] C) : B →+* C)] T') (hτ : Submodule.span C (Set.range τ) = ⊤) :
    letI : Module B T' := Module.compHom T' (algebraMap B C)
    haveI : IsScalarTower B C T' := ⟨fun b c t => by
      show (b • c) • t = (algebraMap B C b) • (c • t); rw [Algebra.smul_def, mul_smul]⟩
    IsBaseChange C (τB T T' τ) := by
  letI : Module B T' := Module.compHom T' (algebraMap B C)
  haveI : IsScalarTower B C T' := ⟨fun b c t => by
    show (b • c) • t = (algebraMap B C b) • (c • t); rw [Algebra.smul_def, mul_smul]⟩
  have hsurj : Function.Surjective ((τB T T' τ).liftBaseChange C) := by
    rw [← LinearMap.range_eq_top, LinearMap.range_liftBaseChange, ← top_le_iff, ← hτ]
    apply Submodule.span_mono
    rintro _ ⟨t, rfl⟩
    exact ⟨t, rfl⟩
  have hbij := Module.Invertible.bijective_of_surjective hsurj
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective _ hbij) (fun t => by
    rw [LinearEquiv.ofBijective_apply, LinearMap.liftBaseChange_tmul, one_smul])

noncomputable def γ {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]
    {C : Type} [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C] (T : Type) [AddCommGroup T] [Module B T] [Module.Invertible B T]
    (T' : Type) [AddCommGroup T'] [Module C T'] [Module.Invertible C T']
    (τ : T →ₛₗ[((IsScalarTower.toAlgHom 𝒪 B C : B →ₐ[𝒪] C) : B →+* C)] T') (y : PrimeSpectrum C) :
    letI : Module B T' := Module.compHom T' (algebraMap B C)
    haveI : IsScalarTower B C T' := ⟨fun b c t => by
      show (b • c) • t = (algebraMap B C b) • (c • t); rw [Algebra.smul_def, mul_smul]⟩
    T →ₗ[B] stalk C y T' :=
  letI : Module B T' := Module.compHom T' (algebraMap B C)
  haveI : IsScalarTower B C T' := ⟨fun b c t => by
    show (b • c) • t = (algebraMap B C b) • (c • t); rw [Algebra.smul_def, mul_smul]⟩
  ((LocalizedModule.mkLinearMap y.asIdeal.primeCompl T').restrictScalars B).comp (τB T T' τ)

theorem γ_apply {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]
    {C : Type} [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C] (T : Type) [AddCommGroup T] [Module B T] [Module.Invertible B T]
    (T' : Type) [AddCommGroup T'] [Module C T'] [Module.Invertible C T']
    (τ : T →ₛₗ[((IsScalarTower.toAlgHom 𝒪 B C : B →ₐ[𝒪] C) : B →+* C)] T') (y : PrimeSpectrum C) (t : T) :
    letI : Module B T' := Module.compHom T' (algebraMap B C)
    haveI : IsScalarTower B C T' := ⟨fun b c t => by
      show (b • c) • t = (algebraMap B C b) • (c • t); rw [Algebra.smul_def, mul_smul]⟩
    γ T T' τ y t = LocalizedModule.mk (τ t) 1 := rfl

theorem isLocalizedModule_γ {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]
    {C : Type} [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C] (g : B) [IsLocalization.Away g C] (T : Type) [AddCommGroup T] [Module B T] [Module.Invertible B T]
    (T' : Type) [AddCommGroup T'] [Module C T'] [Module.Invertible C T']
    (τ : T →ₛₗ[((IsScalarTower.toAlgHom 𝒪 B C : B →ₐ[𝒪] C) : B →+* C)] T')
    (hτ : Submodule.span C (Set.range τ) = ⊤) (y : PrimeSpectrum C) :
    letI : Module B T' := Module.compHom T' (algebraMap B C)
    haveI : IsScalarTower B C T' := ⟨fun b c t => by
      show (b • c) • t = (algebraMap B C b) • (c • t); rw [Algebra.smul_def, mul_smul]⟩
    IsLocalizedModule (PrimeSpectrum.comap (algebraMap B C) y).asIdeal.primeCompl (γ T T' τ y) := by
  letI : Module B T' := Module.compHom T' (algebraMap B C)
  haveI : IsScalarTower B C T' := ⟨fun b c t => by
    show (b • c) • t = (algebraMap B C b) • (c • t); rw [Algebra.smul_def, mul_smul]⟩
  haveI : IsScalarTower B C (locRing C y) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower B C (stalk C y T') := inferInstance
  haveI : IsScalarTower B (locRing C y) (stalk C y T') := inferInstance
  haveI : IsLocalization.AtPrime (locRing C y) (PrimeSpectrum.comap (algebraMap B C) y).asIdeal :=
    isLocalization_atPrime_locRing (𝒪 := 𝒪) g y
  rw [isLocalizedModule_iff_isBaseChange (PrimeSpectrum.comap (algebraMap B C) y).asIdeal.primeCompl (locRing C y)]
  exact IsBaseChange.comp (isBaseChange_τB T T' τ hτ)
    (IsLocalizedModule.isBaseChange y.asIdeal.primeCompl (locRing C y) (LocalizedModule.mkLinearMap y.asIdeal.primeCompl T'))

end B24X4e

namespace B24X4e

theorem iso_γ_mk {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]
    {C : Type} [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C] (g : B) [IsLocalization.Away g C] (T : Type) [AddCommGroup T] [Module B T] [Module.Invertible B T]
    (T' : Type) [AddCommGroup T'] [Module C T'] [Module.Invertible C T']
    (τ : T →ₛₗ[((IsScalarTower.toAlgHom 𝒪 B C : B →ₐ[𝒪] C) : B →+* C)] T')
    (hτ : Submodule.span C (Set.range τ) = ⊤) (y : PrimeSpectrum C) (t : T) (s : B)
    (hs : s ∈ (PrimeSpectrum.comap (algebraMap B C) y).asIdeal.primeCompl) :
    letI : Module B T' := Module.compHom T' (algebraMap B C)
    haveI : IsScalarTower B C T' := ⟨fun b c t => by
      show (b • c) • t = (algebraMap B C b) • (c • t); rw [Algebra.smul_def, mul_smul]⟩
    haveI := isLocalizedModule_γ g T T' τ hτ y
    IsLocalizedModule.iso (PrimeSpectrum.comap (algebraMap B C) y).asIdeal.primeCompl (γ T T' τ y)
        (LocalizedModule.mk t ⟨s, hs⟩) =
      LocalizedModule.mk (τ t) (⟨algebraMap B C s, hs⟩ : y.asIdeal.primeCompl) := by
  letI : Module B T' := Module.compHom T' (algebraMap B C)
  haveI : IsScalarTower B C T' := ⟨fun b c t => by
    show (b • c) • t = (algebraMap B C b) • (c • t); rw [Algebra.smul_def, mul_smul]⟩
  haveI := isLocalizedModule_γ g T T' τ hτ y
  apply ((Module.End.isUnit_iff _).mp
    (IsLocalizedModule.map_units (γ T T' τ y) ⟨s, hs⟩)).1
  rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply, ← map_smul, LocalizedModule.smul'_mk,
    ← algebraMap_smul C s (LocalizedModule.mk (τ t) (⟨algebraMap B C s, hs⟩ : y.asIdeal.primeCompl)),
    LocalizedModule.smul'_mk]
  have h1 : LocalizedModule.mk (s • t) (⟨s, hs⟩ : (PrimeSpectrum.comap (algebraMap B C) y).asIdeal.primeCompl) =
      LocalizedModule.mk t 1 := LocalizedModule.mk_cancel ⟨s, hs⟩ t
  have h2 : LocalizedModule.mk (algebraMap B C s • τ t) (⟨algebraMap B C s, hs⟩ : y.asIdeal.primeCompl) =
      LocalizedModule.mk (τ t) 1 := LocalizedModule.mk_cancel (⟨algebraMap B C s, hs⟩ : y.asIdeal.primeCompl) (τ t)
  rw [h1, h2, IsLocalizedModule.iso_mk_one, γ_apply]

end B24X4e

namespace B24X4e

section Loc

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    {B : Type} [CommRing B] [Algebra 𝒪 B]
variable {A : Type} [CommRing A] [Algebra 𝒪 A] [Algebra B A] [IsScalarTower 𝒪 B A]

noncomputable def ιB (A : Type) [CommRing A] [Algebra 𝒪 A] [Algebra B A] [IsScalarTower 𝒪 B A] (N : FullLattice 𝒪 K) :
    latticeBaseChange 𝒪 K B N →ₗ[B] latticeBaseChange 𝒪 K A N :=
  { toFun := LinearMap.rTensor (↥N.1) (IsScalarTower.toAlgHom 𝒪 B A).toLinearMap
    map_add' := fun a b => map_add _ a b
    map_smul' := fun b p => by
      rw [rTensor_smul_left (IsScalarTower.toAlgHom 𝒪 B A) N b p, IsScalarTower.toAlgHom_apply, algebraMap_smul]
      rfl }

theorem ιB_apply (N : FullLattice 𝒪 K) (p : latticeBaseChange 𝒪 K B N) :
    ιB A N p = LinearMap.rTensor (↥N.1) (IsScalarTower.toAlgHom 𝒪 B A).toLinearMap p := rfl

theorem ιB_one_tmul (N : FullLattice 𝒪 K) (v : ↥N.1) : ιB A N ((1 : B) ⊗ₜ[𝒪] v) = (1 : A) ⊗ₜ[𝒪] v :=
  rTensor_one_tmul _ N v

theorem isLocalizedModule_ιB (S : Submonoid B) [IsLocalization S A] (N : FullLattice 𝒪 K) :
    IsLocalizedModule S (ιB (𝒪 := 𝒪) A N) :=
  (isLocalizedModule_iff_isBaseChange S A _).mpr
    (IsBaseChange.of_equiv (TensorProduct.AlgebraTensorModule.cancelBaseChange 𝒪 B A A (↥N.1))
      (fun p => cancelBaseChange_one_tmul (IsScalarTower.toAlgHom 𝒪 B A) (fun _ => rfl) N p))

theorem ιB_mem_lineBaseChange_iff (S : Submonoid B) [IsLocalization S A] (N : FullLattice 𝒪 K)
    (D : Submodule B (latticeBaseChange 𝒪 K B N)) (p : latticeBaseChange 𝒪 K B N) :
    ιB A N p ∈ lineBaseChange (IsScalarTower.toAlgHom 𝒪 B A) N D ↔ ∃ s ∈ S, s • p ∈ D := by
  haveI := isLocalizedModule_ιB (𝒪 := 𝒪) (A := A) S N
  have hspan : lineBaseChange (IsScalarTower.toAlgHom 𝒪 B A) N D = D.localized' A S (ιB A N) := by
    rw [Submodule.localized'_eq_span]; rfl
  rw [hspan, Submodule.mem_localized']
  constructor
  · rintro ⟨m, hm, s, hms⟩
    rw [IsLocalizedModule.mk'_eq_iff, Submonoid.smul_def, ← map_smul] at hms
    obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_iff_exists S (ιB A N)).mp hms
    refine ⟨c * s, mul_mem c.2 s.2, ?_⟩
    rw [mul_smul]
    have hc' : (c : B) • ((s : B) • p) = (c : B) • m := by
      rw [← Submonoid.smul_def, ← Submonoid.smul_def c m, hc]
    rw [hc']
    exact D.smul_mem _ hm
  · rintro ⟨s, hs, hsp⟩
    exact ⟨s • p, hsp, ⟨s, hs⟩, by rw [IsLocalizedModule.mk'_eq_iff, Submonoid.smul_def, map_smul]⟩

end Loc

end B24X4e

namespace B24X4e

theorem ker_eq_line {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    {C : Type} [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C] (g : B) [IsLocalization.Away g C] (T : Type) [AddCommGroup T] [Module B T] [Module.Invertible B T]
    (T' : Type) [AddCommGroup T'] [Module C T'] [Module.Invertible C T']
    (τ : T →ₛₗ[((IsScalarTower.toAlgHom 𝒪 B C : B →ₐ[𝒪] C) : B →+* C)] T')
    (hτ : Submodule.span C (Set.range τ) = ⊤) (y : PrimeSpectrum C)
    (d : DeligneDatum (K := K) π B) (N N' : FullLattice 𝒪 K) (hN : N = N')
    (u : latticeBaseChange 𝒪 K (locRing B (PrimeSpectrum.comap (algebraMap B C) y)) N →ₗ[locRing B (PrimeSpectrum.comap (algebraMap B C) y)] stalk B (PrimeSpectrum.comap (algebraMap B C) y) T)
    (u' : latticeBaseChange 𝒪 K (locRing C y) N' →ₗ[locRing C y] stalk C y T')
    (hu : ∀ (v : Fin 2 → K) (hv : v ∈ N.1) (hv' : v ∈ N'.1) (t : T) (s : B) (hs : algebraMap B C s ∉ y.asIdeal),
      u ((1 : locRing B (PrimeSpectrum.comap (algebraMap B C) y)) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥N.1)) = LocalizedModule.mk t ⟨s, hs⟩ →
      u' ((1 : locRing C y) ⊗ₜ[𝒪] (⟨v, hv'⟩ : ↥N'.1)) = LocalizedModule.mk (τ t) ⟨algebraMap B C s, hs⟩)
    (hker' : LinearMap.ker u' =
      ((d.map π (IsScalarTower.toAlgHom 𝒪 B C)).map π (toLocRing C y)).line N') :
    LinearMap.ker u = (d.map π (toLocRing B (PrimeSpectrum.comap (algebraMap B C) y))).line N := by
  subst hN
  letI : Module B T' := Module.compHom T' (algebraMap B C)
  haveI : IsScalarTower B C T' := ⟨fun b c t => by
    show (b • c) • t = (algebraMap B C b) • (c • t); rw [Algebra.smul_def, mul_smul]⟩
  haveI : IsScalarTower B C (locRing C y) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower 𝒪 B (locRing C y) := IsScalarTower.of_algebraMap_eq (fun r => by
    rw [IsScalarTower.algebraMap_apply 𝒪 C (locRing C y), IsScalarTower.algebraMap_apply 𝒪 B C]; rfl)
  haveI : IsLocalization.AtPrime (locRing C y) (PrimeSpectrum.comap (algebraMap B C) y).asIdeal := isLocalization_atPrime_locRing (𝒪 := 𝒪) g y
  haveI hγ := isLocalizedModule_γ g T T' τ hτ y
  have hψ : (toLocRing C y).comp (IsScalarTower.toAlgHom 𝒪 B C) = IsScalarTower.toAlgHom 𝒪 B (locRing C y) :=
    AlgHom.ext fun _ => rfl
  have hker'' : LinearMap.ker u' = lineBaseChange (IsScalarTower.toAlgHom 𝒪 B (locRing C y)) N (d.line N) := by
    rw [hker', ← hψ]
    exact congrArg (fun e : DeligneDatum (K := K) π (locRing C y) => e.line N)
      (((Omega K π).map_comp (IsScalarTower.toAlgHom 𝒪 B C) (toLocRing C y) d).symm)

  have hsq : ∀ p₀ : latticeBaseChange 𝒪 K B N,
      u' (ιB (locRing C y) N p₀) =
        IsLocalizedModule.iso (PrimeSpectrum.comap (algebraMap B C) y).asIdeal.primeCompl (γ T T' τ y) (u (ιB (locRing B (PrimeSpectrum.comap (algebraMap B C) y)) N p₀)) := by
    intro p₀
    induction p₀ using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul b v =>
      have e1 : (b ⊗ₜ[𝒪] v : latticeBaseChange 𝒪 K B N) = b • ((1 : B) ⊗ₜ[𝒪] v) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      have l1 : ιB (locRing C y) N (b ⊗ₜ[𝒪] v) = b • ((1 : locRing C y) ⊗ₜ[𝒪] v) := by
        rw [e1, map_smul, ιB_one_tmul]
      have l2 : ιB (locRing B (PrimeSpectrum.comap (algebraMap B C) y)) N (b ⊗ₜ[𝒪] v) = b • ((1 : locRing B (PrimeSpectrum.comap (algebraMap B C) y)) ⊗ₜ[𝒪] v) := by
        rw [e1, map_smul, ιB_one_tmul]
      rw [l1, l2, LinearMap.map_smul_of_tower u', LinearMap.map_smul_of_tower u, map_smul]
      congr 1
      generalize hm : u ((1 : locRing B (PrimeSpectrum.comap (algebraMap B C) y)) ⊗ₜ[𝒪] v) = m
      induction m using LocalizedModule.induction_on with
      | h t s => rw [hu v.1 v.2 v.2 t s s.2 hm, iso_γ_mk g T T' τ hτ y t s s.2]

  have hpt : ∀ p₀ : latticeBaseChange 𝒪 K B N,
      u (ιB (locRing B (PrimeSpectrum.comap (algebraMap B C) y)) N p₀) = 0 ↔ ιB (locRing B (PrimeSpectrum.comap (algebraMap B C) y)) N p₀ ∈ (d.map π (toLocRing B (PrimeSpectrum.comap (algebraMap B C) y))).line N := by
    intro p₀
    rw [← (IsLocalizedModule.iso (PrimeSpectrum.comap (algebraMap B C) y).asIdeal.primeCompl (γ T T' τ y)).map_eq_zero_iff, ← hsq,
      ← LinearMap.mem_ker, hker'', ιB_mem_lineBaseChange_iff (PrimeSpectrum.comap (algebraMap B C) y).asIdeal.primeCompl N (d.line N) p₀]
    exact (ιB_mem_lineBaseChange_iff (A := locRing B (PrimeSpectrum.comap (algebraMap B C) y)) (PrimeSpectrum.comap (algebraMap B C) y).asIdeal.primeCompl N (d.line N) p₀).symm

  haveI := isLocalizedModule_ιB (𝒪 := 𝒪) (A := locRing B (PrimeSpectrum.comap (algebraMap B C) y)) (PrimeSpectrum.comap (algebraMap B C) y).asIdeal.primeCompl N
  ext p
  obtain ⟨⟨p₀, s⟩, hsp⟩ := IsLocalizedModule.surj (PrimeSpectrum.comap (algebraMap B C) y).asIdeal.primeCompl (ιB (locRing B (PrimeSpectrum.comap (algebraMap B C) y)) N) p
  have hunit : IsUnit (algebraMap B (locRing B (PrimeSpectrum.comap (algebraMap B C) y)) s) := IsLocalization.map_units (locRing B (PrimeSpectrum.comap (algebraMap B C) y)) s
  have hsp' : algebraMap B (locRing B (PrimeSpectrum.comap (algebraMap B C) y)) s • p = ιB (locRing B (PrimeSpectrum.comap (algebraMap B C) y)) N p₀ := by
    rw [algebraMap_smul, ← Submonoid.smul_def]; exact hsp
  have hinv : ((hunit.unit⁻¹ : (locRing B (PrimeSpectrum.comap (algebraMap B C) y))ˣ) : locRing B (PrimeSpectrum.comap (algebraMap B C) y)) •
      (algebraMap B (locRing B (PrimeSpectrum.comap (algebraMap B C) y)) s • p) = p := by
    rw [smul_smul, Units.inv_mul_eq_one.mpr hunit.unit_spec, one_smul]
  rw [LinearMap.mem_ker]
  constructor
  · intro hp
    have h0 : u (ιB (locRing B (PrimeSpectrum.comap (algebraMap B C) y)) N p₀) = 0 := by rw [← hsp', map_smul, hp, smul_zero]
    have hmem := (hpt p₀).mp h0
    rw [← hsp'] at hmem
    rw [← hinv]
    exact Submodule.smul_mem _ _ hmem
  · intro hp
    have hmem : ιB (locRing B (PrimeSpectrum.comap (algebraMap B C) y)) N p₀ ∈ (d.map π (toLocRing B (PrimeSpectrum.comap (algebraMap B C) y))).line N := by
      rw [← hsp']; exact Submodule.smul_mem _ _ hp
    have h0 := (hpt p₀).mpr hmem
    rw [← hsp', map_smul] at h0
    have h1 : u p = ((hunit.unit⁻¹ : (locRing B (PrimeSpectrum.comap (algebraMap B C) y))ˣ) :
        locRing B (PrimeSpectrum.comap (algebraMap B C) y)) • (algebraMap B (locRing B (PrimeSpectrum.comap (algebraMap B C) y)) s • u p) := by
      rw [smul_smul, Units.inv_mul_eq_one.mpr hunit.unit_spec, one_smul]
    rw [h1, h0, smul_zero]

end B24X4e

open B24X4e in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B] {k : ℕ} (f : Fin k → B) (hf : Ideal.span (Set.range f) = ⊤)
    (Q : DrinfeldDatum (K := K) π B) (d : DeligneDatum (K := K) π B)
    (Qf : ∀ i : Fin k, DrinfeldDatum (K := K) π (Localization.Away (f i)))
    (hbc : ∀ i : Fin k, Q.IsBaseChangeAlong (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) (Qf i))
    (hQf : ∀ i : Fin k, (Qf i).IsQuadrupleOf (d.map π (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))))) :
    Q.IsQuadrupleOf d := by
  classical
  intro x
  obtain ⟨i, hi⟩ := exists_not_mem f hf x
  have hx : x ∈ Set.range (PrimeSpectrum.comap (algebraMap B (Localization.Away (f i)))) := by
    rw [PrimeSpectrum.localization_away_comap_range _ (f i)]; exact hi
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨W⟩ := hbc i
  obtain ⟨hedge, hker₀, hker₁⟩ := hQf i y
  have hL₀ : (Qf i).L₀ y = Q.L₀ (PrimeSpectrum.comap (algebraMap B (Localization.Away (f i))) y) :=
    Subtype.ext (W.N₀_eq y)
  have hL₁ : (Qf i).L₁ y = Q.L₁ (PrimeSpectrum.comap (algebraMap B (Localization.Away (f i))) y) :=
    Subtype.ext (W.N₁_eq y)
  refine ⟨?_, ?_, ?_⟩
  · rw [hL₀, hL₁] at hedge
    have h := edgeNondegAt_of_map (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) d y.asIdeal _ _ hedge
    rwa [comap_toAlgHom] at h
  · exact ker_eq_line (f i) Q.T₀ (Qf i).T₀ W.τ₀ W.span_range_τ₀ y d _ _ hL₀.symm (Q.u₀ _) ((Qf i).u₀ y)
      (W.u₀_eq y) hker₀
  · exact ker_eq_line (f i) Q.T₁ (Qf i).T₁ W.τ₁ W.span_range_τ₁ y d _ _ hL₁.symm (Q.u₁ _) ((Qf i).u₁ y)
      (W.u₁_eq y) hker₁

end S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_isQuadrupleOf_of_forall_isBaseChangeAlong_away
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_isQuadrupleOf_of_forall_isBaseChangeAlong_away (solution)
