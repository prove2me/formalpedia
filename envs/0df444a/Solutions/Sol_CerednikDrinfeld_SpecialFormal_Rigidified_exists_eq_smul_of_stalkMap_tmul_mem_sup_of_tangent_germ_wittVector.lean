-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.exists_eq_smul_of_stalkMap_tmul_mem_sup_of_tangent_germ_wittVector
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/93682657-1a91-5656-9c1c-44c9f69a03e8

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_mem_iff_exists_isEtaSection_zero_map_of_isAlgClosed_of_ker_eq
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_mem_iff_exists_isEtaSection_one_map_of_isAlgClosed_of_ker_eq
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsAdmissible_map_ringHom
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isEtaSection_map_and_eq_nMap_and_tangent_eq_of_isEtaSection_of_isUnit
import Theorems.Thm_CerednikDrinfeld_FormalODModule_lieZero_lieOne_map_eq_span_image
import Theorems.Thm_CerednikDrinfeld_FormalODModule_tangent_mem_lieZero_and_lieOne_of_mem_gradedPiece_of_isNilpotent
import Theorems.Thm_MvFormalGroup_CartierModule_tangent_surjective_of_algebra_padicInt
import Theorems.Thm_MvFormalGroup_CartierModule_tangent_eq_zero_iff_exists_verschiebungInt_eq
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_nVarpi_eq_of_mem_etaPiece_of_toLieQuot_eq_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_eq_smul_of_stalkMap_tmul_mem_sup_of_tangent_germ_wittVector
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply"

set_option autoImplicit false

namespace StalkOnto

section Good

variable {B : Type} [CommRing B] (x : PrimeSpectrum B) (P : Submodule B (Fin 2 → B))

def good (G : Submodule (Localization.AtPrime x.asIdeal) (LocalizedModule x.asIdeal.primeCompl ↥P)) :
    Submodule (Localization.AtPrime x.asIdeal) (Fin 2 → Localization.AtPrime x.asIdeal) where
  carrier := {w | ∃ (s : ↥P) (b : x.asIdeal.primeCompl), LocalizedModule.mk s b ∈ G ∧
    ∀ i, algebraMap B (Localization.AtPrime x.asIdeal) ((s : Fin 2 → B) i) =
      algebraMap B (Localization.AtPrime x.asIdeal) (b : B) * w i}
  zero_mem' := ⟨0, 1, by rw [LocalizedModule.zero_mk]; exact G.zero_mem, fun i => by simp⟩
  add_mem' := by
    rintro w₁ w₂ ⟨s₁, b₁, h₁, e₁⟩ ⟨s₂, b₂, h₂, e₂⟩
    refine ⟨b₂ • s₁ + b₁ • s₂, b₁ * b₂, ?_, fun i => ?_⟩
    · rw [← LocalizedModule.mk_add_mk]; exact G.add_mem h₁ h₂
    · have hs : ((b₂ • s₁ + b₁ • s₂ : ↥P) : Fin 2 → B) i = (b₂ : B) * (s₁ : Fin 2 → B) i + (b₁ : B) * (s₂ : Fin 2 → B) i := rfl
      rw [hs, map_add, map_mul, map_mul, e₁, e₂, Submonoid.coe_mul, map_mul, Pi.add_apply]
      ring
  smul_mem' := by
    rintro c w ⟨s, b, h, e⟩
    induction c using Localization.induction_on with
    | H y =>
      obtain ⟨a, d⟩ := y
      refine ⟨a • s, d * b, ?_, fun i => ?_⟩
      · rw [← LocalizedModule.mk_smul_mk]; exact G.smul_mem _ h
      · have hs : ((a • s : ↥P) : Fin 2 → B) i = a * (s : Fin 2 → B) i := rfl
        have hd : algebraMap B (Localization.AtPrime x.asIdeal) (d : B) * Localization.mk a d =
            algebraMap B (Localization.AtPrime x.asIdeal) a := by
          rw [Localization.mk_eq_mk']; exact IsLocalization.mk'_spec' _ a d
        rw [hs, map_mul, e, Submonoid.coe_mul, map_mul, Pi.smul_apply, smul_eq_mul, ← hd]
        ring

theorem good_of_mem (G : Submodule (Localization.AtPrime x.asIdeal) (LocalizedModule x.asIdeal.primeCompl ↥P))
    (w : Fin 2 → Localization.AtPrime x.asIdeal) (s : ↥P) (b : x.asIdeal.primeCompl)
    (h : LocalizedModule.mk s b ∈ G)
    (e : ∀ i, algebraMap B (Localization.AtPrime x.asIdeal) ((s : Fin 2 → B) i) =
      algebraMap B (Localization.AtPrime x.asIdeal) (b : B) * w i) :
    w ∈ good x P G := ⟨s, b, h, e⟩

theorem mk_mem_of_good (G : Submodule (Localization.AtPrime x.asIdeal) (LocalizedModule x.asIdeal.primeCompl ↥P))
    (s : ↥P) (w : Fin 2 → Localization.AtPrime x.asIdeal) (hw : w ∈ good x P G)
    (e : ∀ i, algebraMap B (Localization.AtPrime x.asIdeal) ((s : Fin 2 → B) i) = w i) :
    LocalizedModule.mk s (1 : x.asIdeal.primeCompl) ∈ G := by
  obtain ⟨s', b', h', e'⟩ := hw
  have key : ∀ i, ∃ c : x.asIdeal.primeCompl, (c : B) * (s' : Fin 2 → B) i = (c : B) * ((b' : B) * (s : Fin 2 → B) i) := by
    intro i
    apply (IsLocalization.eq_iff_exists x.asIdeal.primeCompl (Localization.AtPrime x.asIdeal)).mp
    rw [e', map_mul, e]
  obtain ⟨c₀, hc₀⟩ := key 0
  obtain ⟨c₁, hc₁⟩ := key 1
  have : LocalizedModule.mk s (1 : x.asIdeal.primeCompl) = LocalizedModule.mk s' b' := by
    rw [LocalizedModule.mk_eq]
    refine ⟨c₀ * c₁, ?_⟩
    apply Subtype.ext
    funext i
    change ((c₀ : B) * c₁) * ((b' : B) * (s : Fin 2 → B) i) = ((c₀ : B) * c₁) * ((1 : B) * (s' : Fin 2 → B) i)
    fin_cases i
    · simp only [Fin.zero_eta, one_mul]; linear_combination (-(c₁ : B)) * hc₀
    · simp only [Fin.mk_one, one_mul]; linear_combination (-(c₀ : B)) * hc₁
  rw [this]; exact h'

theorem surjective_of_forall_mk_one_mem {V : Type} [AddCommGroup V] [Module (Localization.AtPrime x.asIdeal) V]
    (u : V →ₗ[Localization.AtPrime x.asIdeal] LocalizedModule x.asIdeal.primeCompl ↥P)
    (h : ∀ s : ↥P, LocalizedModule.mk s (1 : x.asIdeal.primeCompl) ∈ LinearMap.range u) :
    Function.Surjective u := by
  intro g
  induction g using LocalizedModule.induction_on with
  | h s b =>
    have : LocalizedModule.mk s b =
        Localization.mk (1 : B) b • LocalizedModule.mk s (1 : x.asIdeal.primeCompl) := by
      rw [LocalizedModule.mk_smul_mk, one_smul, mul_one]
    rw [this]
    exact LinearMap.mem_range.mp ((LinearMap.range u).smul_mem _ (h s))

end Good

theorem map_mem_span_image {A R : Type} [CommRing A] [CommRing R] (φ : A →+* R)
    (T : Set (Fin 2 → A)) (τ : Fin 2 → A) (hτ : τ ∈ Submodule.span A T) :
    (fun i => φ (τ i)) ∈ Submodule.span R ((fun (t : Fin 2 → A) (i : Fin 2) => φ (t i)) '' T) := by
  let Q : Submodule A (Fin 2 → A) :=
    { carrier := {τ | (fun i => φ (τ i)) ∈ Submodule.span R ((fun (t : Fin 2 → A) (i : Fin 2) => φ (t i)) '' T)}
      zero_mem' := by
        simp only [Set.mem_setOf_eq, Pi.zero_apply, map_zero]
        exact (Submodule.span R ((fun (t : Fin 2 → A) (i : Fin 2) => φ (t i)) '' T)).zero_mem
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        have hab : (fun i => φ ((a + b) i)) = (fun i => φ (a i)) + (fun i => φ (b i)) := by
          funext i; simp
        rw [hab]; exact Submodule.add_mem _ ha hb
      smul_mem' := by
        intro c a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        have hca : (fun i => φ ((c • a) i)) = φ c • (fun i => φ (a i)) := by
          funext i; simp
        rw [hca]; exact Submodule.smul_mem _ _ ha }
  have hT : T ⊆ Q := fun t ht => Submodule.subset_span ⟨t, ht, rfl⟩
  exact (Submodule.span_le.mpr hT) hτ

end StalkOnto

namespace StalkOnto

theorem eq_top_of_mem_of_not_mem_smul_top {R : Type} [CommRing R] [IsLocalRing R] {M : Type} [AddCommGroup M] [Module R M]
    [Module.Invertible R M] (G : Submodule R M) (m : M) (hm : m ∈ G)
    (hnot : m ∉ (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R M)) : G = ⊤ := by
  haveI : Module.Free R M := inferInstance
  obtain ⟨e⟩ := (Module.Invertible.free_iff_linearEquiv (R := R) (M := M)).mp this
  set g : M := e.symm 1
  have hrep : ∀ n : M, n = e n • g := by
    intro n; apply e.injective; simp [g]
  have hunit : IsUnit (e m) := by
    by_contra hu
    apply hnot
    have hmem : e m ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr hu
    rw [hrep m]
    exact Submodule.smul_mem_smul hmem Submodule.mem_top
  obtain ⟨c, hc⟩ := hunit
  have hg : g ∈ G := by
    have : g = ((c⁻¹ : Rˣ) : R) • m := by
      rw [hrep m, ← hc, smul_smul, Units.inv_mul, one_smul]
    rw [this]; exact G.smul_mem _ hm
  refine Submodule.eq_top_iff'.mpr fun n => ?_
  rw [hrep n]; exact G.smul_mem _ hg

section GeomPoint

variable {B : Type} [CommRing B] (x : PrimeSpectrum B) (P : Submodule B (Fin 2 → B))

theorem apply_eq_zero_of_mk_mem_maximalIdeal_smul_top {K : Type} [CommRing K] [IsDomain K] (φ : B →+* K)
    (hφ0 : ∀ a ∈ x.asIdeal, φ a = 0) (hφ1 : ∀ c ∉ x.asIdeal, φ c ≠ 0)
    (s : ↥P) (b : x.asIdeal.primeCompl)
    (h : LocalizedModule.mk s b ∈
      (IsLocalRing.maximalIdeal (Localization.AtPrime x.asIdeal)) • (⊤ : Submodule (Localization.AtPrime x.asIdeal) (LocalizedModule x.asIdeal.primeCompl ↥P))) :
    ∀ i, φ ((s : Fin 2 → B) i) = 0 := by
  let Z : Submodule (Localization.AtPrime x.asIdeal) (LocalizedModule x.asIdeal.primeCompl ↥P) :=
    { carrier := {m | ∃ (s' : ↥P) (b' : x.asIdeal.primeCompl), m = LocalizedModule.mk s' b' ∧ ∀ i, φ ((s' : Fin 2 → B) i) = 0}
      zero_mem' := ⟨0, 1, (LocalizedModule.zero_mk 1).symm, fun i => by simp⟩
      add_mem' := by
        rintro _ _ ⟨s₁, b₁, rfl, e₁⟩ ⟨s₂, b₂, rfl, e₂⟩
        refine ⟨b₂ • s₁ + b₁ • s₂, b₁ * b₂, LocalizedModule.mk_add_mk, fun i => ?_⟩
        have hs : ((b₂ • s₁ + b₁ • s₂ : ↥P) : Fin 2 → B) i = (b₂ : B) * (s₁ : Fin 2 → B) i + (b₁ : B) * (s₂ : Fin 2 → B) i := rfl
        rw [hs, map_add, map_mul, map_mul, e₁, e₂, mul_zero, mul_zero, add_zero]
      smul_mem' := by
        rintro c _ ⟨s', b', rfl, e'⟩
        induction c using Localization.induction_on with
        | H y =>
          obtain ⟨a, d⟩ := y
          refine ⟨a • s', d * b', (LocalizedModule.mk_smul_mk a s' d b'), fun i => ?_⟩
          have hs : ((a • s' : ↥P) : Fin 2 → B) i = a * (s' : Fin 2 → B) i := rfl
          rw [hs, map_mul, e', mul_zero] }
  have hle : (IsLocalRing.maximalIdeal (Localization.AtPrime x.asIdeal)) •
      (⊤ : Submodule (Localization.AtPrime x.asIdeal) (LocalizedModule x.asIdeal.primeCompl ↥P)) ≤ Z := by
    refine Submodule.smul_le.mpr fun r hr n _ => ?_
    induction n using LocalizedModule.induction_on with
    | h s₀ b₀ =>
      induction r using Localization.induction_on with
      | H y =>
        obtain ⟨a, d⟩ := y
        have ha : a ∈ x.asIdeal := by
          have h1 : Localization.mk a d * algebraMap B (Localization.AtPrime x.asIdeal) (d : B) =
              algebraMap B (Localization.AtPrime x.asIdeal) a := by
            rw [Localization.mk_eq_mk']; exact IsLocalization.mk'_spec _ a d
          have h2 : algebraMap B (Localization.AtPrime x.asIdeal) a ∈
              IsLocalRing.maximalIdeal (Localization.AtPrime x.asIdeal) := by
            rw [← h1]; exact Ideal.mul_mem_right _ _ hr
          exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime x.asIdeal) x.asIdeal a).mp h2
        refine ⟨a • s₀, d * b₀, LocalizedModule.mk_smul_mk a s₀ d b₀, fun i => ?_⟩
        have hs : ((a • s₀ : ↥P) : Fin 2 → B) i = a * (s₀ : Fin 2 → B) i := rfl
        rw [hs, map_mul, hφ0 a ha, zero_mul]
  obtain ⟨s', b', heq, e'⟩ := hle h
  rw [LocalizedModule.mk_eq] at heq
  obtain ⟨c, hc⟩ := heq
  intro i
  have hci : (c : B) * ((b' : B) * (s : Fin 2 → B) i) = (c : B) * ((b : B) * (s' : Fin 2 → B) i) := by
    have := congrArg (fun (v : ↥P) => (v : Fin 2 → B) i) hc
    exact this
  have := congrArg φ hci
  rw [map_mul, map_mul, map_mul, map_mul, e' i, mul_zero, mul_zero] at this
  rcases mul_eq_zero.mp this with h1 | h1
  · exact absurd h1 (hφ1 c c.2)
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact absurd h2 (hφ1 (b' : B) b'.2)
  · exact h2

theorem exists_algClosed_point :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (φ : B →+* K), RingHom.ker φ = x.asIdeal := by
  let D := B ⧸ x.asIdeal
  let F := FractionRing D
  let K := AlgebraicClosure F
  refine ⟨K, inferInstance, inferInstance,
    ((algebraMap F K).comp (algebraMap D F)).comp (Ideal.Quotient.mk x.asIdeal), ?_⟩
  have hinj : Function.Injective ((algebraMap F K).comp (algebraMap D F)) :=
    (algebraMap F K).injective.comp (IsFractionRing.injective D F)
  rw [← RingHom.comap_ker, (RingHom.injective_iff_ker_eq_bot _).mp hinj, ← RingHom.ker_eq_comap_bot,
    Ideal.mk_ker]

end GeomPoint

end StalkOnto

namespace StalkOnto

theorem apply_mem_span_of_mk_mem_range_sup_smul_top {B : Type} [CommRing B] (x : PrimeSpectrum B)
    (P Q : Submodule B (Fin 2 → B)) (Pi : ↥Q →ₗ[B] ↥P)
    {K : Type} [Field K] (φ : B →+* K) (hφ0 : ∀ a ∈ x.asIdeal, φ a = 0) (hφ1 : ∀ c ∉ x.asIdeal, φ c ≠ 0)
    (s : ↥P) (b : x.asIdeal.primeCompl)
    (h : (LocalizedModule.mk s b : LocalizedModule x.asIdeal.primeCompl ↥P) ∈
      (LinearMap.range (LocalizedModule.map x.asIdeal.primeCompl Pi)).restrictScalars B ⊔
        x.asIdeal • (⊤ : Submodule B (LocalizedModule x.asIdeal.primeCompl ↥P))) :
    (fun i => φ ((s : Fin 2 → B) i)) ∈
      Submodule.span K (Set.range (fun (q : ↥Q) (i : Fin 2) => φ (((Pi q : ↥P) : Fin 2 → B) i))) := by
  set U : Submodule K (Fin 2 → K) := Submodule.span K (Set.range (fun (q : ↥Q) (i : Fin 2) => φ (((Pi q : ↥P) : Fin 2 → B) i))) with hU
  let Z : Submodule B (LocalizedModule x.asIdeal.primeCompl ↥P) :=
    { carrier := {g | ∃ (s' : ↥P) (b' : x.asIdeal.primeCompl), g = LocalizedModule.mk s' b' ∧ (fun i => φ ((s' : Fin 2 → B) i)) ∈ U}
      zero_mem' := ⟨0, 1, (LocalizedModule.zero_mk 1).symm, by
        have : (fun i => φ (((0 : ↥P) : Fin 2 → B) i)) = 0 := by funext i; simp
        rw [this]; exact U.zero_mem⟩
      add_mem' := by
        rintro _ _ ⟨s₁, b₁, rfl, e₁⟩ ⟨s₂, b₂, rfl, e₂⟩
        refine ⟨b₂ • s₁ + b₁ • s₂, b₁ * b₂, LocalizedModule.mk_add_mk, ?_⟩
        have : (fun i => φ (((b₂ • s₁ + b₁ • s₂ : ↥P) : Fin 2 → B) i)) =
            φ (b₂ : B) • (fun i => φ ((s₁ : Fin 2 → B) i)) + φ (b₁ : B) • (fun i => φ ((s₂ : Fin 2 → B) i)) := by
          funext i
          have hs : ((b₂ • s₁ + b₁ • s₂ : ↥P) : Fin 2 → B) i = (b₂ : B) * (s₁ : Fin 2 → B) i + (b₁ : B) * (s₂ : Fin 2 → B) i := rfl
          rw [hs]; simp
        rw [this]; exact U.add_mem (U.smul_mem _ e₁) (U.smul_mem _ e₂)
      smul_mem' := by
        rintro a _ ⟨s', b', rfl, e'⟩
        refine ⟨a • s', b', (LocalizedModule.smul'_mk a s' b'), ?_⟩
        have : (fun i => φ (((a • s' : ↥P) : Fin 2 → B) i)) = φ a • (fun i => φ ((s' : Fin 2 → B) i)) := by
          funext i
          have hs : ((a • s' : ↥P) : Fin 2 → B) i = a * (s' : Fin 2 → B) i := rfl
          rw [hs]; simp
        rw [this]; exact U.smul_mem _ e' }
  have h1 : (LinearMap.range (LocalizedModule.map x.asIdeal.primeCompl Pi)).restrictScalars B ≤ Z := by
    rintro g ⟨q, rfl⟩
    induction q using LocalizedModule.induction_on with
    | h q₀ b₀ =>
      refine ⟨Pi q₀, b₀, LocalizedModule.map_mk _ _ _ _, Submodule.subset_span ⟨q₀, rfl⟩⟩
  have h2 : x.asIdeal • (⊤ : Submodule B (LocalizedModule x.asIdeal.primeCompl ↥P)) ≤ Z := by
    refine Submodule.smul_le.mpr fun a ha g _ => ?_
    induction g using LocalizedModule.induction_on with
    | h s₀ b₀ =>
      refine ⟨a • s₀, b₀, LocalizedModule.smul'_mk a s₀ b₀, ?_⟩
      have : (fun i => φ (((a • s₀ : ↥P) : Fin 2 → B) i)) = 0 := by
        funext i
        have hs : ((a • s₀ : ↥P) : Fin 2 → B) i = a * (s₀ : Fin 2 → B) i := rfl
        rw [hs, map_mul, hφ0 a ha, zero_mul]; rfl
      rw [this]; exact U.zero_mem
  obtain ⟨s', b', heq, e'⟩ := (sup_le h1 h2) h
  rw [LocalizedModule.mk_eq] at heq
  obtain ⟨c, hc⟩ := heq
  have hcoord : ∀ i, φ (c : B) * φ (b' : B) * φ ((s : Fin 2 → B) i) = φ (c : B) * φ (b : B) * φ ((s' : Fin 2 → B) i) := by
    intro i
    have h0 : (c : B) * ((b' : B) * (s : Fin 2 → B) i) = (c : B) * ((b : B) * (s' : Fin 2 → B) i) :=
      congrArg (fun (v : ↥P) => (v : Fin 2 → B) i) hc
    have := congrArg φ h0
    rw [map_mul, map_mul, map_mul, map_mul] at this
    rw [mul_assoc, mul_assoc]; exact this
  have hu : φ (c : B) * φ (b' : B) ≠ 0 := mul_ne_zero (hφ1 _ c.2) (hφ1 _ b'.2)
  have : (fun i => φ ((s : Fin 2 → B) i)) = ((φ (c : B) * φ (b' : B))⁻¹ * (φ (c : B) * φ (b : B))) • (fun i => φ ((s' : Fin 2 → B) i)) := by
    funext i
    show φ ((s : Fin 2 → B) i) = ((φ (c : B) * φ (b' : B))⁻¹ * (φ (c : B) * φ (b : B))) * φ ((s' : Fin 2 → B) i)
    calc φ ((s : Fin 2 → B) i) = (φ (c : B) * φ (b' : B))⁻¹ * (φ (c : B) * φ (b' : B) * φ ((s : Fin 2 → B) i)) := by
          rw [← mul_assoc, inv_mul_cancel₀ hu, one_mul]
      _ = (φ (c : B) * φ (b' : B))⁻¹ * (φ (c : B) * φ (b : B)) * φ ((s' : Fin 2 → B) i) := by
          rw [hcoord i]; ring
  rw [this]
  exact U.smul_mem _ e'

end StalkOnto

namespace StalkOnto

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.GradedCartierModuleData MvFormalGroup MvFormalGroup.CartierModule

section Tangent

variable {p : ℕ} [Fact p.Prime]

theorem tangent_eq_of_mkQ_eq {S : Type} [CommRing S] (X : FormalODModule p S) (jS : Zp2 p →+* S)
    (hc : IsCompl (X.gradedPiece jS 0) (X.gradedPiece jS 1)) (m m' : CartierModule p X.F)
    (h : (X.toGradedCartierModuleData jS hc).vRange.mkQ m = (X.toGradedCartierModuleData jS hc).vRange.mkQ m') :
    tangent m = tangent m' := by
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at h
  obtain ⟨y, hy⟩ := ((X.toGradedCartierModuleData jS hc).mem_vRange_iff _).mp h
  have hy' : verschiebungInt y = m - m' := hy
  have : tangent (m - m') = 0 := by
    rw [← hy']
    exact tangent_verschiebungInt y
  rwa [map_sub, sub_eq_zero] at this

theorem tangent_mem_span_of_mkQ_mem_span {S : Type} [CommRing S] (X : FormalODModule p S) (jS : Zp2 p →+* S)
    (hc : IsCompl (X.gradedPiece jS 0) (X.gradedPiece jS 1))
    (T : Set (X.toGradedCartierModuleData jS hc).LieQuot) (m : CartierModule p X.F)
    (hm : (X.toGradedCartierModuleData jS hc).vRange.mkQ m ∈ Submodule.span (WittVector p S) T) :
    tangent m ∈ Submodule.span S
      {τ : Fin 2 → S | ∃ m' : CartierModule p X.F, (X.toGradedCartierModuleData jS hc).vRange.mkQ m' ∈ T ∧ tangent m' = τ} := by
  let D := X.toGradedCartierModuleData jS hc
  let U : Submodule S (Fin 2 → S) := Submodule.span S
    {τ : Fin 2 → S | ∃ m' : CartierModule p X.F, D.vRange.mkQ m' ∈ T ∧ tangent m' = τ}
  let Q : Submodule (WittVector p S) D.LieQuot :=
    { carrier := {q | ∀ m₂ : CartierModule p X.F, D.vRange.mkQ m₂ = q → tangent m₂ ∈ U}
      zero_mem' := by
        simp only [Set.mem_setOf_eq]
        intro m₂ hm0
        have h0 : tangent m₂ = tangent (0 : CartierModule p X.F) :=
          tangent_eq_of_mkQ_eq X jS hc m₂ 0 (by rw [hm0]; exact (map_zero _).symm)
        rw [h0, map_zero]; exact U.zero_mem
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        intro m₂ hm
        obtain ⟨m₁, rfl⟩ := D.vRange.mkQ_surjective a
        obtain ⟨m₃, rfl⟩ := D.vRange.mkQ_surjective b
        have h13 : D.vRange.mkQ m₂ = D.vRange.mkQ (m₁ + m₃) := by rw [hm, map_add]
        have hsplit : tangent m₂ = tangent m₁ + tangent m₃ := by
          have e1 := tangent_eq_of_mkQ_eq X jS hc m₂ (m₁ + m₃) h13
          have e2 : tangent (m₁ + m₃) = tangent m₁ + tangent m₃ := map_add tangent m₁ m₃
          exact e1.trans e2
        rw [hsplit]; exact U.add_mem (ha m₁ rfl) (hb m₃ rfl)
      smul_mem' := by
        intro w a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        intro m₂ hm
        obtain ⟨m₁, rfl⟩ := D.vRange.mkQ_surjective a
        have h2 : D.vRange.mkQ m₂ = D.vRange.mkQ (w • m₁) := by rw [hm, map_smul]
        have hws : tangent m₂ = w.coeff 0 • tangent m₁ := by
          have e1 := tangent_eq_of_mkQ_eq X jS hc m₂ (w • m₁) h2
          have e2 : tangent (w • m₁) = w.coeff 0 • tangent m₁ := tangent_smul_witt w m₁
          exact e1.trans e2
        rw [hws]; exact U.smul_mem _ (ha m₁ rfl) }
  have hT : T ⊆ Q := by
    intro q hq
    show ∀ m₂ : CartierModule p X.F, D.vRange.mkQ m₂ = q → tangent m₂ ∈ U
    intro m₂ hm
    exact Submodule.subset_span ⟨m₂, hm ▸ hq, rfl⟩
  exact (Submodule.span_le.mpr hT) hm m rfl

theorem exists_mem_gradedPiece_tangent_eq {S : Type} [CommRing S] [Algebra ℤ_[p] S] (X : FormalODModule p S)
    (jS : Zp2 p →+* S) (hS : IsNilpotent (p : S))
    (hc : IsCompl (X.gradedPiece jS 0) (X.gradedPiece jS 1))
    (hLie : IsCompl (X.lieZero jS) (X.lieOne jS)) :
    (∀ τ ∈ X.lieZero jS, ∃ m ∈ X.gradedPiece jS 0, tangent m = τ) ∧
    (∀ τ ∈ X.lieOne jS, ∃ m ∈ X.gradedPiece jS 1, tangent m = τ) := by
  have hsurj := MvFormalGroup.CartierModule.tangent_surjective_of_algebra_padicInt p X.F
  have hTG := CerednikDrinfeld.FormalODModule.tangent_mem_lieZero_and_lieOne_of_mem_gradedPiece_of_isNilpotent p jS hS X
  have hdec : ∀ m : CartierModule p X.F, ∃ m₀ ∈ X.gradedPiece jS 0, ∃ m₁ ∈ X.gradedPiece jS 1, m₀ + m₁ = m := by
    intro m
    have htop : m ∈ X.gradedPiece jS 0 ⊔ X.gradedPiece jS 1 := by rw [hc.sup_eq_top]; exact AddSubgroup.mem_top m
    exact AddSubgroup.mem_sup.mp htop
  constructor
  · intro τ hτ
    obtain ⟨m, rfl⟩ := hsurj τ
    obtain ⟨m₀, hm₀, m₁, hm₁, hsum⟩ := hdec m
    refine ⟨m₀, hm₀, ?_⟩
    have h1 : tangent m₁ ∈ X.lieZero jS ⊓ X.lieOne jS := by
      refine Submodule.mem_inf.mpr ⟨?_, hTG.2 m₁ hm₁⟩
      have : tangent m₁ = tangent m - tangent m₀ := by rw [← hsum, map_add, add_sub_cancel_left]
      rw [this]; exact Submodule.sub_mem _ hτ (hTG.1 m₀ hm₀)
    rw [hLie.inf_eq_bot, Submodule.mem_bot] at h1
    rw [← hsum, map_add, h1, add_zero]
  · intro τ hτ
    obtain ⟨m, rfl⟩ := hsurj τ
    obtain ⟨m₀, hm₀, m₁, hm₁, hsum⟩ := hdec m
    refine ⟨m₁, hm₁, ?_⟩
    have h0 : tangent m₀ ∈ X.lieZero jS ⊓ X.lieOne jS := by
      refine Submodule.mem_inf.mpr ⟨hTG.1 m₀ hm₀, ?_⟩
      have : tangent m₀ = tangent m - tangent m₁ := by rw [← hsum, map_add, add_sub_cancel_right]
      rw [this]; exact Submodule.sub_mem _ hτ (hTG.2 m₁ hm₁)
    rw [hLie.inf_eq_bot, Submodule.mem_bot] at h0
    rw [← hsum, map_add, h0, zero_add]

end Tangent

theorem awayToLoc_awayHom {B : Type} [CommRing B] (x : PrimeSpectrum B) (f : B) (hf : f ∉ x.asIdeal) (b : B) :
    Rigidified.awayToLoc x f hf (Rigidified.awayHom f b) = Rigidified.locHom x b := by
  unfold Rigidified.awayToLoc
  exact IsLocalization.Away.lift_eq f _ b

theorem isNilpotent_awayHom {B : Type} [CommRing B] {p : ℕ} (hB : IsNilpotent (p : B)) (f : B) :
    IsNilpotent (p : Rigidified.Baway f) := by
  obtain ⟨n, hn⟩ := hB
  exact ⟨n, by rw [← map_natCast (Rigidified.awayHom f), ← map_pow, hn, map_zero]⟩

end StalkOnto

namespace StalkOnto

theorem nontrivial_of_invertible_of_nontrivial {R M : Type} [CommRing R] [Nontrivial R] [AddCommGroup M] [Module R M]
    [Module.Invertible R M] : Nontrivial M := by
  by_contra h
  haveI : Subsingleton M := not_nontrivial_iff_subsingleton.mp h
  have : (0 : R) = 1 := (FaithfulSMul.eq_of_smul_eq_smul (M := R) (α := M) fun m => Subsingleton.elim _ _)
  exact zero_ne_one this

theorem isField_baway_one (K : Type) [Field K] : IsField (CerednikDrinfeld.SpecialFormal.Rigidified.Baway (1 : K)) := by
  have hu : ∀ s ∈ Submonoid.powers (1 : K), IsUnit s := by
    rintro s ⟨n, rfl⟩; simp
  let e : K ≃+* CerednikDrinfeld.SpecialFormal.Rigidified.Baway (1 : K) :=
    (IsLocalization.atUnits K (Submonoid.powers (1 : K)) hu).toRingEquiv
  refine ⟨⟨e 0, e 1, fun h => zero_ne_one (e.injective h)⟩, mul_comm, fun {a} ha => ⟨e ((e.symm a)⁻¹), ?_⟩⟩
  have ha' : e.symm a ≠ 0 := fun h => ha (by rw [← e.apply_symm_apply a, h, map_zero])
  calc a * e ((e.symm a)⁻¹) = e (e.symm a) * e ((e.symm a)⁻¹) := by rw [e.apply_symm_apply]
    _ = 1 := by rw [← map_mul, mul_inv_cancel₀ ha', map_one]

noncomputable def equivBawayOne (K : Type) [Field K] : K ≃+* CerednikDrinfeld.SpecialFormal.Rigidified.Baway (1 : K) :=
  (IsLocalization.atUnits K (Submonoid.powers (1 : K)) (by rintro s ⟨n, rfl⟩; simp)).toRingEquiv

end StalkOnto

namespace StalkOnto

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.GradedCartierModuleData MvFormalGroup MvFormalGroup.CartierModule

theorem lieVarpi_map_apply {p : ℕ} [Fact p.Prime] {B S : Type} [CommRing B] [CommRing S]
    (X : FormalODModule p B) (g : B →+* S) (τ : Fin 2 → B) :
    (X.map g).lieVarpi (fun i => g (τ i)) = fun i => g (X.lieVarpi τ i) := by
  funext i
  simp only [FormalODModule.lieVarpi, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, map_sum, map_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1 <;> first | rfl | exact MvPowerSeries.coeff_map _ _ _

theorem tangent_endAct_varpiEnd {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] (X : FormalODModule p B)
    (m : CartierModule p X.F) : tangent (endAct X.varpiEnd m) = X.lieVarpi (tangent m) := by
  rw [endAct_apply, tangent_map]; rfl

theorem nVarpi_nVarpi' {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] {j : Zp2 p →+* B}
    (D : GradedCartierModuleData p B j) (z : D.NMod) : D.nVarpi (D.nVarpi z) = (p : ℕ) • z := by
  obtain ⟨⟨m, m'⟩, rfl⟩ := D.nMk_surjective z
  have h1 : ∀ a b : D.M, D.nVarpi (D.nMk (a, b)) = D.nMk (D.varpi a, D.varpi b) := fun _ _ => rfl
  rw [h1, h1, D.varpi_varpi, D.varpi_varpi, ← map_nsmul]; rfl

theorem latticeRel_of_nsmul {p : ℕ} [Fact p.Prime] {S : Type} [CommRing S] {jS : Zp2 p →+* S}
    (E : GradedCartierModuleData p S jS) {n : ℕ} {r : (Fin 2 → ℤ_[p]) →+ E.NMod}
    {zbar : E.NMod} {v : Fin 2 → ℚ_[p]}
    (h : Rigidified.LatticeRel E n r ((p : ℕ) • zbar) ((p : ℚ_[p]) • v)) :
    Rigidified.LatticeRel E n r zbar v := by
  obtain ⟨m, k, w, hw, hrel⟩ := h
  refine ⟨m + 1, k, w, ?_, ?_⟩
  · rw [pow_succ, ← smul_smul]; exact hw
  · rw [hrel, smul_smul, ← pow_succ, show k + n + m + 1 = k + n + (m + 1) by omega]

end StalkOnto

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial (Rigidified.jbar ι)) (hΦ4 : Φ.HasHeight 4)
    (h0Φ : Φ.lieZero (Rigidified.jbar ι) ≤ LinearMap.ker Φ.lieVarpi)
    (hcΦ : IsCompl (Φ.gradedPiece (Rigidified.jbar ι) 0) (Φ.gradedPiece (Rigidified.jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
    (hLΦ : ∃ L : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod,
      (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).IsCanonicalLMap L)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ
        ((Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).etaPiece L
          hL.isCartierLMap.map_verschiebung 0 : Set _))
    {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B)
    (hB : IsNilpotent (p : B))
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ)
    (N₀ N₁ : PrimeSpectrum B → Submodule ℤ_[p] (Fin 2 → ℚ_[p]))
    (hN₀ : ∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]), v ∈ N₀ x ↔
          ∃ (f : B) (_ : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
            (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
            (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
            ∃ z, t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 0 z v)
    (hN₁ : ∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]), v ∈ N₁ x ↔
          ∃ (f : B) (_ : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
            (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
            (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
            ∃ z, t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 1 z v)
    (hfull₀ : ∀ x, LT.LatticeTree.IsFullLattice (N₀ x)) (hfull₁ : ∀ x, LT.LatticeTree.IsFullLattice (N₁ x))
    (hle : ∀ x, N₀ x ≤ N₁ x) (hsmul : ∀ x, ∀ v ∈ N₁ x, algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) • v ∈ N₀ x)
    (Pi₀ : ↥(t.X.lieZero (structureMap ι ψ)) →ₗ[B] ↥(t.X.lieOne (structureMap ι ψ))) (Pi₁ : ↥(t.X.lieOne (structureMap ι ψ)) →ₗ[B] ↥(t.X.lieZero (structureMap ι ψ)))
    (hPi₀ : ∀ s : ↥(t.X.lieZero (structureMap ι ψ)), ((Pi₀ s : ↥(t.X.lieOne (structureMap ι ψ))) : t.X.Lie) = t.X.lieVarpi (s : t.X.Lie))
    (hPi₁ : ∀ s : ↥(t.X.lieOne (structureMap ι ψ)), ((Pi₁ s : ↥(t.X.lieZero (structureMap ι ψ))) : t.X.Lie) = t.X.lieVarpi (s : t.X.Lie))
    (u₀ : ∀ x : PrimeSpectrum B,
          FormalOmega.latticeBaseChange ℤ_[p] ℚ_[p] (FormalOmega.locRing B x) ⟨N₀ x, hfull₀ x⟩ →ₗ[FormalOmega.locRing B x]
            FormalOmega.stalk B x ↥(t.X.lieZero (structureMap ι ψ)))
    (u₁ : ∀ x : PrimeSpectrum B,
          FormalOmega.latticeBaseChange ℤ_[p] ℚ_[p] (FormalOmega.locRing B x) ⟨N₁ x, hfull₁ x⟩ →ₗ[FormalOmega.locRing B x]
            FormalOmega.stalk B x ↥(t.X.lieOne (structureMap ι ψ)))
    (hg₀ :
      (∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]) (hv : v ∈ N₀ x) (f : B) (hf : f ∉ x.asIdeal)
          (hc : t.IsGradedS ι ψ (Rigidified.awayHom f)) (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f))
          (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
          (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L)
          (z : _) (hz : t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 0 z v),
        ∃ (m : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).M) (s : ↥(t.X.lieZero (structureMap ι ψ)))
          (b : x.asIdeal.primeCompl),
          ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).vRange.mkQ m =
            ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).u L
              hL.isCartierLMap.map_verschiebung ⟨z, (AddSubgroup.mem_inf.mp hz.1).1⟩ ∧
          u₀ x ((1 : FormalOmega.locRing B x) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(N₀ x))) = LocalizedModule.mk s b ∧
          ∀ i, Rigidified.locHom x ((s : t.X.Lie) i) =
            Rigidified.locHom x (b : B) * Rigidified.awayToLoc x f hf (MvFormalGroup.CartierModule.tangent m i)))
    (hg₁ :
      (∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]) (hv : v ∈ N₁ x) (f : B) (hf : f ∉ x.asIdeal)
          (hc : t.IsGradedS ι ψ (Rigidified.awayHom f)) (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f))
          (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
          (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L)
          (z : _) (hz : t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 1 z v),
        ∃ (m : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).M) (s : ↥(t.X.lieOne (structureMap ι ψ)))
          (b : x.asIdeal.primeCompl),
          ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).vRange.mkQ m =
            ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).u L
              hL.isCartierLMap.map_verschiebung ⟨z, (AddSubgroup.mem_inf.mp hz.1).1⟩ ∧
          u₁ x ((1 : FormalOmega.locRing B x) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(N₁ x))) = LocalizedModule.mk s b ∧
          ∀ i, Rigidified.locHom x ((s : t.X.Lie) i) =
            Rigidified.locHom x (b : B) * Rigidified.awayToLoc x f hf (MvFormalGroup.CartierModule.tangent m i)))
 :

    (∀ (x : PrimeSpectrum B) (v : ↥(N₀ x)),
          u₀ x ((1 : FormalOmega.locRing B x) ⊗ₜ[ℤ_[p]] v) ∈
            (LinearMap.range (LocalizedModule.map x.asIdeal.primeCompl Pi₁)).restrictScalars B ⊔
              x.asIdeal • (⊤ : Submodule B (FormalOmega.stalk B x ↥(t.X.lieZero (structureMap ι ψ)))) →
          ∃ w ∈ N₁ x, (v : Fin 2 → ℚ_[p]) = algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) • w) ∧
      (∀ (x : PrimeSpectrum B) (v : ↥(N₁ x)),
          u₁ x ((1 : FormalOmega.locRing B x) ⊗ₜ[ℤ_[p]] v) ∈
            (LinearMap.range (LocalizedModule.map x.asIdeal.primeCompl Pi₀)).restrictScalars B ⊔
              x.asIdeal • (⊤ : Submodule B (FormalOmega.stalk B x ↥(t.X.lieOne (structureMap ι ψ)))) →
          (v : Fin 2 → ℚ_[p]) ∈ N₀ x) := by
  refine ⟨?_, ?_⟩
  · rintro x ⟨v, hv⟩ hmem
    obtain ⟨K, instF, instAC, φ, hker⟩ := StalkOnto.exists_algClosed_point x
    letI instAlg : Algebra ℤ_[p] K := (φ.comp (algebraMap ℤ_[p] B)).toAlgebra
    have hg : φ.comp (algebraMap ℤ_[p] B) = algebraMap ℤ_[p] K := rfl
    have hφ0 : ∀ a ∈ x.asIdeal, φ a = 0 := fun a ha => by rw [← RingHom.mem_ker, hker]; exact ha
    have hφ1 : ∀ c ∉ x.asIdeal, φ c ≠ 0 := fun c hc0 h0 => hc0 (by rw [← hker]; exact h0)
    have hunit : ∀ c ∉ x.asIdeal, IsUnit (φ c) := fun c hc0 => isUnit_iff_ne_zero.mpr (hφ1 c hc0)
    have hpx : (p : B) ∈ x.asIdeal := by
      obtain ⟨n, hn⟩ := hB
      exact x.isPrime.mem_of_pow_mem n (by rw [hn]; exact x.asIdeal.zero_mem)
    have hKp0 : (p : K) = 0 := by rw [← map_natCast φ, hφ0 _ hpx]
    have hKp : IsNilpotent (p : K) := ⟨1, by rw [pow_one, hKp0]⟩
    haveI : CharP K p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hKp0
    have ht' : (t.map φ).IsAdmissible ι (φ.comp ψ) :=
      CerednikDrinfeld.SpecialFormal.Rigidified.IsAdmissible.map_ringHom ι ψ φ t ht
    let x' : PrimeSpectrum K := ⟨⊥, Ideal.isPrime_bot⟩
    have h1x' : (1 : K) ∉ x'.asIdeal := fun h => one_ne_zero ((Ideal.mem_bot).mp h)

    obtain ⟨f, hf, hc, hcb, hcΦf, L, hL, z, hz⟩ := (hN₀ x v).mp hv
    obtain ⟨m, s, b, hm, hu, hs⟩ := hg₀ x v hv f hf hc hcb hcΦf L hL z hz
    rw [hu] at hmem
    have hspanK := StalkOnto.apply_mem_span_of_mk_mem_range_sup_smul_top x (t.X.lieZero (structureMap ι ψ))
      (t.X.lieOne (structureMap ι ψ)) Pi₁ φ hφ0 hφ1 s b hmem

    let ψx : Localization.AtPrime x.asIdeal →+* K := IsLocalization.lift (fun y : x.asIdeal.primeCompl => hunit y y.2)
    have hψloc : ∀ b₀ : B, ψx (Rigidified.locHom x b₀) = φ b₀ := fun b₀ => IsLocalization.lift_eq _ b₀
    let χ : Rigidified.Baway f →+* K := IsLocalization.Away.lift f (hunit f hf)
    have hψχ : ∀ y, ψx (Rigidified.awayToLoc x f hf y) = χ y := by
      intro y
      have hext : ψx.comp (Rigidified.awayToLoc x f hf) = χ := by
        apply IsLocalization.ringHom_ext (Submonoid.powers f)
        ext b₀
        simp only [RingHom.comp_apply]
        rw [StalkOnto.awayToLoc_awayHom, hψloc]
        exact (IsLocalization.Away.lift_eq f (hunit f hf) b₀).symm
      rw [← hext, RingHom.comp_apply]
    have hsφ : ∀ i, φ ((s : t.X.Lie) i) = φ (b : B) * χ (MvFormalGroup.CartierModule.tangent m i) := fun i => by
      have := congrArg ψx (hs i); rwa [hψloc, map_mul, hψloc, hψχ] at this
    have hχspan : (fun i => χ (MvFormalGroup.CartierModule.tangent m i)) ∈ Submodule.span K
        (Set.range fun (q : ↥(t.X.lieOne (structureMap ι ψ))) (i : Fin 2) => φ (((Pi₁ q : ↥(t.X.lieZero (structureMap ι ψ))) : t.X.Lie) i)) := by
      have : (fun i => χ (MvFormalGroup.CartierModule.tangent m i)) = (φ (b : B))⁻¹ • (fun i => φ ((s : t.X.Lie) i)) := by
        funext i
        show χ (MvFormalGroup.CartierModule.tangent m i) = (φ (b : B))⁻¹ * φ ((s : t.X.Lie) i)
        rw [hsφ i, ← mul_assoc, inv_mul_cancel₀ (hφ1 _ b.2), one_mul]
      rw [this]; exact Submodule.smul_mem _ _ hspanK

    obtain ⟨hc'', hcb'', hcΦ'', L'', hL'', z'', hz'', -, hrep⟩ :=
      CerednikDrinfeld.SpecialFormal.Rigidified.exists_isEtaSection_map_and_eq_nMap_and_tangent_eq_of_isEtaSection_of_isUnit
        p ι Φ hcΦ rΦ ψ hB t ht f hc hcb hcΦf L hL 0 z v hz φ hg hKp (hunit f hf) ht'
    obtain ⟨m'', hm'', htan''⟩ := hrep m hm
    let eK := StalkOnto.equivBawayOne K
    letI instFS : Field (Rigidified.Baway (1 : K)) := (StalkOnto.isField_baway_one K).toField
    haveI : IsAlgClosed (Rigidified.Baway (1 : K)) := IsAlgClosed.of_ringEquiv K (Rigidified.Baway (1 : K)) eK
    haveI : CharP (Rigidified.Baway (1 : K)) p := charP_of_injective_ringHom eK.injective p
    letI instAlgS : Algebra ℤ_[p] (Rigidified.Baway (1 : K)) := ((algebraMap K (Rigidified.Baway (1 : K))).comp (algebraMap ℤ_[p] K)).toAlgebra
    have hS1p : IsNilpotent (p : Rigidified.Baway (1 : K)) := StalkOnto.isNilpotent_awayHom hKp 1
    have ht'' : ((t.map φ).map (Rigidified.awayHom (1 : K))).IsAdmissible ι ((Rigidified.awayHom (1 : K)).comp (φ.comp ψ)) :=
      CerednikDrinfeld.SpecialFormal.Rigidified.IsAdmissible.map_ringHom ι (φ.comp ψ) (Rigidified.awayHom (1 : K)) (t.map φ) ht'
    have hXsp : ((t.map φ).XS (Rigidified.awayHom (1 : K))).IsSpecial (Rigidified.jS ι (φ.comp ψ) (Rigidified.awayHom (1 : K))) := ht''.1
    have hX4' : ((t.map φ).XS (Rigidified.awayHom (1 : K))).HasHeight 4 := ht''.2.1

    have hpush := StalkOnto.map_mem_span_image (algebraMap K (Rigidified.Baway (1 : K))) _ _ hχspan
    have htm : (fun i => algebraMap K (Rigidified.Baway (1 : K)) (χ (MvFormalGroup.CartierModule.tangent m i))) = MvFormalGroup.CartierModule.tangent m'' :=
      (funext htan'').symm
    rw [htm] at hpush
    have hgen : (fun (t₀ : Fin 2 → K) (i : Fin 2) => algebraMap K (Rigidified.Baway (1 : K)) (t₀ i)) ''
        Set.range (fun (q : ↥(t.X.lieOne (structureMap ι ψ))) (i : Fin 2) => φ (((Pi₁ q : ↥(t.X.lieZero (structureMap ι ψ))) : t.X.Lie) i)) ⊆
        ((((t.map φ).XS (Rigidified.awayHom (1 : K))).lieOne (Rigidified.jS ι (φ.comp ψ) (Rigidified.awayHom (1 : K)))).map ((t.map φ).XS (Rigidified.awayHom (1 : K))).lieVarpi : Set (Fin 2 → Rigidified.Baway (1 : K))) := by
      rintro _ ⟨_, ⟨q, rfl⟩, rfl⟩
      refine ⟨fun i => algebraMap K (Rigidified.Baway (1 : K)) (φ ((q : t.X.Lie) i)), ?_, ?_⟩
      · have h1 : (fun i => φ ((q : t.X.Lie) i)) ∈ (t.X.map φ).lieOne (φ.comp (structureMap ι ψ)) :=
          (CerednikDrinfeld.FormalODModule.lieZero_lieOne_map_eq_span_image p (structureMap ι ψ) φ t.X).1.2 (Submodule.subset_span ⟨(q : t.X.Lie), q.2, rfl⟩)
        exact (CerednikDrinfeld.FormalODModule.lieZero_lieOne_map_eq_span_image p (φ.comp (structureMap ι ψ)) (Rigidified.awayHom (1 : K)) (t.X.map φ)).1.2
          (Submodule.subset_span ⟨_, h1, rfl⟩)
      · show ((t.X.map φ).map (Rigidified.awayHom (1 : K))).lieVarpi (fun i => Rigidified.awayHom (1 : K) (φ ((q : t.X.Lie) i))) =
          fun i => Rigidified.awayHom (1 : K) (φ (((Pi₁ q : ↥(t.X.lieZero (structureMap ι ψ))) : t.X.Lie) i))
        rw [StalkOnto.lieVarpi_map_apply, StalkOnto.lieVarpi_map_apply]
        funext i; rw [hPi₁ q]
    obtain ⟨τ₁, hτ₁, hτeq⟩ := Submodule.mem_map.mp ((Submodule.span_le.mpr hgen) hpush)
    obtain ⟨m₁, hm₁, hm₁t⟩ := (StalkOnto.exists_mem_gradedPiece_tangent_eq ((t.map φ).XS (Rigidified.awayHom (1 : K))) (Rigidified.jS ι (φ.comp ψ) (Rigidified.awayHom (1 : K))) hS1p hc'' hXsp.1).2 τ₁ hτ₁
    let mC : MvFormalGroup.CartierModule p ((t.map φ).XS (Rigidified.awayHom (1 : K))).F := m''
    have hdiff : MvFormalGroup.CartierModule.tangent (mC - MvFormalGroup.CartierModule.endAct ((t.map φ).XS (Rigidified.awayHom (1 : K))).varpiEnd m₁) = 0 := by
      rw [map_sub, StalkOnto.tangent_endAct_varpiEnd, hm₁t, hτeq, sub_self]
    obtain ⟨g₁, hg₁⟩ := (MvFormalGroup.CartierModule.tangent_eq_zero_iff_exists_verschiebungInt_eq p ((t.map φ).XS (Rigidified.awayHom (1 : K))).F _).mp hdiff
    have hfib : (((t.map φ).XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData _ hc'').toLieQuot z'' = (((t.map φ).XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData _ hc'').vRange.mkQ (MvFormalGroup.CartierModule.endAct ((t.map φ).XS (Rigidified.awayHom (1 : K))).varpiEnd m₁) := by
      have e1 : (((t.map φ).XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData _ hc'').toLieQuot z'' = (((t.map φ).XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData _ hc'').vRange.mkQ m'' := hm''.symm
      rw [e1, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      exact ((((t.map φ).XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData _ hc'').mem_vRange_iff _).mpr ⟨g₁, hg₁⟩

    obtain ⟨z₁, hz₁, hz₁eq⟩ := (CerednikDrinfeld.FormalODModule.exists_nVarpi_eq_of_mem_etaPiece_of_toLieQuot_eq_of_isAlgClosed p (Rigidified.jS ι (φ.comp ψ) (Rigidified.awayHom (1 : K))) ((t.map φ).XS (Rigidified.awayHom (1 : K))) hXsp hX4' hc'' L'' hL'').1 z'' hz''.1 ⟨m₁, hm₁, hfib⟩

    have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
    have hz₁' : (t.map φ).IsEtaSection ι hcΦ rΦ (φ.comp ψ) ht'.2.2.1 (Rigidified.awayHom (1 : K)) hc'' hcb'' hcΦ'' L'' hL'' 1 z₁ ((p : ℚ_[p])⁻¹ • v) := by
      rw [Rigidified.isEtaSection_one_iff]
      refine ⟨hz₁, ?_⟩
      rw [hz₁eq, smul_smul, mul_inv_cancel₀ hp0, one_smul]
      exact ((Rigidified.isEtaSection_zero_iff _ _ _ _ _ _ _ _ _ _ _ _ _ _).mp hz'').2
    refine ⟨(p : ℚ_[p])⁻¹ • v, ?_, ?_⟩
    · exact (CerednikDrinfeld.SpecialFormal.Rigidified.mem_iff_exists_isEtaSection_one_map_of_isAlgClosed_of_ker_eq
        p ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hLΦ hrΦ ψ hB t ht N₁ hN₁ φ hg x hker ht' x' _).mpr ⟨1, h1x', hc'', hcb'', hcΦ'', L'', hL'', z₁, hz₁'⟩
    · show v = algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) • ((p : ℚ_[p])⁻¹ • v)
      rw [map_natCast, smul_smul, mul_inv_cancel₀ hp0, one_smul]
  · rintro x ⟨v, hv⟩ hmem
    obtain ⟨K, instF, instAC, φ, hker⟩ := StalkOnto.exists_algClosed_point x
    letI instAlg : Algebra ℤ_[p] K := (φ.comp (algebraMap ℤ_[p] B)).toAlgebra
    have hg : φ.comp (algebraMap ℤ_[p] B) = algebraMap ℤ_[p] K := rfl
    have hφ0 : ∀ a ∈ x.asIdeal, φ a = 0 := fun a ha => by rw [← RingHom.mem_ker, hker]; exact ha
    have hφ1 : ∀ c ∉ x.asIdeal, φ c ≠ 0 := fun c hc0 h0 => hc0 (by rw [← hker]; exact h0)
    have hunit : ∀ c ∉ x.asIdeal, IsUnit (φ c) := fun c hc0 => isUnit_iff_ne_zero.mpr (hφ1 c hc0)
    have hpx : (p : B) ∈ x.asIdeal := by
      obtain ⟨n, hn⟩ := hB
      exact x.isPrime.mem_of_pow_mem n (by rw [hn]; exact x.asIdeal.zero_mem)
    have hKp0 : (p : K) = 0 := by rw [← map_natCast φ, hφ0 _ hpx]
    have hKp : IsNilpotent (p : K) := ⟨1, by rw [pow_one, hKp0]⟩
    haveI : CharP K p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hKp0
    have ht' : (t.map φ).IsAdmissible ι (φ.comp ψ) :=
      CerednikDrinfeld.SpecialFormal.Rigidified.IsAdmissible.map_ringHom ι ψ φ t ht
    let x' : PrimeSpectrum K := ⟨⊥, Ideal.isPrime_bot⟩
    have h1x' : (1 : K) ∉ x'.asIdeal := fun h => one_ne_zero ((Ideal.mem_bot).mp h)

    obtain ⟨f, hf, hc, hcb, hcΦf, L, hL, z, hz⟩ := (hN₁ x v).mp hv
    obtain ⟨m, s, b, hm, hu, hs⟩ := hg₁ x v hv f hf hc hcb hcΦf L hL z hz
    rw [hu] at hmem
    have hspanK := StalkOnto.apply_mem_span_of_mk_mem_range_sup_smul_top x (t.X.lieOne (structureMap ι ψ))
      (t.X.lieZero (structureMap ι ψ)) Pi₀ φ hφ0 hφ1 s b hmem

    let ψx : Localization.AtPrime x.asIdeal →+* K := IsLocalization.lift (fun y : x.asIdeal.primeCompl => hunit y y.2)
    have hψloc : ∀ b₀ : B, ψx (Rigidified.locHom x b₀) = φ b₀ := fun b₀ => IsLocalization.lift_eq _ b₀
    let χ : Rigidified.Baway f →+* K := IsLocalization.Away.lift f (hunit f hf)
    have hψχ : ∀ y, ψx (Rigidified.awayToLoc x f hf y) = χ y := by
      intro y
      have hext : ψx.comp (Rigidified.awayToLoc x f hf) = χ := by
        apply IsLocalization.ringHom_ext (Submonoid.powers f)
        ext b₀
        simp only [RingHom.comp_apply]
        rw [StalkOnto.awayToLoc_awayHom, hψloc]
        exact (IsLocalization.Away.lift_eq f (hunit f hf) b₀).symm
      rw [← hext, RingHom.comp_apply]
    have hsφ : ∀ i, φ ((s : t.X.Lie) i) = φ (b : B) * χ (MvFormalGroup.CartierModule.tangent m i) := fun i => by
      have := congrArg ψx (hs i); rwa [hψloc, map_mul, hψloc, hψχ] at this
    have hχspan : (fun i => χ (MvFormalGroup.CartierModule.tangent m i)) ∈ Submodule.span K
        (Set.range fun (q : ↥(t.X.lieZero (structureMap ι ψ))) (i : Fin 2) => φ (((Pi₀ q : ↥(t.X.lieOne (structureMap ι ψ))) : t.X.Lie) i)) := by
      have : (fun i => χ (MvFormalGroup.CartierModule.tangent m i)) = (φ (b : B))⁻¹ • (fun i => φ ((s : t.X.Lie) i)) := by
        funext i
        show χ (MvFormalGroup.CartierModule.tangent m i) = (φ (b : B))⁻¹ * φ ((s : t.X.Lie) i)
        rw [hsφ i, ← mul_assoc, inv_mul_cancel₀ (hφ1 _ b.2), one_mul]
      rw [this]; exact Submodule.smul_mem _ _ hspanK

    obtain ⟨hc'', hcb'', hcΦ'', L'', hL'', z'', hz'', -, hrep⟩ :=
      CerednikDrinfeld.SpecialFormal.Rigidified.exists_isEtaSection_map_and_eq_nMap_and_tangent_eq_of_isEtaSection_of_isUnit
        p ι Φ hcΦ rΦ ψ hB t ht f hc hcb hcΦf L hL 1 z v hz φ hg hKp (hunit f hf) ht'
    obtain ⟨m'', hm'', htan''⟩ := hrep m hm
    let eK := StalkOnto.equivBawayOne K
    letI instFS : Field (Rigidified.Baway (1 : K)) := (StalkOnto.isField_baway_one K).toField
    haveI : IsAlgClosed (Rigidified.Baway (1 : K)) := IsAlgClosed.of_ringEquiv K (Rigidified.Baway (1 : K)) eK
    haveI : CharP (Rigidified.Baway (1 : K)) p := charP_of_injective_ringHom eK.injective p
    letI instAlgS : Algebra ℤ_[p] (Rigidified.Baway (1 : K)) := ((algebraMap K (Rigidified.Baway (1 : K))).comp (algebraMap ℤ_[p] K)).toAlgebra
    have hS1p : IsNilpotent (p : Rigidified.Baway (1 : K)) := StalkOnto.isNilpotent_awayHom hKp 1
    have ht'' : ((t.map φ).map (Rigidified.awayHom (1 : K))).IsAdmissible ι ((Rigidified.awayHom (1 : K)).comp (φ.comp ψ)) :=
      CerednikDrinfeld.SpecialFormal.Rigidified.IsAdmissible.map_ringHom ι (φ.comp ψ) (Rigidified.awayHom (1 : K)) (t.map φ) ht'
    have hXsp : ((t.map φ).XS (Rigidified.awayHom (1 : K))).IsSpecial (Rigidified.jS ι (φ.comp ψ) (Rigidified.awayHom (1 : K))) := ht''.1
    have hX4' : ((t.map φ).XS (Rigidified.awayHom (1 : K))).HasHeight 4 := ht''.2.1

    have hpush := StalkOnto.map_mem_span_image (algebraMap K (Rigidified.Baway (1 : K))) _ _ hχspan
    have htm : (fun i => algebraMap K (Rigidified.Baway (1 : K)) (χ (MvFormalGroup.CartierModule.tangent m i))) = MvFormalGroup.CartierModule.tangent m'' :=
      (funext htan'').symm
    rw [htm] at hpush
    have hgen : (fun (t₀ : Fin 2 → K) (i : Fin 2) => algebraMap K (Rigidified.Baway (1 : K)) (t₀ i)) ''
        Set.range (fun (q : ↥(t.X.lieZero (structureMap ι ψ))) (i : Fin 2) => φ (((Pi₀ q : ↥(t.X.lieOne (structureMap ι ψ))) : t.X.Lie) i)) ⊆
        ((((t.map φ).XS (Rigidified.awayHom (1 : K))).lieZero (Rigidified.jS ι (φ.comp ψ) (Rigidified.awayHom (1 : K)))).map ((t.map φ).XS (Rigidified.awayHom (1 : K))).lieVarpi : Set (Fin 2 → Rigidified.Baway (1 : K))) := by
      rintro _ ⟨_, ⟨q, rfl⟩, rfl⟩
      refine ⟨fun i => algebraMap K (Rigidified.Baway (1 : K)) (φ ((q : t.X.Lie) i)), ?_, ?_⟩
      · have h1 : (fun i => φ ((q : t.X.Lie) i)) ∈ (t.X.map φ).lieZero (φ.comp (structureMap ι ψ)) :=
          (CerednikDrinfeld.FormalODModule.lieZero_lieOne_map_eq_span_image p (structureMap ι ψ) φ t.X).1.1 (Submodule.subset_span ⟨(q : t.X.Lie), q.2, rfl⟩)
        exact (CerednikDrinfeld.FormalODModule.lieZero_lieOne_map_eq_span_image p (φ.comp (structureMap ι ψ)) (Rigidified.awayHom (1 : K)) (t.X.map φ)).1.1
          (Submodule.subset_span ⟨_, h1, rfl⟩)
      · show ((t.X.map φ).map (Rigidified.awayHom (1 : K))).lieVarpi (fun i => Rigidified.awayHom (1 : K) (φ ((q : t.X.Lie) i))) =
          fun i => Rigidified.awayHom (1 : K) (φ (((Pi₀ q : ↥(t.X.lieOne (structureMap ι ψ))) : t.X.Lie) i))
        rw [StalkOnto.lieVarpi_map_apply, StalkOnto.lieVarpi_map_apply]
        funext i; rw [hPi₀ q]
    obtain ⟨τ₁, hτ₁, hτeq⟩ := Submodule.mem_map.mp ((Submodule.span_le.mpr hgen) hpush)
    obtain ⟨m₁, hm₁, hm₁t⟩ := (StalkOnto.exists_mem_gradedPiece_tangent_eq ((t.map φ).XS (Rigidified.awayHom (1 : K))) (Rigidified.jS ι (φ.comp ψ) (Rigidified.awayHom (1 : K))) hS1p hc'' hXsp.1).1 τ₁ hτ₁
    let mC : MvFormalGroup.CartierModule p ((t.map φ).XS (Rigidified.awayHom (1 : K))).F := m''
    have hdiff : MvFormalGroup.CartierModule.tangent (mC - MvFormalGroup.CartierModule.endAct ((t.map φ).XS (Rigidified.awayHom (1 : K))).varpiEnd m₁) = 0 := by
      rw [map_sub, StalkOnto.tangent_endAct_varpiEnd, hm₁t, hτeq, sub_self]
    obtain ⟨g₁, hg₁⟩ := (MvFormalGroup.CartierModule.tangent_eq_zero_iff_exists_verschiebungInt_eq p ((t.map φ).XS (Rigidified.awayHom (1 : K))).F _).mp hdiff
    have hfib : (((t.map φ).XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData _ hc'').toLieQuot z'' = (((t.map φ).XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData _ hc'').vRange.mkQ (MvFormalGroup.CartierModule.endAct ((t.map φ).XS (Rigidified.awayHom (1 : K))).varpiEnd m₁) := by
      have e1 : (((t.map φ).XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData _ hc'').toLieQuot z'' = (((t.map φ).XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData _ hc'').vRange.mkQ m'' := hm''.symm
      rw [e1, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      exact ((((t.map φ).XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData _ hc'').mem_vRange_iff _).mpr ⟨g₁, hg₁⟩

    obtain ⟨z₁, hz₁, hz₁eq⟩ := (CerednikDrinfeld.FormalODModule.exists_nVarpi_eq_of_mem_etaPiece_of_toLieQuot_eq_of_isAlgClosed p (Rigidified.jS ι (φ.comp ψ) (Rigidified.awayHom (1 : K))) ((t.map φ).XS (Rigidified.awayHom (1 : K))) hXsp hX4' hc'' L'' hL'').2 z'' hz''.1 ⟨m₁, hm₁, hfib⟩

    have hz₁' : (t.map φ).IsEtaSection ι hcΦ rΦ (φ.comp ψ) ht'.2.2.1 (Rigidified.awayHom (1 : K)) hc'' hcb'' hcΦ'' L'' hL'' 0 z₁ v := by
      rw [Rigidified.isEtaSection_zero_iff]
      refine ⟨hz₁, StalkOnto.latticeRel_of_nsmul _ ?_⟩
      have h2 := ((Rigidified.isEtaSection_one_iff _ _ _ _ _ _ _ _ _ _ _ _ _ _).mp hz'').2
      rw [← hz₁eq, StalkOnto.nVarpi_nVarpi', map_nsmul] at h2
      exact h2
    exact (CerednikDrinfeld.SpecialFormal.Rigidified.mem_iff_exists_isEtaSection_zero_map_of_isAlgClosed_of_ker_eq
      p ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hLΦ hrΦ ψ hB t ht N₀ hN₀ φ hg x hker ht' x' _).mpr ⟨1, h1x', hc'', hcb'', hcΦ'', L'', hL'', z₁, hz₁'⟩

end S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_eq_smul_of_stalkMap_tmul_mem_sup_of_tangent_germ_wittVector
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_eq_smul_of_stalkMap_tmul_mem_sup_of_tangent_germ_wittVector (solution)
