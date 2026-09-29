-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_isFinite_proj_tower_of_finiteBySections
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/d33bda19-18b1-563d-a458-666fb7ab4293

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_pullbackLocalSection_eq_of_ker_mul_maximalIdeal_eq_bot_of_forall_subsingleton_HSucc
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_proj_tower_of_forall_projPresentation_sigma_eq
import Theorems.Thm_AlgebraicGeometry_IsFinite_of_isFinite_comp_of_surjective_of_isProper
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_forall_subsingleton_HSucc_tensorObj_tensorPow_of_isFinite_toProj_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_FiniteBySections_tensor_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_FiniteBySections_of_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_iSup_eq_top_bijective_smul_of_span_pullback_of_surjective
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensorPow_monoidalV2
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_IsPullbackVia_comp
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_sigma_eq_toProj_eq_comp_map_of_algebraMap
import Theorems.Thm_AlgebraicGeometry_ProjSpace_isClosedImmersion_map_of_surjective
import Theorems.Thm_AlgebraicGeometry_surjective_specMap_of_surjective_of_ker_le_nilradical
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isFinite_proj_tower_of_finiteBySections
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.OModulePresheaf.familyFramesGradedModule.moduleBase AlgebraicGeometry.OModulePresheaf.FamilyFrames.module AlgebraicGeometry.OModulePresheaf.FamilyFrames.addCommGroup"
p2m_attr_erase "simp" "AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val"
p2m_attr_erase "simp" "AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open scoped TensorProduct Quaternion
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

universe u

namespace C1ASol

p2m_open "AlgebraicGeometry.Scheme.Modules"

noncomputable def pullbackTensorPowIso {X X' : Scheme.{u}} (p : X' ⟶ X) (N : X.Modules) :
    ∀ m : ℕ, (Scheme.Modules.pullback p).obj (N.tensorPow m) ≅ ((Scheme.Modules.pullback p).obj N).tensorPow m
  | 0 => (Functor.Monoidal.εIso (Scheme.Modules.pullback p)).symm
  | m + 1 => (Functor.Monoidal.μIso (Scheme.Modules.pullback p) (N.tensorPow m) N).symm ≪≫
      tensorIso (pullbackTensorPowIso p N m) (Iso.refl _)

noncomputable def tensorPowIso {X : Scheme.{u}} {N N' : X.Modules} (e : N ≅ N') :
    ∀ m : ℕ, N.tensorPow m ≅ N'.tensorPow m
  | 0 => Iso.refl _
  | m + 1 => tensorIso (tensorPowIso e m) e

def castBase {R : Type u} [CommRing R] {X : Scheme.{u}} {f f' : X ⟶ Spec (.of R)} (h : f = f')
    {M : X.Modules} {N : ℕ} (𝔓 : M.ProjPresentation f N) : M.ProjPresentation f' N := h ▸ 𝔓

theorem castBase_toProj {R : Type u} [CommRing R] {X : Scheme.{u}} {f f' : X ⟶ Spec (.of R)} (h : f = f')
    {M : X.Modules} {N : ℕ} (𝔓 : M.ProjPresentation f N) : (castBase h 𝔓).toProj = 𝔓.toProj := by
  subst h; rfl

theorem iso_hom_inv_apply {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) (U : X.Opens) (x : Γ(N, U)) :
    (e.hom.app U) ((e.inv.app U) x) = x := by
  change ((e.inv.app U) ≫ (e.hom.app U)) x = x
  rw [← Scheme.Modules.Hom.comp_app, e.inv_hom_id, Scheme.Modules.Hom.id_app]
  rfl

end C1ASol

theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]

    (π : ∀ n : ℕ, (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1 + 1)) →+* (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1)))
    (hπ : ∀ n, (π n).comp (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1 + 1))) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))

    (E : ∀ n : ℕ, FakeEllipticCurve Λ 1 (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1)))
    (t : ∀ n : ℕ, (E n).A ⟶ (E (n + 1)).A)
    (ht : ∀ n, FakeEllipticCurve.IsPullbackVia (π n) (E (n + 1)) (E n) (t n))

    (𝓛 : ∀ n : ℕ, (E n).A.Modules)
    (hinv : ∀ n, Scheme.Modules.IsInvertible (𝓛 n))
    (hcompat : ∀ n, Nonempty ((Scheme.Modules.pullback (t n)).obj (𝓛 (n + 1)) ≅ 𝓛 n))
    (hample : Scheme.Modules.FiniteBySections ((𝓛 0) ⊗ (𝓛 0) ⊗ (𝓛 0)) (E 0).f) :
    ∃ (r : ℕ) (ι : ∀ n : ℕ, (E n).A ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) R)),
      (∀ n, IsFinite (ι n)) ∧
      (∀ n, ι n ≫ ProjSpace.π R r = (E n).f ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1))))) ∧
      (∀ n, t n ≫ ι (n + 1) = ι n) := by
  classical

  haveI hprop : ∀ n, IsProper (E n).f := fun n => (E n).bundle.proper
  haveI hflat : ∀ n, Flat (E n).f := fun n => by
    haveI := (E n).bundle.smooth; infer_instance
  let fn : ∀ n : ℕ, (E n).A ⟶ Spec (CommRingCat.of R) := fun n =>
    (E n).f ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1))))

  let C : ∀ n : ℕ, (E n).A.Modules := fun n => 𝓛 n ⊗ 𝓛 n ⊗ 𝓛 n
  have hCinv : ∀ n, Scheme.Modules.IsInvertible (C n) := fun n => (hinv n).tensor_monoidalV2 ((hinv n).tensor_monoidalV2 (hinv n))
  have eL : ∀ n, (Scheme.Modules.pullback (t n)).obj (𝓛 (n + 1)) ≅ 𝓛 n := fun n => (hcompat n).some
  let eC : ∀ n, (Scheme.Modules.pullback (t n)).obj (C (n + 1)) ≅ C n := fun n =>
    (Functor.Monoidal.μIso (Scheme.Modules.pullback (t n)) _ _).symm ≪≫
      tensorIso (eL n) ((Functor.Monoidal.μIso (Scheme.Modules.pullback (t n)) _ _).symm ≪≫ tensorIso (eL n) (eL n))

  haveI hmax : (IsLocalRing.maximalIdeal R ^ (0 + 1)).IsMaximal := by rw [zero_add, pow_one]; infer_instance
  letI kinst : Field (R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1)) := Ideal.Quotient.field _
  obtain ⟨r₀, 𝔔, hfin⟩ := hample
  obtain ⟨m₀, hm₀⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_forall_subsingleton_HSucc_tensorObj_tensorPow_of_isFinite_toProj_monoidalV2
      (R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1)) (E 0).f (C 0) (hCinv 0) r₀ 𝔔 hfin (𝟙_ _) (Scheme.Modules.isInvertible_unit _)
  set m : ℕ := max m₀ 1 with hm
  have hm₀m : m₀ ≤ m := le_max_left _ _
  have h1m : 1 ≤ m := le_max_right _ _

  let 𝓜 : ∀ n : ℕ, (E n).A.Modules := fun n => (C n).tensorPow m
  have h𝓜 : ∀ n, Scheme.Modules.IsInvertible (𝓜 n) := fun n => (hCinv n).tensorPow_monoidalV2 m
  let e𝓜 : ∀ n, (Scheme.Modules.pullback (t n)).obj (𝓜 (n + 1)) ≅ 𝓜 n := fun n =>
    C1ASol.pullbackTensorPowIso (t n) (C (n + 1)) m ≪≫ C1ASol.tensorPowIso (eC n) m
  have hvan0 : ∀ 𝒲 : (E 0).A.OrderedAffineCover, Subsingleton ((OModulePresheaf.ofModules (E 0).f (𝓜 0)).HSucc 𝒲 0) := by
    intro 𝒲
    have h1 := hm₀ m hm₀m 𝒲 0
    obtain ⟨-, h2, -⟩ := AlgebraicGeometry.OModulePresheaf.nonempty_cechEquiv_ofModules_of_iso (E 0).f (λ_ (𝓜 0)) 𝒲
    exact (h2 0).some.symm.toEquiv.subsingleton

  have hFBS : Scheme.Modules.FiniteBySections (𝓜 0) (E 0).f := by
    have key : ∀ j : ℕ, Scheme.Modules.FiniteBySections ((C 0).tensorPow (j + 1)) (E 0).f := by
      intro j
      induction j with
      | zero => exact Scheme.Modules.FiniteBySections.of_iso (λ_ (C 0)).symm ⟨r₀, 𝔔, hfin⟩
      | succ j ih => exact ih.tensor_monoidalV2 ⟨r₀, 𝔔, hfin⟩
    obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [show 𝓜 0 = (C 0).tensorPow (m' + 1) from by simp only [𝓜, hm']]
    exact key m'
  obtain ⟨r, 𝔔₀, hfin₀⟩ := hFBS
  obtain ⟨𝔓₀, h𝔓₀⟩ : ∃ 𝔓₀ : Scheme.Modules.ProjPresentation (𝓜 0) (fn 0) r, IsFinite 𝔓₀.toProj := by
    obtain ⟨𝔓₀', -, hto₀'⟩ :=
      AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_sigma_eq_toProj_eq_comp_map_of_algebraMap (R := R) 𝔔₀
    have hfeq : (E 0).f ≫ Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1)))) = fn 0 := rfl
    refine ⟨C1ASol.castBase hfeq 𝔓₀', ?_⟩
    rw [C1ASol.castBase_toProj, hto₀']
    haveI := hfin₀
    haveI := AlgebraicGeometry.ProjSpace.isClosedImmersion_map_of_surjective
      (R := R) (A := R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1)) Ideal.Quotient.mk_surjective r
    infer_instance
  have hsurj : ∀ n, Surjective (t n) := fun n => by
    obtain ⟨hsq, -⟩ := ht n
    have hmk' : Function.Surjective (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1 + 1))) := Ideal.Quotient.mk_surjective
    have hπs : Function.Surjective (π n) := by
      intro y; obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact ⟨Ideal.Quotient.mk _ x, by rw [← RingHom.comp_apply, hπ n]⟩
    have hkerπ : RingHom.ker (π n) = (IsLocalRing.maximalIdeal R ^ (n + 1)).map (Ideal.Quotient.mk _) := by
      rw [← Ideal.map_comap_of_surjective _ hmk' (RingHom.ker (π n)), RingHom.comap_ker, hπ n, Ideal.mk_ker]
    have hnil : RingHom.ker (π n) ≤ nilradical _ := by
      rw [hkerπ]
      intro x hx
      rw [mem_nilradical]
      refine ⟨2, ?_⟩
      have hx2 : x ^ 2 ∈ ((IsLocalRing.maximalIdeal R ^ (n + 1)).map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1 + 1)))) ^ 2 :=
        Ideal.pow_mem_pow hx 2
      rw [← Ideal.map_pow, ← pow_mul] at hx2
      have hle : ((IsLocalRing.maximalIdeal R) ^ ((n + 1) * 2)).map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1 + 1))) = ⊥ := by
        rw [← le_bot_iff, ← Ideal.map_quotient_self (IsLocalRing.maximalIdeal R ^ (n + 1 + 1))]
        exact Ideal.map_mono (Ideal.pow_le_pow_right (by omega))
      rw [hle] at hx2
      exact hx2
    exact MorphismProperty.of_isPullback (P := @Surjective) hsq.flip
      (AlgebraicGeometry.surjective_specMap_of_surjective_of_ker_le_nilradical (π n) hπs hnil)

  have step : ∀ (n : ℕ) (𝔓n : Scheme.Modules.ProjPresentation (𝓜 n) (fn n) r),
      ∃ 𝔓' : Scheme.Modules.ProjPresentation (𝓜 (n + 1)) (fn (n + 1)) r,
        ∀ i : Fin (r + 1), 𝔓n.σ i =
          ((e𝓜 n).hom.app ⊤) ((((Scheme.Modules.pullbackPushforwardAdjunction (t n)).unit.app (𝓜 (n + 1))).app ⊤) (𝔓'.σ i)) := by
    intro n 𝔓n

    have hpowle : ∀ a b : ℕ, a ≤ b → IsLocalRing.maximalIdeal R ^ b ≤ IsLocalRing.maximalIdeal R ^ a :=
      fun a b h => Ideal.pow_le_pow_right h

    have hmk : ∀ j, Function.Surjective (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (j + 1))) :=
      fun j => Ideal.Quotient.mk_surjective
    have hπs : Function.Surjective (π n) := by
      intro y; obtain ⟨x, rfl⟩ := hmk n y
      exact ⟨Ideal.Quotient.mk _ x, by rw [← RingHom.comp_apply, hπ n]⟩
    have hne : ∀ j, IsLocalRing.maximalIdeal R ^ (j + 1) ≠ ⊤ := fun j h =>
      (IsLocalRing.maximalIdeal.isMaximal R).ne_top (by
        rw [eq_top_iff, ← h]; exact Ideal.pow_le_self (Nat.succ_ne_zero j))
    haveI hloc : ∀ j, IsLocalRing (R ⧸ IsLocalRing.maximalIdeal R ^ (j + 1)) := fun j =>
      haveI : Nontrivial (R ⧸ IsLocalRing.maximalIdeal R ^ (j + 1)) :=
        ⟨⟨0, 1, fun h => hne j (Ideal.Quotient.zero_eq_one_iff.mp h)⟩⟩
      IsLocalRing.of_surjective' (Ideal.Quotient.mk _) (hmk j)
    have hmaxq : ∀ j, IsLocalRing.maximalIdeal (R ⧸ IsLocalRing.maximalIdeal R ^ (j + 1)) =
        (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk _) := by
      intro j
      have hsj := hmk j
      have hker : RingHom.ker (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (j + 1))) ≤ IsLocalRing.maximalIdeal R := by
        rw [Ideal.mk_ker]; exact Ideal.pow_le_self (Nat.succ_ne_zero j)
      have hne' : (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (j + 1))) ≠ ⊤ := by
        intro htop
        have := congrArg (Ideal.comap (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (j + 1)))) htop
        rw [Ideal.comap_map_of_surjective _ hsj, Ideal.comap_top, ← RingHom.ker_eq_comap_bot,
          sup_eq_left.mpr hker] at this
        exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top this
      rcases Ideal.map_eq_top_or_isMaximal_of_surjective _ hsj (IsLocalRing.maximalIdeal.isMaximal R) with h | h
      · exact absurd h hne'
      · exact (IsLocalRing.eq_maximalIdeal h).symm
    have hkerπ : RingHom.ker (π n) = (IsLocalRing.maximalIdeal R ^ (n + 1)).map (Ideal.Quotient.mk _) := by
      rw [← Ideal.map_comap_of_surjective _ (hmk (n + 1)) (RingHom.ker (π n)), RingHom.comap_ker, hπ n, Ideal.mk_ker]
    have hsmall : RingHom.ker (π n) * IsLocalRing.maximalIdeal (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1 + 1)) = ⊥ := by
      rw [hkerπ, hmaxq, ← Ideal.map_mul, ← pow_succ, Ideal.map_quotient_self]

    let G : ∀ j : ℕ, ((E 0).A ⟶ (E (j + 1)).A) := fun j =>
      Nat.rec (motive := fun j => (E 0).A ⟶ (E (j + 1)).A) (t 0) (fun j g => g ≫ t (j + 1)) j
    let sφ : ∀ j : ℕ, (R ⧸ IsLocalRing.maximalIdeal R ^ (j + 1 + 1)) →+* (R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1)) := fun j =>
      Nat.rec (motive := fun j => (R ⧸ IsLocalRing.maximalIdeal R ^ (j + 1 + 1)) →+* (R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1)))
        (π 0) (fun j s => s.comp (π (j + 1))) j
    have hGvia : ∀ j, FakeEllipticCurve.IsPullbackVia (sφ j) (E (j + 1)) (E 0) (G j) := by
      intro j
      induction j with
      | zero => exact ht 0
      | succ j ih =>
        exact CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia.comp (π (j + 1)) (sφ j) (E (j + 1 + 1)) (E (j + 1)) (E 0)
          (t (j + 1)) (G j) (ht (j + 1)) ih
    have hsφmk : ∀ j, (sφ j).comp (Ideal.Quotient.mk _) = Ideal.Quotient.mk _ := by
      intro j
      induction j with
      | zero => exact hπ 0
      | succ j ih =>
        show ((sφ j).comp (π (j + 1))).comp (Ideal.Quotient.mk _) = _
        rw [RingHom.comp_assoc, hπ (j + 1), ih]
    have hsφs : Function.Surjective (sφ n) := by
      intro y; obtain ⟨x, rfl⟩ := hmk 0 y
      exact ⟨Ideal.Quotient.mk _ x, by rw [← RingHom.comp_apply, hsφmk n]⟩
    have hsφk : RingHom.ker (sφ n) = IsLocalRing.maximalIdeal (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1 + 1)) := by
      rw [hmaxq (n + 1), ← Ideal.map_comap_of_surjective _ (hmk (n + 1)) (RingHom.ker (sφ n)), RingHom.comap_ker,
        hsφmk n, Ideal.mk_ker, zero_add, pow_one]
    obtain ⟨hGsq, -⟩ := hGvia n
    obtain ⟨htsq, -⟩ := ht n

    have eG : ∀ j, Nonempty ((Scheme.Modules.pullback (G j)).obj (𝓜 (j + 1)) ≅ 𝓜 0) := by
      intro j
      induction j with
      | zero => exact ⟨e𝓜 0⟩
      | succ j ih =>
        refine ⟨((Scheme.Modules.pullbackComp (G j) (t (j + 1))).app (𝓜 (j + 1 + 1))).symm ≪≫
          (Scheme.Modules.pullback (G j)).mapIso (e𝓜 (j + 1)) ≪≫ ih.some⟩
    have hvanG : ∀ 𝒰 : (E 0).A.OrderedAffineCover,
        Subsingleton ((OModulePresheaf.ofModules (E 0).f ((Scheme.Modules.pullback (G n)).obj (𝓜 (n + 1)))).HSucc 𝒰 0) := by
      intro 𝒰
      obtain ⟨-, h2, -⟩ := AlgebraicGeometry.OModulePresheaf.nonempty_cechEquiv_ofModules_of_iso (E 0).f (eG n).some 𝒰
      exact (h2 0).some.toEquiv.subsingleton

    haveI := hprop (n + 1)
    haveI := hflat (n + 1)
    have hlift : ∀ i : Fin (r + 1), ∃ σ : Γ(𝓜 (n + 1), ⊤),
        Scheme.Modules.pullbackLocalSection (t n) σ = ((e𝓜 n).inv.app ⊤) (𝔓n.σ i) := fun i =>
      AlgebraicGeometry.Scheme.Modules.exists_pullbackLocalSection_eq_of_ker_mul_maximalIdeal_eq_bot_of_forall_subsingleton_HSucc
        (π n) hπs hsmall (sφ n) hsφs hsφk (E (n + 1)).f (E n).f (t n) htsq (E 0).f (G n) hGsq (𝓜 (n + 1)) (h𝓜 (n + 1)) hvanG _
    choose σ' hσ' using hlift

    haveI := hsurj n
    obtain ⟨𝔓n', h𝔓n'to, h𝔓n'σ⟩ :=
      AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_of_iso 𝔓n (e𝓜 n).symm
    have hcov : (⨆ j : Fin (r + 1), 𝔓n'.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) R) (MvPolynomial.X j)) = ⊤ := by
      rw [← Scheme.Hom.preimage_iSup, Proj.iSup_basicOpen_eq_top _ _ (ProjSpace.irrelevant_le_span_X R r), Scheme.Hom.preimage_top]
    have hσn' : ∀ i, 𝔓n'.σ i = ((e𝓜 n).inv.app ⊤) (𝔓n.σ i) := fun i => h𝔓n'σ i
    obtain ⟨U, hU, hframeU⟩ :=
      AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_iSup_eq_top_bijective_smul_of_span_pullback_of_surjective
        (t n) (𝓜 (n + 1)) (h𝓜 (n + 1)) σ' (fun i => ((e𝓜 n).inv.app ⊤) (𝔓n.σ i))
        (fun i => by beta_reduce; rw [← hσ' i]; rfl)
        𝔓n'.σ _ hcov (fun j V' hV' => 𝔓n'.frame j V' hV')
        (fun j => ⟨Pi.single j 1, by rw [hσn' j]; simp [Pi.single_apply, Finset.sum_ite_eq]⟩)
    obtain ⟨𝔓', h𝔓'σ, -⟩ :=
      AlgebraicGeometry.Scheme.Modules.exists_projPresentation_of_iSup_eq_top (fn (n + 1)) (𝓜 (n + 1)) r σ' U hU hframeU
    refine ⟨𝔓', fun i => ?_⟩
    rw [h𝔓'σ]
    change 𝔓n.σ i = ((e𝓜 n).hom.app ⊤) (Scheme.Modules.pullbackLocalSection (t n) (σ' i))
    rw [hσ' i, C1ASol.iso_hom_inv_apply]

  let 𝔓seq : ∀ n : ℕ, Scheme.Modules.ProjPresentation (𝓜 n) (fn n) r :=
    fun n => Nat.rec (motive := fun n => Scheme.Modules.ProjPresentation (𝓜 n) (fn n) r) 𝔓₀ (fun n 𝔓n => (step n 𝔓n).choose) n
  have hσ : ∀ (n : ℕ) (i : Fin (r + 1)), (𝔓seq n).σ i =
      ((e𝓜 n).hom.app ⊤) ((((Scheme.Modules.pullbackPushforwardAdjunction (t n)).unit.app (𝓜 (n + 1))).app ⊤) ((𝔓seq (n + 1)).σ i)) :=
    fun n i => (step n (𝔓seq n)).choose_spec i

  obtain ⟨ι, hιeq, hιπ, hιt⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_proj_tower_of_forall_projPresentation_sigma_eq
      hqq' hB Λ hΛ μ hμ star hstar R π hπ E t ht 𝓜 e𝓜 r 𝔓seq hσ

  have hproperι : ∀ n, IsProper (ι n) := fun n => by
    haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1))))) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    haveI : IsProper (ι n ≫ ProjSpace.π R r) := by rw [hιπ n]; infer_instance
    haveI : IsSeparated (ProjSpace.π R r) := by unfold ProjSpace.π; infer_instance
    haveI := UniversallyClosed.of_comp_of_isSeparated (ι n) (ProjSpace.π R r)
    haveI := IsSeparated.of_comp (ι n) (ProjSpace.π R r)
    haveI := locallyOfFiniteType_of_comp (ι n) (ProjSpace.π R r)
    exact IsProper.mk
  have hfinι : ∀ n, IsFinite (ι n) := by
    intro n
    induction n with
    | zero => rw [hιeq 0]; exact h𝔓₀
    | succ n ih =>
      haveI := hsurj n
      haveI := hproperι (n + 1)
      haveI : IsFinite (t n ≫ ι (n + 1)) := by rw [hιt n]; exact ih
      exact AlgebraicGeometry.IsFinite.of_isFinite_comp_of_surjective_of_isProper (t n) (ι (n + 1))
  exact ⟨r, ι, hfinι, hιπ, hιt⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isFinite_proj_tower_of_finiteBySections
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isFinite_proj_tower_of_finiteBySections (solution)
