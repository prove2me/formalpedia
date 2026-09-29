-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.length_gradedSubmodule_quotient_map_varpiLinear_eq_one_of_isSpecial_of_hasHeight
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/4ea8262c-73fb-5054-b1b8-f6e7eb2e2d05

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Theorems.Thm_MvFormalGroup_CartierModule_length_quotient_range_mapLinear_eq_of_finrank_eq_pow
import Theorems.Thm_MvFormalGroup_CartierModule_map_injective_of_finite_quotient
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_of_isSpecial_field
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isSpecialCartierModule_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isNilpotent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_length_gradedSubmodule_quotient_map_varpiLinear_eq_one_of_isSpecial_of_hasHeight
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

namespace Ws23PiColength

set_option linter.unusedSectionVars false

section General

variable {R : Type} [Ring R] {M : Type} [AddCommGroup M] [Module R M]

theorem length_quot_eq_add (A B C : Submodule R M) (hCB : C ≤ B) (hBA : B ≤ A) :
    Module.length R (↥A ⧸ Submodule.comap A.subtype C) =
      Module.length R (↥B ⧸ Submodule.comap B.subtype C) +
        Module.length R (↥A ⧸ Submodule.comap A.subtype B) := by
  have hle : Submodule.comap B.subtype C ≤
      Submodule.comap (Submodule.inclusion hBA) (Submodule.comap A.subtype C) := by
    intro x hx; exact hx
  have hle' : Submodule.comap A.subtype C ≤ Submodule.comap A.subtype B :=
    Submodule.comap_mono hCB
  refine Module.length_eq_add_of_exact
    (Submodule.mapQ _ _ (Submodule.inclusion hBA) hle) (Submodule.factor hle') ?_ ?_ ?_
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [LinearMap.mem_ker, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    exact (Submodule.Quotient.mk_eq_zero _).mpr hx
  · intro y
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨Submodule.Quotient.mk a, rfl⟩
  · rw [LinearMap.exact_iff]
    ext x
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hfa : Submodule.factor hle' (Submodule.Quotient.mk a) =
        (Submodule.Quotient.mk a : ↥A ⧸ Submodule.comap A.subtype B) := rfl
    rw [LinearMap.mem_ker, hfa, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, LinearMap.mem_range]
    constructor
    · intro ha
      exact ⟨Submodule.Quotient.mk ⟨(a : M), ha⟩, rfl⟩
    · rintro ⟨y, hy⟩
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rw [Submodule.mapQ_apply, Submodule.Quotient.eq] at hy
      have hba : ((b : ↥B) : M) - (a : M) ∈ C := by simpa using hy
      have hb : ((b : ↥B) : M) ∈ B := b.2
      have : (a : M) = (b : M) - (((b : ↥B) : M) - (a : M)) := by abel
      rw [Submodule.coe_subtype, this]
      exact B.sub_mem hb (hCB hba)

theorem length_eq_of_bijective {R₂ : Type} [Ring R₂] {M₂ : Type} [AddCommGroup M₂] [Module R₂ M₂]
    {τ : R →+* R₂} [RingHomSurjective τ] (f : M →ₛₗ[τ] M₂) (hf : Function.Bijective f) :
    Module.length R M = Module.length R₂ M₂ := by
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f hf)]

theorem length_quot_map_eq {M₂ : Type} [AddCommGroup M₂] [Module R M₂]
    (f : M →ₗ[R] M₂) (hf : Function.Injective f) (T S : Submodule R M) (hST : S ≤ T) :
    Module.length R (↥(T.map f) ⧸ Submodule.comap (T.map f).subtype (S.map f)) =
      Module.length R (↥T ⧸ Submodule.comap T.subtype S) := by
  haveI : RingHomSurjective (RingHom.id R) := ⟨Function.surjective_id⟩
  let ψ : ↥T →ₗ[R] ↥(T.map f) :=
    { toFun := fun x => ⟨f x, ⟨x, x.2, rfl⟩⟩
      map_add' := fun x y => by
        apply Subtype.ext
        show f ((x : M) + y) = f x + f y
        exact map_add f _ _
      map_smul' := fun c x => by
        apply Subtype.ext
        show f (c • (x : M)) = c • f x
        exact map_smul f _ _ }
  have hψ : ∀ x : ↥T, ((ψ x : ↥(T.map f)) : M₂) = f x := fun _ => rfl
  have hle : Submodule.comap T.subtype S ≤ Submodule.comap ψ (Submodule.comap (T.map f).subtype (S.map f)) := by
    intro x hx
    show ((ψ x : ↥(T.map f)) : M₂) ∈ S.map f
    rw [hψ]; exact ⟨x, hx, rfl⟩
  symm
  refine length_eq_of_bijective (Submodule.mapQ _ _ ψ hle) ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [LinearMap.mem_ker, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    rw [Submodule.Quotient.mk_eq_zero]
    change ((ψ a : ↥(T.map f)) : M₂) ∈ S.map f at hx
    rw [hψ] at hx
    obtain ⟨b, hb, hba⟩ := hx
    have : b = (a : M) := hf hba
    show (a : M) ∈ S
    rw [← this]; exact hb
  · intro y
    obtain ⟨⟨_, ⟨a, ha, rfl⟩⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨Submodule.Quotient.mk ⟨a, ha⟩, rfl⟩

end General

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [CharP K p] {j : Zp2 p →+* K}

local notation "𝕎" => WittVector p K

open CerednikDrinfeld.GradedCartierModuleData

def vImg (D : GradedCartierModuleData p K j) (S : Submodule 𝕎 D.M) : Submodule 𝕎 D.M where
  carrier := D.verschiebung '' (S : Set D.M)
  zero_mem' := ⟨0, S.zero_mem, map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, S.add_mem ha hb, map_add _ _ _⟩
  smul_mem' := by
    rintro w _ ⟨a, ha, rfl⟩
    exact ⟨WittVector.frobenius w • a, S.smul_mem _ ha, (D.smul_verschiebung w a).symm⟩

theorem mem_vImg_iff (D : GradedCartierModuleData p K j) (S : Submodule 𝕎 D.M) (x : D.M) :
    x ∈ vImg D S ↔ ∃ a ∈ S, D.verschiebung a = x := Iff.rfl

theorem vImg_mono (D : GradedCartierModuleData p K j) {S T : Submodule 𝕎 D.M} (h : S ≤ T) :
    vImg D S ≤ vImg D T := by
  rintro _ ⟨a, ha, rfl⟩; exact ⟨a, h ha, rfl⟩

theorem vImg_piece_le (D : GradedCartierModuleData p K j) (i : Fin 2) :
    vImg D (D.piece i) ≤ D.piece (i + 1) := by
  rintro _ ⟨a, ha, rfl⟩
  exact D.verschiebung_mem i a ha

theorem map_varpi_vImg (D : GradedCartierModuleData p K j) (S : Submodule 𝕎 D.M) :
    (vImg D S).map D.varpi = vImg D (S.map D.varpi) := by
  ext z
  simp only [mem_vImg_iff, Submodule.mem_map]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨D.varpi a, ⟨a, ha, rfl⟩, (D.varpi_verschiebung a).symm⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨D.verschiebung a, ⟨a, ha, rfl⟩, D.varpi_verschiebung a⟩

theorem length_quot_eq_one {M : Type} [AddCommGroup M] [Module 𝕎 M]
    (A T : Submodule 𝕎 M) (hTA : T ≤ A) (g : M) (hg : g ∈ A) (hgT : g ∉ T)
    (hgen : ∀ a ∈ A, ∃ (c : K) (r : M), r ∈ T ∧ a = WittVector.teichmuller p c • g + r) :
    Module.length 𝕎 (↥A ⧸ Submodule.comap A.subtype T) = 1 := by
  rw [Module.length_eq_one_iff, isSimpleModule_iff_isCoatom]
  refine ⟨fun htop => hgT ?_, fun S hS => ?_⟩
  · have : (⟨g, hg⟩ : ↥A) ∈ Submodule.comap A.subtype T := htop.symm ▸ Submodule.mem_top
    exact this
  · obtain ⟨s, hsS, hsT⟩ := Set.exists_of_ssubset hS
    obtain ⟨c, r, hr, hs⟩ := hgen (s : M) s.2
    have hc : c ≠ 0 := by
      rintro rfl
      apply hsT
      show (s : M) ∈ T
      rw [hs, WittVector.teichmuller_zero, zero_smul, zero_add]; exact hr
    have hrS : (⟨r, hTA hr⟩ : ↥A) ∈ S := hS.le (show r ∈ T from hr)
    have hcg : (⟨WittVector.teichmuller p c • g, A.smul_mem _ hg⟩ : ↥A) ∈ S := by
      have : (⟨WittVector.teichmuller p c • g, A.smul_mem _ hg⟩ : ↥A) = s - ⟨r, hTA hr⟩ := by
        apply Subtype.ext
        show WittVector.teichmuller p c • g = (s : M) - r
        rw [hs, add_sub_cancel_right]
      rw [this]; exact S.sub_mem hsS hrS
    have hgS : (⟨g, hg⟩ : ↥A) ∈ S := by
      have : (⟨g, hg⟩ : ↥A) =
          WittVector.teichmuller p c⁻¹ • (⟨WittVector.teichmuller p c • g, A.smul_mem _ hg⟩ : ↥A) := by
        apply Subtype.ext
        show g = WittVector.teichmuller p c⁻¹ • (WittVector.teichmuller p c • g)
        rw [smul_smul, ← map_mul, inv_mul_cancel₀ hc, map_one, one_smul]
      rw [this]; exact S.smul_mem _ hcg
    rw [eq_top_iff]
    rintro ⟨a, ha⟩ -
    obtain ⟨c', r', hr', ha'⟩ := hgen a ha
    have : (⟨a, ha⟩ : ↥A) = WittVector.teichmuller p c' • ⟨g, hg⟩ + ⟨r', hTA hr'⟩ := by
      apply Subtype.ext; exact ha'
    rw [this]
    exact S.add_mem (S.smul_mem _ hgS) (hS.le (show r' ∈ T from hr'))

theorem exists_eq_teichmuller_smul_add_verschiebung (D : GradedCartierModuleData p K j)
    (γ : Fin 2 → D.M) (hγ : D.IsHomogeneousVBasis γ) (i : Fin 2) (x : D.M) (hx : x ∈ D.piece (i + 1)) :
    ∃ (c : K) (y : D.M), y ∈ D.piece i ∧
      x = WittVector.teichmuller p c • γ (i + 1) + D.verschiebung y := by
  obtain ⟨⟨c, y⟩, hxy, -⟩ := hγ.2 x
  simp only [Fin.sum_univ_two] at hxy
  have hy : y ∈ D.piece 0 ⊔ D.piece 1 := by rw [D.isCompl_piece.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨y₀, hy₀, y₁, hy₁, rfl⟩ := Submodule.mem_sup.mp hy
  have h10 : (1 : Fin 2) + 1 = 0 := rfl
  have h01 : (0 : Fin 2) + 1 = 1 := rfl

  set u : D.M := WittVector.teichmuller p (c 0) • γ 0 + D.verschiebung y₁ with hu_def
  set v : D.M := WittVector.teichmuller p (c 1) • γ 1 + D.verschiebung y₀ with hv_def
  have hu : u ∈ D.piece 0 :=
    (D.piece 0).add_mem ((D.piece 0).smul_mem _ (hγ.1 0)) (h10 ▸ D.verschiebung_mem 1 y₁ hy₁)
  have hv : v ∈ D.piece 1 :=
    (D.piece 1).add_mem ((D.piece 1).smul_mem _ (hγ.1 1)) (h01 ▸ D.verschiebung_mem 0 y₀ hy₀)
  have hsplit : x = v + u := by
    rw [hxy, map_add]; simp only [hu_def, hv_def]; abel
  have hdisj := Submodule.disjoint_def.mp D.isCompl_piece.disjoint
  fin_cases i
  ·
    refine ⟨c 1, y₀, hy₀, ?_⟩
    have hu1 : u ∈ D.piece 1 := by
      have : u = x - v := by rw [hsplit]; abel
      rw [this]; exact (D.piece 1).sub_mem hx hv
    have hu0 : u = 0 := hdisj _ hu hu1
    rw [hsplit, hu0, add_zero]
    exact hv_def
  ·
    refine ⟨c 0, y₁, hy₁, ?_⟩
    have hv0' : v ∈ D.piece 0 := by
      have : v = x - u := by rw [hsplit]; abel
      rw [this]; exact (D.piece 0).sub_mem hx hu
    have hv0 : v = 0 := hdisj _ hv0' hv
    rw [hsplit, hv0, zero_add]
    exact hu_def

theorem verschiebung_ne_basis (D : GradedCartierModuleData p K j)
    (γ : Fin 2 → D.M) (hγ : D.IsHomogeneousVBasis γ) (i : Fin 2) (y : D.M) :
    D.verschiebung y ≠ γ i := by
  intro h
  obtain ⟨cy, -, huniq⟩ := hγ.2 (γ i)
  have h1 : ((fun k => if k = i then (1 : K) else 0), (0 : D.M)) = cy :=
    huniq _ (by fin_cases i <;> simp [Fin.sum_univ_two])
  have h2 : ((fun _ => (0 : K)), y) = cy :=
    huniq _ (by simp [h])
  have := congrArg (fun q => q.1 i) (h1.trans h2.symm)
  simp at this

theorem length_piece_quot_vImg_eq_one (D : GradedCartierModuleData p K j)
    (γ : Fin 2 → D.M) (hγ : D.IsHomogeneousVBasis γ) (i : Fin 2) :
    Module.length 𝕎 (↥(D.piece (i + 1)) ⧸
      Submodule.comap (D.piece (i + 1)).subtype (vImg D (D.piece i))) = 1 := by
  refine length_quot_eq_one _ _ (vImg_piece_le D i) (γ (i + 1)) (hγ.1 (i + 1)) ?_ ?_
  · rintro ⟨y, -, hy⟩; exact verschiebung_ne_basis D γ hγ (i + 1) y hy
  · intro a ha
    obtain ⟨c, y, hy, rfl⟩ := exists_eq_teichmuller_smul_add_verschiebung D γ hγ i a ha
    exact ⟨c, _, ⟨y, hy, rfl⟩, rfl⟩

theorem length_quot_vImg_eq [PerfectRing K p] (D : GradedCartierModuleData p K j)
    (γ : Fin 2 → D.M) (hγ : D.IsHomogeneousVBasis γ) (T S : Submodule 𝕎 D.M) (hST : S ≤ T) :
    Module.length 𝕎 (↥(vImg D T) ⧸ Submodule.comap (vImg D T).subtype (vImg D S)) =
      Module.length 𝕎 (↥T ⧸ Submodule.comap T.subtype S) := by
  let τ : 𝕎 →+* 𝕎 := ((WittVector.frobeniusEquiv p K).symm : _ ≃+* _)
  haveI : RingHomSurjective τ := ⟨(WittVector.frobeniusEquiv p K).symm.surjective⟩
  have hτ : ∀ u, WittVector.frobenius (τ u) = u := fun u => by
    show (WittVector.frobeniusEquiv p K) ((WittVector.frobeniusEquiv p K).symm u) = u
    exact RingEquiv.apply_symm_apply _ _
  let ψ : ↥T →ₛₗ[τ] ↥(vImg D T) :=
    { toFun := fun x => ⟨D.verschiebung x, ⟨x, x.2, rfl⟩⟩
      map_add' := fun x y => by
        apply Subtype.ext
        show D.verschiebung ((x : D.M) + y) = D.verschiebung x + D.verschiebung y
        exact map_add _ _ _
      map_smul' := fun u x => by
        apply Subtype.ext
        show D.verschiebung (u • (x : D.M)) = τ u • D.verschiebung x
        rw [D.smul_verschiebung (τ u), hτ] }
  have hψ : ∀ x : ↥T, ((ψ x : ↥(vImg D T)) : D.M) = D.verschiebung x := fun _ => rfl
  have hle : Submodule.comap T.subtype S ≤
      Submodule.comap ψ (Submodule.comap (vImg D T).subtype (vImg D S)) := by
    intro x hx
    show ((ψ x : ↥(vImg D T)) : D.M) ∈ vImg D S
    rw [hψ]
    exact ⟨x, hx, rfl⟩
  symm
  refine length_eq_of_bijective (Submodule.mapQ _ _ ψ hle) ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [LinearMap.mem_ker, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    rw [Submodule.Quotient.mk_eq_zero]
    change ((ψ a : ↥(vImg D T)) : D.M) ∈ vImg D S at hx
    rw [hψ] at hx
    obtain ⟨b, hb, hba⟩ := hx
    have : b = (a : D.M) := hγ.verschiebung_injective hba
    show (a : D.M) ∈ S
    rw [← this]; exact hb
  · intro y
    obtain ⟨⟨_, ⟨a, ha, rfl⟩⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨Submodule.Quotient.mk ⟨a, ha⟩, rfl⟩

theorem length_piece_quot_varpi_balance [PerfectRing K p] (D : GradedCartierModuleData p K j)
    (γ : Fin 2 → D.M) (hγ : D.IsHomogeneousVBasis γ) (hPi : Function.Injective D.varpi) :
    Module.length 𝕎 (↥(D.piece 1) ⧸
        Submodule.comap (D.piece 1).subtype ((D.piece 0).map D.varpi)) =
      Module.length 𝕎 (↥(D.piece 0) ⧸
        Submodule.comap (D.piece 0).subtype ((D.piece 1).map D.varpi)) := by
  classical

  set A : Submodule 𝕎 D.M := D.piece 1 with hA
  set Q : Submodule 𝕎 D.M := vImg D (D.piece 0) with hQ
  set P : Submodule 𝕎 D.M := (D.piece 0).map D.varpi with hP
  set R : Submodule 𝕎 D.M := vImg D ((D.piece 1).map D.varpi) with hR
  have hR' : R = (vImg D (D.piece 1)).map D.varpi := (map_varpi_vImg D _).symm
  have h10 : (1 : Fin 2) + 1 = 0 := rfl
  have h01 : (0 : Fin 2) + 1 = 1 := rfl
  have hPi10 : (D.piece 1).map D.varpi ≤ D.piece 0 :=
    Submodule.map_le_iff_le_comap.mpr fun x hx => h10 ▸ D.varpi_mem 1 x hx
  have hPi01 : (D.piece 0).map D.varpi ≤ D.piece 1 :=
    Submodule.map_le_iff_le_comap.mpr fun x hx => h01 ▸ D.varpi_mem 0 x hx
  have hV10 : vImg D (D.piece 1) ≤ D.piece 0 := h10 ▸ vImg_piece_le D 1
  have hQA : Q ≤ A := by rw [hQ, hA]; exact vImg_piece_le D 0
  have hRQ : R ≤ Q := vImg_mono D hPi10
  have hPA : P ≤ A := hPi01
  have hRP : R ≤ P := by rw [hR']; exact Submodule.map_mono hV10

  have h1 : Module.length 𝕎 (↥A ⧸ Submodule.comap A.subtype Q) = 1 := by
    rw [hQ, hA]; exact length_piece_quot_vImg_eq_one D γ hγ 0

  have h2 : Module.length 𝕎 (↥P ⧸ Submodule.comap P.subtype R) = 1 := by
    rw [hR', hP, length_quot_map_eq D.varpi hPi _ _ hV10]
    exact h10 ▸ length_piece_quot_vImg_eq_one D γ hγ 1

  have h3 : Module.length 𝕎 (↥Q ⧸ Submodule.comap Q.subtype R) =
      Module.length 𝕎 (↥(D.piece 0) ⧸
        Submodule.comap (D.piece 0).subtype ((D.piece 1).map D.varpi)) :=
    length_quot_vImg_eq D γ hγ _ _ hPi10

  have e1 := length_quot_eq_add A Q R hRQ hQA
  have e2 := length_quot_eq_add A P R hRP hPA
  rw [h1, h3] at e1
  rw [h2] at e2
  have := e1.symm.trans e2
  rw [add_comm (1 : ℕ∞)] at this
  exact (ENat.add_left_injective_of_ne_top WithTop.one_ne_top this).symm

end Ws23PiColength

namespace Ws23PiColength

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [CharP K p] {j : Zp2 p →+* K}

local notation "𝕎" => WittVector p K

open CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData

theorem map_varpi_map_varpi (D : GradedCartierModuleData p K j) (S : Submodule 𝕎 D.M) :
    (S.map D.varpi).map D.varpi = S.map ((p : 𝕎) • (LinearMap.id : D.M →ₗ[𝕎] D.M)) := by
  rw [← Submodule.map_comp]
  congr 1
  ext x
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply, D.varpi_varpi x]
  rw [Nat.cast_smul_eq_nsmul]

theorem length_piece_quot_varpi_varpi (D : GradedCartierModuleData p K j)
    (hPi : Function.Injective D.varpi) (i k : Fin 2) (hik : i + 1 = k) (hki : k + 1 = i) :
    Module.length 𝕎 (↥(D.piece i) ⧸
        Submodule.comap (D.piece i).subtype (((D.piece i).map D.varpi).map D.varpi)) =
      Module.length 𝕎 (↥(D.piece k) ⧸
          Submodule.comap (D.piece k).subtype ((D.piece i).map D.varpi)) +
        Module.length 𝕎 (↥(D.piece i) ⧸
          Submodule.comap (D.piece i).subtype ((D.piece k).map D.varpi)) := by
  have hik' : (D.piece i).map D.varpi ≤ D.piece k :=
    Submodule.map_le_iff_le_comap.mpr fun x hx => hik ▸ D.varpi_mem i x hx
  have hki' : (D.piece k).map D.varpi ≤ D.piece i :=
    Submodule.map_le_iff_le_comap.mpr fun x hx => hki ▸ D.varpi_mem k x hx
  rw [length_quot_eq_add (D.piece i) ((D.piece k).map D.varpi) (((D.piece i).map D.varpi).map D.varpi)
    (Submodule.map_mono hik') hki', length_quot_map_eq D.varpi hPi _ _ hik']

end Ws23PiColength

namespace Ws23PiColength

theorem length_quotient_range_eq_add {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (P₀ P₁ : Submodule R M) (hP : IsCompl P₀ P₁) (f : M →ₗ[R] M)
    (h₀ : Submodule.map f P₀ ≤ P₀) (h₁ : Submodule.map f P₁ ≤ P₁) :
    Module.length R (M ⧸ LinearMap.range f) =
      Module.length R (↥P₀ ⧸ Submodule.comap P₀.subtype (Submodule.map f P₀)) +
        Module.length R (↥P₁ ⧸ Submodule.comap P₁.subtype (Submodule.map f P₁)) := by
  classical
  set N₀ : Submodule R P₀ := Submodule.comap P₀.subtype (Submodule.map f P₀) with hN₀
  set N₁ : Submodule R P₁ := Submodule.comap P₁.subtype (Submodule.map f P₁) with hN₁
  let g : M →ₗ[R] (↥P₀ ⧸ N₀) × (↥P₁ ⧸ N₁) :=
    LinearMap.prod (N₀.mkQ ∘ₗ Submodule.projectionOnto P₀ P₁ hP) (N₁.mkQ ∘ₗ Submodule.projectionOnto P₁ P₀ hP.symm)
  have hg_apply : ∀ x, g x = (N₀.mkQ (Submodule.projectionOnto P₀ P₁ hP x),
      N₁.mkQ (Submodule.projectionOnto P₁ P₀ hP.symm x)) := fun x => rfl
  have hsurj : Function.Surjective g := by
    rintro ⟨a, b⟩
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective N₀ a
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective N₁ b
    refine ⟨(x : M) + (y : M), ?_⟩
    simp only [hg_apply, map_add, Submodule.projectionOnto_apply_left, Submodule.projectionOnto_apply_right,
      add_zero, zero_add]
  have hker : LinearMap.ker g = LinearMap.range f := by
    ext m
    rw [LinearMap.mem_ker, hg_apply, Prod.mk_eq_zero, Submodule.mkQ_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_eq_zero]
    constructor
    · rintro ⟨hm₀, hm₁⟩
      have hx : m = (Submodule.projectionOnto P₀ P₁ hP m : M) + (Submodule.projectionOnto P₁ P₀ hP.symm m : M) := by
        have := Submodule.projection_add_projection_eq_self hP m
        rw [Submodule.projection_apply, Submodule.projection_apply] at this
        exact this.symm
      rw [hx]
      have h0 : ((Submodule.projectionOnto P₀ P₁ hP m : ↥P₀) : M) ∈ LinearMap.range f :=
        LinearMap.map_le_range (Submodule.mem_comap.mp hm₀)
      have h1 : ((Submodule.projectionOnto P₁ P₀ hP.symm m : ↥P₁) : M) ∈ LinearMap.range f :=
        LinearMap.map_le_range (Submodule.mem_comap.mp hm₁)
      exact Submodule.add_mem _ h0 h1
    · rintro ⟨q, rfl⟩
      have hq : q ∈ P₀ ⊔ P₁ := by rw [hP.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨q₀, hq₀, q₁, hq₁, rfl⟩ := Submodule.mem_sup.mp hq
      have hf₀ : f q₀ ∈ P₀ := h₀ (Submodule.mem_map_of_mem hq₀)
      have hf₁ : f q₁ ∈ P₁ := h₁ (Submodule.mem_map_of_mem hq₁)
      set a : ↥P₀ := ⟨f q₀, hf₀⟩ with ha
      set b : ↥P₁ := ⟨f q₁, hf₁⟩ with hb
      have hab : f (q₀ + q₁) = (a : M) + (b : M) := by rw [map_add]
      rw [hab, map_add, map_add, Submodule.projectionOnto_apply_left, Submodule.projectionOnto_apply_right,
        Submodule.projectionOnto_apply_right, Submodule.projectionOnto_apply_left, add_zero, zero_add]
      exact ⟨Submodule.mem_comap.mpr (Submodule.mem_map_of_mem hq₀),
        Submodule.mem_comap.mpr (Submodule.mem_map_of_mem hq₁)⟩
  have e : (M ⧸ LinearMap.range f) ≃ₗ[R] (↥P₀ ⧸ N₀) × (↥P₁ ⧸ N₁) :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans (g.quotKerEquivOfSurjective hsurj)
  rw [e.length_eq, Module.length_prod]

theorem enat_eq_one_of_four (a : ℕ∞) (h : a + a + (a + a) = 4) : a = 1 := by
  induction a using ENat.recTopCoe with
  | top => exact absurd h (by simp)
  | coe n =>
    have : n + n + (n + n) = 4 := by exact_mod_cast h
    exact_mod_cast (show n = 1 by omega)

end Ws23PiColength

open Ws23PiColength MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld.GradedCartierModuleData in
theorem solution
    (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] [PerfectRing K p]
    (j : Zp2 p →+* K) (Y : FormalODModule p K) (hY : Y.IsSpecial j) (hY4 : Y.HasHeight 4)
    (i : Fin 2) :
    Submodule.map Y.varpiLinear (Y.gradedSubmodule j (i : ℕ)) ≤ Y.gradedSubmodule j ((i + 1 : Fin 2) : ℕ) ∧
    Module.length (WittVector p K)
        (↥(Y.gradedSubmodule j ((i + 1 : Fin 2) : ℕ)) ⧸
          Submodule.comap (Y.gradedSubmodule j ((i + 1 : Fin 2) : ℕ)).subtype
            (Submodule.map Y.varpiLinear (Y.gradedSubmodule j (i : ℕ)))) = 1 := by
  classical

  have hc : IsCompl (Y.gradedPiece j 0) (Y.gradedPiece j 1) :=
    CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p j
      (by rw [CharP.cast_eq_zero]; exact IsNilpotent.zero) Y
  set D : GradedCartierModuleData p K j := Y.toGradedCartierModuleData j hc with hD

  obtain ⟨γ, hγ⟩ := CerednikDrinfeld.FormalODModule.exists_isHomogeneousVBasis_of_isSpecial_field p j Y hY
  have hγD : D.IsHomogeneousVBasis γ :=
    (CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p j Y γ hγ hc).1

  set ψ : Y.F.Hom Y.F := (Y.isLawHom_act (p : Zp2 p)).toHom with hψdef
  have hψ : ψ.toPowerSeries = Y.act (p : Zp2 p) := rfl
  have hfin : Module.Finite K (MvPowerSeries (Fin 2) K ⧸ Ideal.span (Set.range ψ.toPowerSeries)) := by
    rw [hψ]; exact hY4.1
  have hdeg : Module.finrank K (MvPowerSeries (Fin 2) K ⧸ Ideal.span (Set.range ψ.toPowerSeries)) = p ^ 4 := by
    have := hY4.2.2 K (RingHom.id K)
    rwa [Series.map_ringHom_id, ← hψ] at this
  have htot := length_quotient_range_mapLinear_eq_of_finrank_eq_pow p Y.F Y.F ψ 4 hdeg
  have hinjp : Function.Injective (mapLinear (p := p) ψ) := by
    intro a b hab
    exact map_injective_of_finite_quotient p Y.F Y.F ψ hfin (by simpa only [mapLinear_apply] using hab)
  have hpsiPi : ∀ f : CartierModule p Y.F, mapLinear (p := p) ψ f = D.varpi (D.varpi f) := by
    intro f
    show map ψ f = endAct Y.varpiEnd (endAct Y.varpiEnd f)
    have h1 : map (p := p) ψ f = endAct (p := p) (Y.actRingHom (p : Zp2 p)) f := rfl
    rw [h1, ← FormalODModule.varpiEnd_mul_varpiEnd, map_mul]
    rfl
  have hpsiPi2 : mapLinear (p := p) ψ = D.varpi ∘ₗ D.varpi := LinearMap.ext hpsiPi

  have hPi : Function.Injective D.varpi := by
    intro a b hab
    apply hinjp
    rw [hpsiPi, hpsiPi, hab]

  have hPiPi : ∀ k : Fin 2, Submodule.map (D.varpi ∘ₗ D.varpi) (D.piece k) ≤ D.piece k := by
    intro k
    have hk : k + 1 + 1 = k := by fin_cases k <;> rfl
    rintro _ ⟨x, hx, rfl⟩
    have h1 : D.varpi x ∈ D.piece (k + 1) := D.varpi_mem k x hx
    have h2 : D.varpi (D.varpi x) ∈ D.piece (k + 1 + 1) := D.varpi_mem (k + 1) _ h1
    rw [hk] at h2
    exact h2
  have hsplit := length_quotient_range_eq_add (D.piece 0) (D.piece 1) D.isCompl_piece (D.varpi ∘ₗ D.varpi)
    (hPiPi 0) (hPiPi 1)
  have h4 : Module.length (WittVector p K) (D.M ⧸ LinearMap.range (D.varpi ∘ₗ D.varpi)) = 4 := by
    rw [← hpsiPi2]; exact htot
  rw [h4, Submodule.map_comp, Submodule.map_comp] at hsplit

  have h01 : (0 : Fin 2) + 1 = 1 := rfl
  have h10 : (1 : Fin 2) + 1 = 0 := rfl
  have hflag0 := length_piece_quot_varpi_varpi D hPi 0 1 h01 h10
  have hflag1 := length_piece_quot_varpi_varpi D hPi 1 0 h10 h01
  have hbal := length_piece_quot_varpi_balance D γ hγD hPi
  rw [hflag0, hflag1, hbal] at hsplit

  have ha : Module.length (WittVector p K) (↥(D.piece 0) ⧸
      Submodule.comap (D.piece 0).subtype ((D.piece 1).map D.varpi)) = 1 :=
    enat_eq_one_of_four _ hsplit.symm
  have hb : Module.length (WittVector p K) (↥(D.piece 1) ⧸
      Submodule.comap (D.piece 1).subtype ((D.piece 0).map D.varpi)) = 1 := hbal.trans ha

  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact D.varpi_mem i x hx
  fin_cases i
  · exact hb
  · exact ha

end S_CerednikDrinfeld_FormalODModule_length_gradedSubmodule_quotient_map_varpiLinear_eq_one_of_isSpecial_of_hasHeight
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_length_gradedSubmodule_quotient_map_varpiLinear_eq_one_of_isSpecial_of_hasHeight (solution)
