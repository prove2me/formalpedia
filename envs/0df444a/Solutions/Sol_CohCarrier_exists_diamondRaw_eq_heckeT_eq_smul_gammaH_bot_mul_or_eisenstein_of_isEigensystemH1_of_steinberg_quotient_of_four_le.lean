-- Prove2me | solution 1 for CohCarrier.exists_diamondRaw_eq_heckeT_eq_smul_gammaH_bot_mul_or_eisenstein_of_isEigensystemH1_of_steinberg_quotient_of_four_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/f98f9be2-cafa-543b-83b0-1dde0cdfc4e1

import Mathlib
import Definitions.Def_Gamma0CoeffCohomologyEigen
import Definitions.Def_CuspidalType_IsCuspidalOfType
import Definitions.Def_CohCarrier_Level
import Definitions.Def_GroupCohomology_TransferHecke
import Definitions.Def_GroupCohomology_DClassCoeff
import Theorems.Thm_HeckeEis_exists_ne_zero_map_conjHom_eq_and_heckeH1_gammaH_bot_eq_smul_of_isEigensystemH1
import Theorems.Thm_CuspidalType_eq_zero_of_forall_specialLinearGroup_apply_eq_of_steinberg_quotient
import Theorems.Thm_HeckeCohomology_exists_eigenvector_H1_of_eigenvector_H1_of_shortExact_gammaH
import Theorems.Thm_HeckeCohomology_exists_eigenvector_H1_or_forall_eq_of_eigenvector_H1_of_shortExact
import Theorems.Thm_HeckeCohomology_heckeInvD_sub_card_smul
import Theorems.Thm_CohCarrier_index_GammaHUpper_of_prime
import Theorems.Thm_CohCarrier_injective_iDeg_one_of_isUnit_relIndex
import Theorems.Thm_CohCarrier_iDeg_diamondRaw_comm
import Theorems.Thm_CohCarrier_iDeg_heckeT_comm_of_coprime
import Theorems.Thm_HeckeCohomology_exists_shapiro_ind_ker_unitsMap_bijective_linear_and_conjHom_eq_diamondRaw_and_heckeH1_eq_heckeT
import Theorems.Thm_HeckeCohomology_commute_of_forall_eq_heckeH1_cTop_or_eq_heckeH1_conjHom_of_forall_rep_eq_monoidHom_submonoid
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_exists_diamondRaw_eq_heckeT_eq_smul_gammaH_bot_mul_or_eisenstein_of_isEigensystemH1_of_steinberg_quotient_of_four_le

set_option autoImplicit false

namespace RepSES

open CategoryTheory

variable {k G : Type} [CommRing k] [Group G]
variable {N₁ N₂ N₃ : Type} [AddCommGroup N₁] [Module k N₁] [AddCommGroup N₂] [Module k N₂]
  [AddCommGroup N₃] [Module k N₃]
variable (ρ₁ : Representation k G N₁) (ρ₂ : Representation k G N₂) (ρ₃ : Representation k G N₃)

noncomputable def homOf (f : N₁ →ₗ[k] N₂) (hf : ∀ g : G, f ∘ₗ ρ₁ g = ρ₂ g ∘ₗ f) : Rep.of ρ₁ ⟶ Rep.of ρ₂ :=
  Rep.ofHom ⟨f, fun g => hf g⟩

@[scoped simp] theorem homOf_hom_apply (f : N₁ →ₗ[k] N₂) (hf : ∀ g : G, f ∘ₗ ρ₁ g = ρ₂ g ∘ₗ f) (x : N₁) :
    (homOf ρ₁ ρ₂ f hf).hom x = f x := rfl

noncomputable def ses (f : N₁ →ₗ[k] N₂) (hf : ∀ g : G, f ∘ₗ ρ₁ g = ρ₂ g ∘ₗ f)
    (g : N₂ →ₗ[k] N₃) (hg : ∀ γ : G, g ∘ₗ ρ₂ γ = ρ₃ γ ∘ₗ g) (hfg : ∀ x, g (f x) = 0) :
    ShortComplex (Rep k G) where
  X₁ := Rep.of ρ₁
  X₂ := Rep.of ρ₂
  X₃ := Rep.of ρ₃
  f := homOf ρ₁ ρ₂ f hf
  g := homOf ρ₂ ρ₃ g hg
  zero := by ext x; exact hfg x

theorem ses_shortExact (f : N₁ →ₗ[k] N₂) (hf : ∀ g : G, f ∘ₗ ρ₁ g = ρ₂ g ∘ₗ f)
    (g : N₂ →ₗ[k] N₃) (hg : ∀ γ : G, g ∘ₗ ρ₂ γ = ρ₃ γ ∘ₗ g) (hfg : ∀ x, g (f x) = 0)
    (hfinj : Function.Injective f) (hgsurj : Function.Surjective g) (hex : ∀ y, g y = 0 → ∃ x, f x = y) :
    (ses ρ₁ ρ₂ ρ₃ f hf g hg hfg).ShortExact where
  exact :=
    (forget₂ (Rep k G) (ModuleCat k)).reflects_exact_of_faithful _ <|
      (ShortComplex.moduleCat_exact_iff _).2 fun y hy => hex y hy
  mono_f := (Rep.mono_iff_injective _).2 hfinj
  epi_g := (Rep.epi_iff_surjective _).2 hgsurj

end RepSES
p2m_reactivate "P2MW.S_CohCarrier_exists_diamondRaw_eq_heckeT_eq_smul_gammaH_bot_mul_or_eisenstein_of_isEigensystemH1_of_steinberg_quotient_of_four_le.RepSES"

namespace K3aDock

open CategoryTheory CongruenceSubgroup groupCohomology
open scoped MatrixGroups

abbrev Gam (N : ℕ) : Type := ↥(CohCarrier.GammaH N (⊥ : Subgroup (ZMod N)ˣ))

abbrev red0 (N q : ℕ) [Fact q.Prime] : Gamma0 N →* CuspidalType.GL2 q :=
  (Matrix.SpecialLinearGroup.toGL.comp (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype

abbrev incl (N : ℕ) : ↥(CohCarrier.GammaH N (⊥ : Subgroup (ZMod N)ˣ)) →* ↥(Gamma0 N) :=
  Subgroup.inclusion (CohCarrier.GammaH_le_Gamma0 (M := N) (⊥ : Subgroup (ZMod N)ˣ))

section Beta
variable (N q : ℕ) [NeZero N] [Fact q.Prime] (κ : Type) [Field κ]

variable {W : Type} [AddCommGroup W] [Module κ W]

abbrev pull (ρW : Representation κ (CuspidalType.GL2 q) W) :
    Representation κ ↥(CohCarrier.GammaH N (⊥ : Subgroup (ZMod N)ˣ)) W :=
  (ρW.comp (red0 N q)).comp (incl N)

theorem diagElem_mul_red_cTop (ℓ : ℕ) [NeZero ℓ] (hℓq : ((ℓ : ℕ) : ZMod q) ≠ 0)
    (s : ↥(CohCarrier.GammaHUpper N (⊥ : Subgroup (ZMod N)ˣ) ℓ)) :
    CuspidalType.diagElem q (Units.mk0 ((ℓ : ℕ) : ZMod q) hℓq) *
        red0 N q (incl N ((HeckeCohomology.cTop N ⊥ ℓ s : ↥(⊤ : Subgroup _)) : ↥(CohCarrier.GammaH N ⊥))) =
      red0 N q (incl N (s : ↥(CohCarrier.GammaH N ⊥))) * CuspidalType.diagElem q (Units.mk0 ((ℓ : ℕ) : ZMod q) hℓq) := by
  apply Units.ext
  have hb : (ℓ : ℤ) ∣ ((s : ↥(CohCarrier.GammaH N ⊥)) : SL(2, ℤ)) 0 1 := CohCarrier.dvd_of_mem_GammaHUpper N ⊥ ℓ s
  have hcT : (((HeckeCohomology.cTop N ⊥ ℓ s : ↥(⊤ : Subgroup _)) : ↥(CohCarrier.GammaH N ⊥)) : SL(2, ℤ)) =
      CohCarrier.conjUpperMat ℓ ((s : ↥(CohCarrier.GammaH N ⊥)) : SL(2, ℤ)) hb := rfl

  have hred : ∀ (γ : ↥(CohCarrier.GammaH N (⊥ : Subgroup (ZMod N)ˣ))) (i j : Fin 2),
      ((red0 N q (incl N γ) : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) i j =
        ((((γ : SL(2, ℤ)) i j : ℤ)) : ZMod q) := fun _ _ _ => rfl
  ext i j
  rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, Matrix.mul_apply]
  simp only [Fin.sum_univ_two, hred, hcT, CuspidalType.diagElem_val]
  obtain ⟨b', hb'⟩ := hb
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne ℓ
  fin_cases i <;> fin_cases j <;>
    simp [CohCarrier.conjUpperMat, hb', Int.mul_ediv_cancel_left _ hℓ0, Int.mul_ediv_cancel _ hℓ0, mul_comm]

theorem isTwist_pull_diagElem (ρW : Representation κ (CuspidalType.GL2 q) W) (ℓ : ℕ) [NeZero ℓ]
    (hℓq : ((ℓ : ℕ) : ZMod q) ≠ 0) :
    HeckeCohomology.IsTwist ⊤ (CohCarrier.GammaHUpper N ⊥ ℓ) (HeckeCohomology.cTop N ⊥ ℓ) (Rep.of (pull N q κ ρW))
      (ρW (CuspidalType.diagElem q (Units.mk0 ((ℓ : ℕ) : ZMod q) hℓq))) := by
  intro s w
  change ρW (CuspidalType.diagElem q _) (ρW (red0 N q (incl N _)) w) = ρW (red0 N q (incl N _)) (ρW (CuspidalType.diagElem q _) w)
  rw [← Module.End.mul_apply, ← map_mul, diagElem_mul_red_cTop N q ℓ hℓq s, map_mul, Module.End.mul_apply]

noncomputable abbrev indRep : Representation κ ↥(CohCarrier.GammaH N (⊥ : Subgroup (ZMod N)ˣ)) (CuspidalType.ProjLine q →₀ κ) :=
  pull N q κ (CuspidalType.ind q κ)

noncomputable abbrev stRep : Representation κ ↥(CohCarrier.GammaH N (⊥ : Subgroup (ZMod N)ˣ)) ↥(CuspidalType.steinberg q κ).toSubmodule :=
  pull (W := ↥(CuspidalType.steinberg q κ).toSubmodule) N q κ (CuspidalType.steinbergRep q κ)

noncomputable def trivRep : Representation κ ↥(CohCarrier.GammaH N (⊥ : Subgroup (ZMod N)ˣ)) κ := 1

theorem trivRep_apply (γ : ↥(CohCarrier.GammaH N (⊥ : Subgroup (ZMod N)ˣ))) : trivRep N κ γ = LinearMap.id := rfl

omit [NeZero N] in
theorem coeffSum_ind (g : CuspidalType.GL2 q) (v : CuspidalType.ProjLine q →₀ κ) :
    CuspidalType.coeffSum q κ (CuspidalType.ind q κ g v) = CuspidalType.coeffSum q κ v := by
  rw [CuspidalType.coeffSum, Representation.ofMulActionFinsupp_def, Finsupp.lmapDomain_apply,
    Finsupp.linearCombination_mapDomain]
  rfl

theorem subtype_equivariant (γ : ↥(CohCarrier.GammaH N (⊥ : Subgroup (ZMod N)ˣ))) :
    (CuspidalType.steinberg q κ).toSubmodule.subtype ∘ₗ stRep N q κ γ =
      indRep N q κ γ ∘ₗ (CuspidalType.steinberg q κ).toSubmodule.subtype :=
  LinearMap.ext fun _ => rfl

theorem coeffSum_equivariant (γ : ↥(CohCarrier.GammaH N (⊥ : Subgroup (ZMod N)ˣ))) :
    CuspidalType.coeffSum q κ ∘ₗ indRep N q κ γ = trivRep N κ γ ∘ₗ CuspidalType.coeffSum q κ :=
  LinearMap.ext fun v => coeffSum_ind q κ (red0 N q (incl N γ)) v

noncomputable def ses2 : ShortComplex (Rep κ ↥(CohCarrier.GammaH N (⊥ : Subgroup (ZMod N)ˣ))) :=
  RepSES.ses (k := κ) (G := ↥(CohCarrier.GammaH N (⊥ : Subgroup (ZMod N)ˣ)))
    (N₁ := ↥(CuspidalType.steinberg q κ).toSubmodule) (N₂ := CuspidalType.ProjLine q →₀ κ) (N₃ := κ)
    (stRep N q κ) (indRep N q κ) (trivRep N κ)
    (CuspidalType.steinberg q κ).toSubmodule.subtype (subtype_equivariant N q κ)
    (CuspidalType.coeffSum q κ) (coeffSum_equivariant N q κ)
    (fun x : ↥(CuspidalType.steinberg q κ).toSubmodule => (LinearMap.mem_ker.mp x.2 : CuspidalType.coeffSum q κ x = 0))

omit [NeZero N] in
theorem nonempty_projLine : Nonempty (CuspidalType.ProjLine q) := by
  have h := CuspidalType.card_projLine q
  by_contra hne
  rw [not_nonempty_iff] at hne
  rw [Nat.card_of_isEmpty] at h
  omega

omit [NeZero N] in
theorem coeffSum_surjective : Function.Surjective (CuspidalType.coeffSum q κ) := by
  classical
  intro a
  obtain ⟨P⟩ := nonempty_projLine q
  refine ⟨Finsupp.single P a, ?_⟩
  rw [CuspidalType.coeffSum, Finsupp.linearCombination_single, smul_eq_mul, mul_one]

theorem ses2_shortExact : (ses2 N q κ).ShortExact :=
  RepSES.ses_shortExact _ _ _ _ _ _ _ _ (Submodule.injective_subtype _) (coeffSum_surjective q κ)
    (fun y hy => ⟨⟨y, hy⟩, rfl⟩)

section SES1

variable {V : Type} [AddCommGroup V] [Module κ V]
variable (ρ : Representation κ (CuspidalType.GL2 q) V)
variable (π : ↥(CuspidalType.steinberg q κ).toSubmodule →ₗ[κ] V)
variable (hπ : ∀ g : CuspidalType.GL2 q, ∀ v : ↥(CuspidalType.steinberg q κ).toSubmodule,
  π ⟨CuspidalType.ind q κ g v, (CuspidalType.steinberg q κ).apply_mem_toSubmodule g v.2⟩ = ρ g (π v))
variable (hq1 : (q : κ) + 1 = 0)
variable (hπker : ∀ v : ↥(CuspidalType.steinberg q κ).toSubmodule, π v = 0 ↔ ∃ c : κ, (v : CuspidalType.ProjLine q →₀ κ) = c • CuspidalType.constFun q κ)

noncomputable abbrev vRep : Representation κ ↥(CohCarrier.GammaH N (⊥ : Subgroup (ZMod N)ˣ)) V := pull N q κ ρ

noncomputable def constSt : ↥(CuspidalType.steinberg q κ).toSubmodule :=
  ⟨CuspidalType.constFun q κ, (CuspidalType.constFun_mem_steinberg_iff q κ).2 hq1⟩

omit [NeZero N] in
theorem ind_constFun (g : CuspidalType.GL2 q) : CuspidalType.ind q κ g (CuspidalType.constFun q κ) = CuspidalType.constFun q κ := by
  classical
  rw [Representation.ofMulActionFinsupp_def, Finsupp.lmapDomain_apply]
  ext P
  change (Finsupp.mapDomain (⇑(MulAction.toPerm g : CuspidalType.ProjLine q ≃ CuspidalType.ProjLine q))
    (CuspidalType.constFun q κ)) P = CuspidalType.constFun q κ P
  rw [Finsupp.mapDomain_equiv_apply]
  simp [CuspidalType.constFun]

omit [NeZero N] in
theorem steinbergRep_constSt (g : CuspidalType.GL2 q) : CuspidalType.steinbergRep q κ g (constSt q κ hq1) = constSt q κ hq1 :=
  Subtype.ext (ind_constFun q κ g)

noncomputable def constMap : κ →ₗ[κ] ↥(CuspidalType.steinberg q κ).toSubmodule :=
  LinearMap.toSpanSingleton κ _ (constSt q κ hq1)

theorem constMap_apply (a : κ) : constMap q κ hq1 a = a • constSt q κ hq1 := rfl

theorem constMap_equivariant (γ : ↥(CohCarrier.GammaH N (⊥ : Subgroup (ZMod N)ˣ))) :
    constMap q κ hq1 ∘ₗ trivRep N κ γ = stRep N q κ γ ∘ₗ constMap q κ hq1 := by
  apply LinearMap.ext
  intro a
  change a • constSt q κ hq1 = CuspidalType.steinbergRep q κ (red0 N q (incl N γ)) (a • constSt q κ hq1)
  rw [map_smul, steinbergRep_constSt]

include hπ in
omit [NeZero N] in
theorem pi_equivariant (γ : ↥(CohCarrier.GammaH N (⊥ : Subgroup (ZMod N)ˣ))) :
    π ∘ₗ stRep N q κ γ = vRep N q κ ρ γ ∘ₗ π :=
  LinearMap.ext fun v => hπ (red0 N q (incl N γ)) v

noncomputable def ses1 : ShortComplex (Rep κ ↥(CohCarrier.GammaH N (⊥ : Subgroup (ZMod N)ˣ))) :=
  RepSES.ses (k := κ) (G := ↥(CohCarrier.GammaH N (⊥ : Subgroup (ZMod N)ˣ)))
    (N₁ := κ) (N₂ := ↥(CuspidalType.steinberg q κ).toSubmodule) (N₃ := V)
    (trivRep N κ) (stRep N q κ) (vRep N q κ ρ)
    (constMap q κ hq1) (constMap_equivariant N q κ hq1) π (pi_equivariant N q κ ρ π hπ)
    (fun a => (hπker _).2 ⟨a, rfl⟩)

omit [NeZero N] in
theorem constSt_ne_zero : constSt q κ hq1 ≠ 0 := by
  intro h
  have h1 := congrArg (fun f : ↥(CuspidalType.steinberg q κ).toSubmodule => ((f : CuspidalType.ProjLine q →₀ κ) (Classical.choice (nonempty_projLine q)))) h
  simp [constSt, CuspidalType.constFun] at h1

theorem ses1_shortExact (hπsurj : Function.Surjective π) : (ses1 N q κ ρ π hπ hq1 hπker).ShortExact :=
  RepSES.ses_shortExact _ _ _ _ _ _ _ _
    (by
      intro a b hab
      have h : a • constSt q κ hq1 = b • constSt q κ hq1 := hab
      by_contra hne
      apply constSt_ne_zero q κ hq1
      have h2 : (a - b) • constSt q κ hq1 = 0 := by
        rw [sub_smul a b (constSt q κ hq1), h, sub_self]
      exact (smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hne))
    hπsurj
    (fun y hy => by
      obtain ⟨a, ha⟩ := (hπker y).1 hy
      exact ⟨a, Subtype.ext (by rw [ha]; rfl)⟩)

end SES1
p2m_reactivate "P2MW.S_CohCarrier_exists_diamondRaw_eq_heckeT_eq_smul_gammaH_bot_mul_or_eisenstein_of_isEigensystemH1_of_steinberg_quotient_of_four_le.RepSES"

end Beta
p2m_reactivate "P2MW.S_CohCarrier_exists_diamondRaw_eq_heckeT_eq_smul_gammaH_bot_mul_or_eisenstein_of_isEigensystemH1_of_steinberg_quotient_of_four_le.RepSES"

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

open HeckeCohomology in
theorem heckeInv_one_eq_smul {k : Type} [CommRing k] (N : ℕ) (H : Subgroup (ZMod N)ˣ) (ℓ : ℕ) [NeZero ℓ]
    (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    (A : Rep k ↥(CohCarrier.GammaH N H)) (hA : ∀ γ, A.ρ γ = LinearMap.id)
    (hφ : IsTwist ⊤ (CohCarrier.GammaHUpper N H ℓ) (cTop N H ℓ) A LinearMap.id)
    (z : A.ρ.invariants) :
    heckeInv ⊤ (CohCarrier.GammaHUpper N H ℓ) (cTop N H ℓ) A LinearMap.id hφ z = ((ℓ : k) + 1) • z := by
  have hD : IsDClass N H A := ⟨1, fun γ => by rw [hA γ, MonoidHom.one_apply]; rfl⟩
  have h := heckeInvD_sub_card_smul N H ℓ A hD z
  have hcard : Fintype.card (Quotient (QuotientGroup.rightRel (CohCarrier.GammaHUpper N H ℓ))) = ℓ + 1 := by
    rw [Fintype.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel (CohCarrier.GammaHUpper N H ℓ)),
      ← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card, CohCarrier.index_GammaHUpper_of_prime N H ℓ hℓ hℓN]
  rw [hcard, sub_eq_zero] at h
  change heckeInv ⊤ (CohCarrier.GammaHUpper N H ℓ) (cTop N H ℓ) A LinearMap.id _ z = _ at h
  rw [h, ← Nat.cast_smul_eq_nsmul k, Nat.cast_add, Nat.cast_one]

scoped instance subsingleton_quotient_rightRel_top {Γ : Type} [Group Γ] :
    Subsingleton (Quotient (QuotientGroup.rightRel (⊤ : Subgroup Γ))) :=
  ⟨fun a b => Quotient.inductionOn₂ a b fun x y => Quotient.sound
    (QuotientGroup.rightRel_apply.mpr (Subgroup.mem_top _))⟩

open HeckeCohomology in

theorem heckeInv_top_eq_self {k Γ : Type} [CommRing k] [Group Γ] (S₁ : Subgroup Γ) (c : ↥(⊤ : Subgroup Γ) →* ↥S₁)
    (A : Rep k Γ) (hA : ∀ γ, A.ρ γ = LinearMap.id) (φ : A →ₗ[k] A) (hφid : ∀ a, φ a = a)
    (hφ : IsTwist S₁ ⊤ c A φ) (z : A.ρ.invariants) :
    heckeInv S₁ ⊤ c A φ hφ z = z := by
  apply Subtype.ext
  rw [coe_heckeInv, norm0_apply, Fintype.sum_subsingleton _ (Quotient.mk _ 1), hφid]

  generalize (rep (⊤ : Subgroup Γ) (Quotient.mk _ 1)) = t
  rw [hA t⁻¹]
  rfl

section D1b
variable {k : Type} [CommRing k] (N : ℕ) {V : Type} [AddCommGroup V] [Module k V]

def conjGam (σ : ↥(Gamma0 N)) : Gam N →* Gam N where
  toFun γ := ⟨(σ : SL(2, ℤ))⁻¹ * (γ : SL(2, ℤ)) * (σ : SL(2, ℤ)), by
    have h := CohCarrier.conj_mem_GammaH (M := N) (H := (⊥ : Subgroup (ZMod N)ˣ)) σ⁻¹ γ
    simpa using h⟩
  map_one' := Subtype.ext (by simp)
  map_mul' γ δ := Subtype.ext (by
    simp only [Subgroup.coe_mul]
    group)

@[scoped simp] theorem coe_conjGam (σ : ↥(Gamma0 N)) (γ : Gam N) :
    ((conjGam N σ γ : Gam N) : SL(2, ℤ)) = (σ : SL(2, ℤ))⁻¹ * (γ : SL(2, ℤ)) * (σ : SL(2, ℤ)) := rfl

theorem incl_conjGam (σ : ↥(Gamma0 N)) (γ : Gam N) : incl N (conjGam N σ γ) = σ⁻¹ * incl N γ * σ :=
  Subtype.ext rfl

def conjTop (σ : ↥(Gamma0 N)) : ↥(⊤ : Subgroup (Gam N)) →* ↥(⊤ : Subgroup (Gam N)) where
  toFun s := ⟨conjGam N σ s.1, Subgroup.mem_top _⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

@[scoped simp] theorem coe_conjTop (σ : ↥(Gamma0 N)) (s : ↥(⊤ : Subgroup (Gam N))) :
    ((conjTop N σ s : ↥(⊤ : Subgroup (Gam N))) : Gam N) = conjGam N σ s.1 := rfl

variable (ρ₀ : Representation k ↥(Gamma0 N) V)

noncomputable abbrev A : Rep k (Gam N) := Rep.of (ρ₀.comp (incl N))

theorem A_ρ_apply (γ : Gam N) : (A N ρ₀).ρ γ = ρ₀ (incl N γ) := rfl

theorem isTwist_conjTop (σ : ↥(Gamma0 N)) :
    HeckeCohomology.IsTwist ⊤ ⊤ (conjTop N σ) (A N ρ₀) (ρ₀ σ) := by
  intro s a
  change ρ₀ σ (ρ₀ (incl N (conjGam N σ s.1)) a) = ρ₀ (incl N s.1) (ρ₀ σ a)
  rw [incl_conjGam, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  congr 2
  group

noncomputable def conjAct (σ : ↥(Gamma0 N)) (f : cocycles₁ (A N ρ₀)) : cocycles₁ (A N ρ₀) :=
  ⟨fun γ => ρ₀ σ (f (conjGam N σ γ)), by
    rw [mem_cocycles₁_iff]
    intro γ δ
    have hf := (mem_cocycles₁_iff f).1 f.2 (conjGam N σ γ) (conjGam N σ δ)
    rw [← map_mul] at hf
    change ρ₀ σ (f (conjGam N σ (γ * δ))) = ρ₀ (incl N γ) (ρ₀ σ (f (conjGam N σ δ))) + ρ₀ σ (f (conjGam N σ γ))
    rw [hf, map_add]
    congr 1
    change ρ₀ σ (ρ₀ (incl N (conjGam N σ γ)) _) = _
    rw [incl_conjGam, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    group⟩

theorem conjAct_apply (σ : ↥(Gamma0 N)) (f : cocycles₁ (A N ρ₀)) (γ : Gam N) :
    conjAct N ρ₀ σ f γ = ρ₀ σ (f (conjGam N σ γ)) := rfl

theorem heckeZ1_conjTop_apply (σ : ↥(Gamma0 N)) (f : cocycles₁ (A N ρ₀)) (γ : Gam N) :
    HeckeCohomology.heckeZ1 ⊤ ⊤ (conjTop N σ) (A N ρ₀) (ρ₀ σ) (isTwist_conjTop N ρ₀ σ) f γ =
      ρ₀ (incl N (HeckeCohomology.rep (⊤ : Subgroup (Gam N)) (HeckeCohomology.cls ⊤ γ)))⁻¹
        (ρ₀ σ (f (conjGam N σ (HeckeCohomology.slip (⊤ : Subgroup (Gam N)) (HeckeCohomology.cls ⊤ γ) γ).1))) := by
  letI := Subgroup.fintypeQuotientOfFiniteIndex (H := (⊤ : Subgroup (Gam N)))
  rw [HeckeCohomology.heckeZ1_apply]
  rw [Fintype.sum_subsingleton _ (HeckeCohomology.cls (⊤ : Subgroup (Gam N)) γ)]
  rfl

theorem conjGam_mul_apply (a b : ↥(Gamma0 N)) (γ : Gam N) : conjGam N (a * b) γ = conjGam N b (conjGam N a γ) := by
  apply Subtype.ext
  simp only [coe_conjGam, Subgroup.coe_mul, mul_inv_rev]
  group

theorem conjAct_mul (a b : ↥(Gamma0 N)) (f : cocycles₁ (A N ρ₀)) :
    conjAct N ρ₀ (a * b) f = conjAct N ρ₀ a (conjAct N ρ₀ b f) := by
  apply DFunLike.ext
  intro γ
  rw [conjAct_apply, conjAct_apply, conjAct_apply, conjGam_mul_apply, map_mul, Module.End.mul_apply]

theorem conjAct_incl_sub_mem_coboundaries (u : Gam N) (f : cocycles₁ (A N ρ₀)) :
    (⇑(conjAct N ρ₀ (incl N u) f) - ⇑f) ∈ coboundaries₁ (A N ρ₀) := by
  refine ⟨f u, funext fun γ => ?_⟩
  have hγ : conjGam N (incl N u) γ = u⁻¹ * γ * u := Subtype.ext rfl
  have hf := (mem_cocycles₁_iff f).1 f.2

  have e1 : ρ₀ (incl N u) (ρ₀ (incl N (u⁻¹ * γ)) (f u)) = ρ₀ (incl N γ) (f u) := by
    rw [← Module.End.mul_apply, ← map_mul, ← map_mul, mul_inv_cancel_left]
  have e2 : ρ₀ (incl N u) (ρ₀ (incl N u⁻¹) (f γ)) = f γ := by
    rw [← Module.End.mul_apply, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one, Module.End.one_apply]
  have e3 : ρ₀ (incl N u) (f u⁻¹) = - f u := cocycles₁_map_inv f u
  rw [d₀₁_hom_apply, Pi.sub_apply, conjAct_apply, hγ, hf, hf]
  simp only [MonoidHom.coe_comp, Function.comp_apply, map_add]
  rw [e1, e2, e3]
  abel

theorem H1π_conjAct_incl (u : Gam N) (f : cocycles₁ (A N ρ₀)) :
    H1π (A N ρ₀) (conjAct N ρ₀ (incl N u) f) = H1π (A N ρ₀) f :=
  (H1π_eq_iff _ _).mpr (conjAct_incl_sub_mem_coboundaries N ρ₀ u f)

theorem slip_top (q : Quotient (QuotientGroup.rightRel (⊤ : Subgroup (Gam N)))) (γ : Gam N) :
    ((HeckeCohomology.slip (⊤ : Subgroup (Gam N)) q γ).1 : Gam N) =
      HeckeCohomology.rep (⊤ : Subgroup (Gam N)) q * γ * (HeckeCohomology.rep (⊤ : Subgroup (Gam N)) q)⁻¹ := by
  have hq' : HeckeCohomology.cls (⊤ : Subgroup (Gam N)) (HeckeCohomology.rep (⊤ : Subgroup (Gam N)) q * γ) = q :=
    Subsingleton.elim _ _
  show HeckeCohomology.rep (⊤ : Subgroup (Gam N)) q * γ *
      (HeckeCohomology.rep (⊤ : Subgroup (Gam N)) (HeckeCohomology.cls (⊤ : Subgroup (Gam N)) (HeckeCohomology.rep (⊤ : Subgroup (Gam N)) q * γ)))⁻¹ = _
  rw [hq']

theorem rep_cls_eq (γ : Gam N) :
    HeckeCohomology.rep (⊤ : Subgroup (Gam N)) (HeckeCohomology.cls ⊤ γ) = HeckeCohomology.rep (⊤ : Subgroup (Gam N)) (HeckeCohomology.cls ⊤ (1 : Gam N)) := by
  rw [Subsingleton.elim (HeckeCohomology.cls (⊤ : Subgroup (Gam N)) γ) (HeckeCohomology.cls ⊤ (1 : Gam N))]

theorem conjGam_conj (σ : ↥(Gamma0 N)) (t γ : Gam N) :
    conjGam N σ (t * γ * t⁻¹) = conjGam N ((incl N t)⁻¹ * σ) γ := by
  apply Subtype.ext
  simp only [coe_conjGam, Subgroup.coe_mul, InvMemClass.coe_inv, mul_inv_rev, inv_inv, Subgroup.coe_inclusion, mul_assoc]

theorem heckeZ1_conjTop_eq (σ : ↥(Gamma0 N)) (f : cocycles₁ (A N ρ₀)) :
    HeckeCohomology.heckeZ1 ⊤ ⊤ (conjTop N σ) (A N ρ₀) (ρ₀ σ) (isTwist_conjTop N ρ₀ σ) f =
      conjAct N ρ₀ ((incl N (HeckeCohomology.rep (⊤ : Subgroup (Gam N)) (HeckeCohomology.cls ⊤ (1 : Gam N))))⁻¹ * σ) f := by
  apply DFunLike.ext
  intro γ
  rw [heckeZ1_conjTop_apply, conjAct_apply, slip_top, rep_cls_eq, conjGam_conj, map_mul ρ₀, Module.End.mul_apply, ← map_inv]

theorem heckeH1_conjTop (σ : ↥(Gamma0 N)) (f : cocycles₁ (A N ρ₀)) :
    HeckeCohomology.heckeH1 ⊤ ⊤ (conjTop N σ) (A N ρ₀) (ρ₀ σ) (isTwist_conjTop N ρ₀ σ) (H1π (A N ρ₀) f) =
      H1π (A N ρ₀) (conjAct N ρ₀ σ f) := by
  rw [HeckeCohomology.heckeH1_H1π, heckeZ1_conjTop_eq, ← map_inv, conjAct_mul, H1π_conjAct_incl]

theorem conjGam_inv_apply (τ : ↥(Gamma0 N)) (γ : Gam N) :
    conjGam N τ⁻¹ γ = CohCarrier.conjHom N (⊥ : Subgroup (ZMod N)ˣ) τ γ := by
  apply Subtype.ext
  simp only [coe_conjGam, InvMemClass.coe_inv, inv_inv]
  rfl

noncomputable def cHom (τ : ↥(Gamma0 N)) :
    Rep.res (CohCarrier.conjHom N (⊥ : Subgroup (ZMod N)ˣ) τ) (A N ρ₀) ⟶ A N ρ₀ :=
  Rep.ofHom
    { toLinearMap := ρ₀ τ⁻¹
      isIntertwining' := fun g => LinearMap.ext fun v => by
        have h := isTwist_conjTop N ρ₀ τ⁻¹ ⟨g, Subgroup.mem_top g⟩ v
        rw [coe_conjTop, conjGam_inv_apply] at h
        exact h }

theorem cHom_apply (τ : ↥(Gamma0 N)) (v : V) : (cHom N ρ₀ τ).hom v = ρ₀ τ⁻¹ v := rfl

theorem map_conjHom_H1π (τ : ↥(Gamma0 N))
    (c : Rep.res (CohCarrier.conjHom N (⊥ : Subgroup (ZMod N)ˣ) τ) (A N ρ₀) ⟶ A N ρ₀)
    (hc : ∀ v : V, c.hom v = ρ₀ τ⁻¹ v) (f : cocycles₁ (A N ρ₀)) :
    groupCohomology.map (CohCarrier.conjHom N (⊥ : Subgroup (ZMod N)ˣ) τ) c 1 (H1π (A N ρ₀) f) =
      H1π (A N ρ₀) (conjAct N ρ₀ τ⁻¹ f) := by
  rw [groupCohomology.H1π_comp_map_apply]
  congr 1
  apply DFunLike.ext
  intro γ
  rw [groupCohomology.coe_mapCocycles₁, conjAct_apply, conjGam_inv_apply, ← hc]
  rfl

theorem map_conjHom_eq_heckeH1 (τ : ↥(Gamma0 N))
    (c : Rep.res (CohCarrier.conjHom N (⊥ : Subgroup (ZMod N)ˣ) τ) (A N ρ₀) ⟶ A N ρ₀)
    (hc : ∀ v : V, c.hom v = ρ₀ τ⁻¹ v) (y : groupCohomology.H1 (A N ρ₀)) :
    groupCohomology.map (CohCarrier.conjHom N (⊥ : Subgroup (ZMod N)ˣ) τ) c 1 y =
      HeckeCohomology.heckeH1 ⊤ ⊤ (conjTop N τ⁻¹) (A N ρ₀) (ρ₀ τ⁻¹) (isTwist_conjTop N ρ₀ τ⁻¹) y := by
  induction y using groupCohomology.H1_induction_on with
  | h f => rw [map_conjHom_H1π N ρ₀ τ c hc, heckeH1_conjTop]

theorem heckeH1_conjTop_eq_self_of_forall_map_conjHom (y : groupCohomology.H1 (A N ρ₀))
    (hy : ∀ (σ : ↥(Gamma0 N))
      (c : Rep.res (CohCarrier.conjHom N (⊥ : Subgroup (ZMod N)ˣ) σ) (A N ρ₀) ⟶ A N ρ₀),
      (∀ v : V, c.hom v = ρ₀ σ⁻¹ v) → groupCohomology.map (CohCarrier.conjHom N (⊥ : Subgroup (ZMod N)ˣ) σ) c 1 y = y)
    (σ : ↥(Gamma0 N)) :
    HeckeCohomology.heckeH1 ⊤ ⊤ (conjTop N σ) (A N ρ₀) (ρ₀ σ) (isTwist_conjTop N ρ₀ σ) y = y := by
  have h := hy σ⁻¹ (cHom N ρ₀ σ⁻¹) (fun v => rfl)
  rw [map_conjHom_eq_heckeH1 N ρ₀ σ⁻¹ (cHom N ρ₀ σ⁻¹) (fun v => rfl)] at h

  revert h
  rw [inv_inv]
  exact id

theorem map_conjHom_eq_self_of_forall_heckeH1_conjTop (y : groupCohomology.H1 (A N ρ₀))
    (hy : ∀ σ : ↥(Gamma0 N), HeckeCohomology.heckeH1 ⊤ ⊤ (conjTop N σ) (A N ρ₀) (ρ₀ σ) (isTwist_conjTop N ρ₀ σ) y = y)
    (τ : ↥(Gamma0 N)) (c : Rep.res (CohCarrier.conjHom N (⊥ : Subgroup (ZMod N)ˣ) τ) (A N ρ₀) ⟶ A N ρ₀)
    (hc : ∀ v : V, c.hom v = ρ₀ τ⁻¹ v) :
    groupCohomology.map (CohCarrier.conjHom N (⊥ : Subgroup (ZMod N)ˣ) τ) c 1 y = y := by
  rw [map_conjHom_eq_heckeH1 N ρ₀ τ c hc, hy]

end D1b
p2m_reactivate "P2MW.S_CohCarrier_exists_diamondRaw_eq_heckeT_eq_smul_gammaH_bot_mul_or_eisenstein_of_isEigensystemH1_of_steinberg_quotient_of_four_le.RepSES"

section Guard
variable (q : ℕ) [Fact q.Prime] (κ : Type) [Field κ]

omit [Fact q.Prime] in

theorem cast_pred_ne_zero (hq : 1 ≤ q) (hq1 : (q : κ) + 1 = 0) (h2 : (2 : κ) ≠ 0) : ((q - 1 : ℕ) : κ) ≠ 0 := by
  intro h
  rw [Nat.cast_sub hq, Nat.cast_one, sub_eq_zero] at h
  apply h2
  have hq' : (q : κ) = -1 := eq_neg_of_add_eq_zero_left hq1
  rw [hq'] at h

  calc (2 : κ) = 1 + 1 := by norm_num
    _ = 1 + (-1) := by rw [h]
    _ = 0 := add_neg_cancel 1

theorem not_ringChar_dvd_pred (hq1 : (q : κ) + 1 = 0) (h2 : (2 : κ) ≠ 0) : ¬ (ringChar κ ∣ q - 1) := by
  intro h
  have hq : 1 ≤ q := (Fact.out : q.Prime).one_lt.le
  exact cast_pred_ne_zero q κ hq hq1 h2 ((ringChar.spec κ (q - 1)).mpr h)

end Guard
p2m_reactivate "P2MW.S_CohCarrier_exists_diamondRaw_eq_heckeT_eq_smul_gammaH_bot_mul_or_eisenstein_of_isEigensystemH1_of_steinberg_quotient_of_four_le.RepSES"

section Core
variable (N q : ℕ) [NeZero N] [Fact q.Prime] (κ : Type) [Field κ]

section Family

variable (S₀ : Set ℕ)

abbrev GoodIdx : Type := {ℓ : ℕ // ℓ.Prime ∧ ¬ ℓ ∣ N ∧ ℓ ∉ insert q S₀}

abbrev Idx : Type := GoodIdx N q S₀ ⊕ ↥(Gamma0 N)

abbrev S₁ : Idx N q S₀ → Subgroup (Gam N) := fun _ => ⊤

abbrev S₂ : Idx N q S₀ → Subgroup (Gam N) :=
  Sum.elim (fun i => CohCarrier.GammaHUpper N (⊥ : Subgroup (ZMod N)ˣ) i.1) (fun _ => ⊤)

noncomputable def cfam : ∀ i : Idx N q S₀, ↥(S₂ N q S₀ i) →* ↥(S₁ N q S₀ i)
  | Sum.inl i => HeckeCohomology.cTop N (⊥ : Subgroup (ZMod N)ˣ) i.1
  | Sum.inr σ => conjTop N σ

omit [NeZero N] in
theorem good_ne_zero (i : GoodIdx N q S₀) : ((i.1 : ℕ) : ZMod q) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  have hq : q.Prime := Fact.out
  have hiq : i.1 = q := ((Nat.prime_dvd_prime_iff_eq hq i.2.1).mp h).symm
  exact i.2.2.2 (by rw [hiq]; exact Set.mem_insert q S₀)

scoped instance S₂_finiteIndex : ∀ i : Idx N q S₀, (S₂ N q S₀ i).FiniteIndex
  | Sum.inl i => by
      haveI : NeZero (i.1 : ℕ) := ⟨i.2.1.ne_zero⟩
      change (CohCarrier.GammaHUpper N (⊥ : Subgroup (ZMod N)ˣ) i.1).FiniteIndex
      infer_instance
  | Sum.inr _ => by
      change (⊤ : Subgroup (Gam N)).FiniteIndex
      infer_instance

variable {W : Type} [AddCommGroup W] [Module κ W]

noncomputable def φfam (ρW : Representation κ (CuspidalType.GL2 q) W) : Idx N q S₀ → (W →ₗ[κ] W)
  | Sum.inl i => if h : (((i.1 : ℕ) : ZMod q) ≠ 0) then ρW (CuspidalType.diagElem q (Units.mk0 ((i.1 : ℕ) : ZMod q) h)) else LinearMap.id
  | Sum.inr σ => ρW (red0 N q σ)

omit [NeZero N] in
theorem φfam_inl (ρW : Representation κ (CuspidalType.GL2 q) W) (i : GoodIdx N q S₀) :
    φfam N q κ S₀ ρW (Sum.inl i) = ρW (CuspidalType.diagElem q (Units.mk0 ((i.1 : ℕ) : ZMod q) (good_ne_zero N q S₀ i))) := by
  change (if h : (((i.1 : ℕ) : ZMod q) ≠ 0) then ρW (CuspidalType.diagElem q (Units.mk0 ((i.1 : ℕ) : ZMod q) h)) else LinearMap.id) = _
  rw [dif_pos (good_ne_zero N q S₀ i)]

omit [NeZero N] in
theorem φfam_inr (ρW : Representation κ (CuspidalType.GL2 q) W) (σ : ↥(Gamma0 N)) :
    φfam N q κ S₀ ρW (Sum.inr σ) = ρW (red0 N q σ) := rfl

noncomputable abbrev φSt : Idx N q S₀ → (↥(CuspidalType.steinberg q κ).toSubmodule →ₗ[κ] ↥(CuspidalType.steinberg q κ).toSubmodule) :=
  φfam (W := ↥(CuspidalType.steinberg q κ).toSubmodule) N q κ S₀ (CuspidalType.steinbergRep q κ)

omit [NeZero N] in
theorem φSt_inl (i : GoodIdx N q S₀) :
    φSt N q κ S₀ (Sum.inl i) = CuspidalType.steinbergRep q κ (CuspidalType.diagElem q (Units.mk0 ((i.1 : ℕ) : ZMod q) (good_ne_zero N q S₀ i))) :=
  φfam_inl (W := ↥(CuspidalType.steinberg q κ).toSubmodule) N q κ S₀ (CuspidalType.steinbergRep q κ) i

omit [NeZero N] in
theorem φSt_inr (σ : ↥(Gamma0 N)) : φSt N q κ S₀ (Sum.inr σ) = CuspidalType.steinbergRep q κ (red0 N q σ) := rfl

noncomputable abbrev XSt : Rep κ (Gam N) := Rep.of (X := ↥(CuspidalType.steinberg q κ).toSubmodule) (stRep N q κ)
noncomputable abbrev XInd : Rep κ (Gam N) := Rep.of (indRep N q κ)
noncomputable abbrev Xκ : Rep κ (Gam N) := Rep.of (trivRep N κ)

theorem isTwist_V (ρW : Representation κ (CuspidalType.GL2 q) W) :
    ∀ i : Idx N q S₀, HeckeCohomology.IsTwist (S₁ N q S₀ i) (S₂ N q S₀ i) (cfam N q S₀ i) (Rep.of (pull N q κ ρW)) (φfam N q κ S₀ ρW i)
  | Sum.inl i => by
      haveI : NeZero (i.1 : ℕ) := ⟨i.2.1.ne_zero⟩
      change HeckeCohomology.IsTwist ⊤ (CohCarrier.GammaHUpper N (⊥ : Subgroup (ZMod N)ˣ) i.1)
        (HeckeCohomology.cTop N (⊥ : Subgroup (ZMod N)ˣ) i.1) (Rep.of (pull N q κ ρW)) (φfam N q κ S₀ ρW (Sum.inl i))
      rw [φfam_inl]
      exact isTwist_pull_diagElem N q κ ρW i.1 (good_ne_zero N q S₀ i)
  | Sum.inr σ => isTwist_conjTop N (ρW.comp (red0 N q)) σ

theorem isTwist_ind : ∀ i : Idx N q S₀, HeckeCohomology.IsTwist (S₁ N q S₀ i) (S₂ N q S₀ i) (cfam N q S₀ i)
    (XInd N q κ) (φfam N q κ S₀ (CuspidalType.ind q κ) i) :=
  isTwist_V N q κ S₀ (CuspidalType.ind q κ)

theorem isTwist_st : ∀ i : Idx N q S₀, HeckeCohomology.IsTwist (S₁ N q S₀ i) (S₂ N q S₀ i) (cfam N q S₀ i)
    (XSt N q κ) (φSt N q κ S₀ i)
  | Sum.inl i => by
      intro s w
      apply Subtype.ext
      have h := isTwist_ind N q κ S₀ (Sum.inl i) s (w : CuspidalType.ProjLine q →₀ κ)
      rw [φfam_inl] at h
      rw [φSt_inl]
      exact h
  | Sum.inr σ => by
      intro s w
      apply Subtype.ext
      exact isTwist_ind N q κ S₀ (Sum.inr σ) s (w : CuspidalType.ProjLine q →₀ κ)

omit [NeZero N] [Fact q.Prime] in

theorem isTwist_triv : ∀ i : Idx N q S₀,
    HeckeCohomology.IsTwist (S₁ N q S₀ i) (S₂ N q S₀ i) (cfam N q S₀ i) (Xκ N κ) LinearMap.id :=
  fun _ _ _ => rfl

def lamfam (lam : ℕ → κ) : Idx N q S₀ → κ := Sum.elim (fun i => lam i.1) (fun _ => 1)

def ccfam : Idx N q S₀ → κ := Sum.elim (fun i => (i.1 : κ) + 1) (fun _ => 1)

theorem hinv_triv : ∀ (i : Idx N q S₀) (z : (Xκ N κ).ρ.invariants),
    HeckeCohomology.heckeInv (S₁ N q S₀ i) (S₂ N q S₀ i) (cfam N q S₀ i) (Xκ N κ) LinearMap.id
      (isTwist_triv N q κ S₀ i) z = ccfam N q κ S₀ i • z
  | Sum.inl i, z => by
      haveI : NeZero (i.1 : ℕ) := ⟨i.2.1.ne_zero⟩
      exact heckeInv_one_eq_smul N (⊥ : Subgroup (ZMod N)ˣ) i.1 i.2.1 i.2.2.1 (Xκ N κ) (fun _ => rfl) _ z
  | Sum.inr σ, z => by
      change HeckeCohomology.heckeInv ⊤ ⊤ (conjTop N σ) (Xκ N κ) LinearMap.id _ z = (1 : κ) • z
      rw [one_smul]
      exact heckeInv_top_eq_self ⊤ (conjTop N σ) (Xκ N κ) (fun _ => rfl) LinearMap.id (fun _ => rfl) _ z

theorem hf_subtype : ∀ (i : Idx N q S₀) (a : ↥(CuspidalType.steinberg q κ).toSubmodule),
    (CuspidalType.steinberg q κ).toSubmodule.subtype (φSt N q κ S₀ i a) =
      φfam N q κ S₀ (CuspidalType.ind q κ) i ((CuspidalType.steinberg q κ).toSubmodule.subtype a)
  | Sum.inl i, a => by rw [φSt_inl, φfam_inl]; rfl
  | Sum.inr σ, a => rfl

theorem hg_coeffSum : ∀ (i : Idx N q S₀) (b : CuspidalType.ProjLine q →₀ κ),
    CuspidalType.coeffSum q κ (φfam N q κ S₀ (CuspidalType.ind q κ) i b) = (LinearMap.id : κ →ₗ[κ] κ) (CuspidalType.coeffSum q κ b)
  | Sum.inl i, b => by rw [φfam_inl]; exact coeffSum_ind q κ _ b
  | Sum.inr σ, b => coeffSum_ind q κ _ b

def HCOMM : Prop :=
  ∀ i j : Idx N q S₀,
    Commute (HeckeCohomology.heckeH1 (S₁ N q S₀ i) (S₂ N q S₀ i) (cfam N q S₀ i) (XSt N q κ)
        (φSt N q κ S₀ i) (isTwist_st N q κ S₀ i))
      (HeckeCohomology.heckeH1 (S₁ N q S₀ j) (S₂ N q S₀ j) (cfam N q S₀ j) (XSt N q κ)
        (φSt N q κ S₀ j) (isTwist_st N q κ S₀ j))

def D3 (lam : ℕ → κ) : Prop :=
  ∀ z : groupCohomology.H1 (XInd N q κ), z ≠ 0 →
    (∀ i : Idx N q S₀, HeckeCohomology.heckeH1 (S₁ N q S₀ i) (S₂ N q S₀ i) (cfam N q S₀ i) (XInd N q κ)
        (φfam N q κ S₀ (CuspidalType.ind q κ) i) (isTwist_ind N q κ S₀ i) z = lamfam N q κ S₀ lam i • z) →
    haveI : NeZero (N * q) := ⟨Nat.mul_ne_zero (NeZero.ne N) (Fact.out : q.Prime).ne_zero⟩
    ∃ v : CohCarrier.H1 (N * q) ⊥ κ, v ≠ 0 ∧
      (∀ σ : CongruenceSubgroup.Gamma0 (N * q), CohCarrier.diamondRaw (N * q) ⊥ κ σ v = v) ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N * q → ℓ ∉ S₀ →
        haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
        CohCarrier.heckeT (N * q) ⊥ ℓ κ v = lam ℓ • v

def D3' (lam : ℕ → κ) : Prop :=
  ∀ z : groupCohomology.H1 (XInd N q κ), z ≠ 0 →
    (∀ i : Idx N q S₀, HeckeCohomology.heckeH1 (S₁ N q S₀ i) (S₂ N q S₀ i) (cfam N q S₀ i) (XInd N q κ)
        (φfam N q κ S₀ (CuspidalType.ind q κ) i) (isTwist_ind N q κ S₀ i) z = lamfam N q κ S₀ lam i • z) →
    haveI : NeZero (N * q) := ⟨Nat.mul_ne_zero (NeZero.ne N) (Fact.out : q.Prime).ne_zero⟩
    (∃ v : CohCarrier.H1 (N * q) ⊥ κ, v ≠ 0 ∧
      (∀ σ : CongruenceSubgroup.Gamma0 (N * q), CohCarrier.diamondRaw (N * q) ⊥ κ σ v = v) ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N * q → ℓ ∉ S₀ →
        haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
        CohCarrier.heckeT (N * q) ⊥ ℓ κ v = lam ℓ • v) ∨
      ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ insert q S₀ → lam ℓ = (ℓ : κ) + 1

theorem d3'_of_d3 (lam : ℕ → κ) (h : D3 N q κ S₀ lam) : D3' N q κ S₀ lam :=
  fun z hz hzT => Or.inl (h z hz hzT)

theorem d3_of_two_step (lam : ℕ → κ) {X' : Type} (P' : X' → Prop) (guard : Prop) (hguard : guard)
    (hD3a : ∀ z : groupCohomology.H1 (XInd N q κ), z ≠ 0 →
      (∀ i : Idx N q S₀, HeckeCohomology.heckeH1 (S₁ N q S₀ i) (S₂ N q S₀ i) (cfam N q S₀ i) (XInd N q κ)
          (φfam N q κ S₀ (CuspidalType.ind q κ) i) (isTwist_ind N q κ S₀ i) z = lamfam N q κ S₀ lam i • z) →
      ∃ v' : X', P' v')
    (hD3b : ∀ v' : X', P' v' → guard →
      haveI : NeZero (N * q) := ⟨Nat.mul_ne_zero (NeZero.ne N) (Fact.out : q.Prime).ne_zero⟩
      ∃ v : CohCarrier.H1 (N * q) ⊥ κ, v ≠ 0 ∧
        (∀ σ : CongruenceSubgroup.Gamma0 (N * q), CohCarrier.diamondRaw (N * q) ⊥ κ σ v = v) ∧
        ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N * q → ℓ ∉ S₀ →
          haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
          CohCarrier.heckeT (N * q) ⊥ ℓ κ v = lam ℓ • v) :
    D3 N q κ S₀ lam := by
  intro z hz hzT
  obtain ⟨v', hv'⟩ := hD3a z hz hzT
  exact hD3b v' hv' hguard

omit [NeZero N] [Fact q.Prime] in
theorem conjLowerMat_one (A : SL(2, ℤ)) (h : ((1 : ℕ) : ℤ) ∣ A 1 0) : CohCarrier.conjLowerMat 1 A h = A := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [CohCarrier.conjLowerMat]

omit [NeZero N] [Fact q.Prime] in
theorem levelLE_bot (M : ℕ) (H' : Subgroup (ZMod M)ˣ) : CohCarrier.LevelLE M M H' ⊥ 1 :=
  ⟨dvd_rfl, one_dvd _, fun u hu => by
    rw [Subgroup.mem_bot] at hu
    subst hu
    rw [map_one]
    exact H'.one_mem⟩

theorem d3_of_borel (lam : ℕ → κ) (hq1 : (q : κ) + 1 = 0) (h2 : (2 : κ) ≠ 0)
    (H' : Subgroup (ZMod (N * q))ˣ) (hrel : ((⊥ : Subgroup (ZMod (N * q))ˣ).relIndex H') ∣ q - 1)
    (hD3a : ∀ z : groupCohomology.H1 (XInd N q κ), z ≠ 0 →
      (∀ i : Idx N q S₀, HeckeCohomology.heckeH1 (S₁ N q S₀ i) (S₂ N q S₀ i) (cfam N q S₀ i) (XInd N q κ)
          (φfam N q κ S₀ (CuspidalType.ind q κ) i) (isTwist_ind N q κ S₀ i) z = lamfam N q κ S₀ lam i • z) →
      haveI : NeZero (N * q) := ⟨Nat.mul_ne_zero (NeZero.ne N) (Fact.out : q.Prime).ne_zero⟩
      ∃ v' : CohCarrier.H1 (N * q) H' κ, v' ≠ 0 ∧
        (∀ σ : CongruenceSubgroup.Gamma0 (N * q), CohCarrier.diamondRaw (N * q) H' κ σ v' = v') ∧
        ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N * q → ℓ ∉ S₀ →
          haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
          CohCarrier.heckeT (N * q) H' ℓ κ v' = lam ℓ • v') :
    D3 N q κ S₀ lam := by
  haveI : NeZero (N * q) := ⟨Nat.mul_ne_zero (NeZero.ne N) (Fact.out : q.Prime).ne_zero⟩
  intro z hz hzT
  obtain ⟨v', hv0, hvd, hvT⟩ := hD3a z hz hzT
  have hLE : CohCarrier.LevelLE (N * q) (N * q) H' ⊥ 1 := levelLE_bot (N * q) H'
  refine ⟨CohCarrier.iDeg' (N * q) (N * q) H' ⊥ 1 κ hLE v', ?_, ?_, ?_⟩
  ·
    have hunit : IsUnit ((((⊥ : Subgroup (ZMod (N * q))ˣ).relIndex H' : ℕ)) : κ) := by
      rw [isUnit_iff_ne_zero]
      intro h0
      obtain ⟨c, hc⟩ := hrel
      apply cast_pred_ne_zero q κ (Fact.out : q.Prime).one_lt.le hq1 h2
      rw [hc, Nat.cast_mul, h0, zero_mul]
    intro h0
    apply hv0
    apply CohCarrier.injective_iDeg_one_of_isUnit_relIndex (N * q) ⊥ H' κ κ hLE hunit
    rw [h0, map_zero]
  ·
    intro σ
    have hd : ((1 : ℕ) : ℤ) ∣ (σ : SL(2, ℤ)) 1 0 := by rw [Nat.cast_one]; exact one_dvd _
    let σ₀ : CongruenceSubgroup.Gamma0 (N * q) :=
      ⟨CohCarrier.conjLowerMat 1 (σ : SL(2, ℤ)) hd, by rw [conjLowerMat_one]; exact σ.2⟩
    have h := CohCarrier.iDeg_diamondRaw_comm hLE σ hd σ₀ rfl v'
    rw [hvd σ₀] at h
    exact h.symm
  ·
    intro ℓ hℓ hℓNq hℓS
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    have h := CohCarrier.iDeg_heckeT_comm_of_coprime hLE (Nat.coprime_one_right ℓ) hℓ hℓNq v'
    rw [hvT ℓ hℓ hℓNq hℓS] at h
    rw [← h]
    change CohCarrier.iDegL (N * q) (N * q) H' ⊥ 1 κ κ hLE (lam ℓ • v') = lam ℓ • CohCarrier.iDegL (N * q) (N * q) H' ⊥ 1 κ κ hLE v'
    rw [map_smul]

abbrev Hker : Subgroup (ZMod (N * q))ˣ := (ZMod.unitsMap (dvd_mul_right N q)).ker

theorem relIndex_bot_Hker (hqN : ¬ q ∣ N) : (⊥ : Subgroup (ZMod (N * q))ˣ).relIndex (Hker N q) = q - 1 := by
  have hq : q.Prime := Fact.out
  haveI : NeZero (N * q) := ⟨Nat.mul_ne_zero (NeZero.ne N) hq.ne_zero⟩
  rw [Subgroup.relIndex_bot_left]
  have hsurj := ZMod.unitsMap_surjective (dvd_mul_right N q)

  have hcard : Nat.card (ZMod (N * q))ˣ = Nat.card (ZMod N)ˣ * Nat.card (Hker N q) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Hker N q),
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hsurj).toEquiv]
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, ZMod.card_units_eq_totient,
    Nat.totient_mul ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqN).symm, Nat.totient_prime hq] at hcard
  exact (Nat.eq_of_mul_eq_mul_left (Nat.totient_pos.mpr (NeZero.pos N)) hcard).symm

theorem d3_of_borel_ker (lam : ℕ → κ) (hqN : ¬ q ∣ N) (hq1 : (q : κ) + 1 = 0) (h2 : (2 : κ) ≠ 0)
    (hD3a : ∀ z : groupCohomology.H1 (XInd N q κ), z ≠ 0 →
      (∀ i : Idx N q S₀, HeckeCohomology.heckeH1 (S₁ N q S₀ i) (S₂ N q S₀ i) (cfam N q S₀ i) (XInd N q κ)
          (φfam N q κ S₀ (CuspidalType.ind q κ) i) (isTwist_ind N q κ S₀ i) z = lamfam N q κ S₀ lam i • z) →
      haveI : NeZero (N * q) := ⟨Nat.mul_ne_zero (NeZero.ne N) (Fact.out : q.Prime).ne_zero⟩
      ∃ v' : CohCarrier.H1 (N * q) (Hker N q) κ, v' ≠ 0 ∧
        (∀ σ : CongruenceSubgroup.Gamma0 (N * q), CohCarrier.diamondRaw (N * q) (Hker N q) κ σ v' = v') ∧
        ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N * q → ℓ ∉ S₀ →
          haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
          CohCarrier.heckeT (N * q) (Hker N q) ℓ κ v' = lam ℓ • v') :
    D3 N q κ S₀ lam :=
  d3_of_borel N q κ S₀ lam hq1 h2 (Hker N q) (dvd_of_eq (relIndex_bot_Hker N q hqN)) hD3a

section Steps

variable {V : Type} [AddCommGroup V] [Module κ V]
  (ρ : Representation κ (CuspidalType.GL2 q) V)
  (π : ↥(CuspidalType.steinberg q κ).toSubmodule →ₗ[κ] V)
  (hπ : ∀ g : CuspidalType.GL2 q, ∀ v : ↥(CuspidalType.steinberg q κ).toSubmodule,
    π ⟨CuspidalType.ind q κ g v, (CuspidalType.steinberg q κ).apply_mem_toSubmodule g v.2⟩ = ρ g (π v))
  (hq1 : (q : κ) + 1 = 0)
  (hπker : ∀ v : ↥(CuspidalType.steinberg q κ).toSubmodule, π v = 0 ↔ ∃ c : κ, (v : CuspidalType.ProjLine q →₀ κ) = c • CuspidalType.constFun q κ)

include hπ hq1 hπker in

theorem step_D2 (hN4 : 4 ≤ N) (hπsurj : Function.Surjective π) (lam : ℕ → κ) (hcomm : HCOMM N q κ S₀)
    (y : groupCohomology.H1 (Rep.of (vRep N q κ ρ))) (hy0 : y ≠ 0)
    (hyT : ∀ i : Idx N q S₀, HeckeCohomology.heckeH1 (S₁ N q S₀ i) (S₂ N q S₀ i) (cfam N q S₀ i) (Rep.of (vRep N q κ ρ))
      (φfam N q κ S₀ ρ i) (isTwist_V N q κ S₀ ρ i) y = lamfam N q κ S₀ lam i • y) :
    ∃ x : groupCohomology.H1 (XSt N q κ), x ≠ 0 ∧
      ∀ i : Idx N q S₀, HeckeCohomology.heckeH1 (S₁ N q S₀ i) (S₂ N q S₀ i) (cfam N q S₀ i) (XSt N q κ)
        (φSt N q κ S₀ i) (isTwist_st N q κ S₀ i) x = lamfam N q κ S₀ lam i • x := by
  have hH : ∀ u ∈ (⊥ : Subgroup (ZMod N)ˣ), ZMod.castHom (dvd_refl N) (ZMod N) ((u : (ZMod N)ˣ) : ZMod N) = 1 := by
    intro u hu
    rw [Subgroup.mem_bot] at hu
    subst hu
    rw [Units.val_one, map_one]
  haveI : Module.Finite κ (ses1 N q κ ρ π hπ hq1 hπker).X₂ :=
    (inferInstance : Module.Finite κ ↥(CuspidalType.steinberg q κ).toSubmodule)
  exact HeckeCohomology.exists_eigenvector_H1_of_eigenvector_H1_of_shortExact_gammaH N N (dvd_refl N) hN4 ⊥ hH
      (ses1_shortExact N q κ ρ π hπ hq1 hπker hπsurj)
      (S₁ N q S₀) (S₂ N q S₀) (cfam N q S₀)
      (φSt N q κ S₀) (isTwist_st N q κ S₀)
      (φfam N q κ S₀ ρ) (isTwist_V N q κ S₀ ρ)
      (fun i b => by
        change π (φSt N q κ S₀ i b) = φfam N q κ S₀ ρ i (π b)
        rcases i with i | σ
        · rw [φSt_inl, φfam_inl]
          exact hπ _ b
        · exact hπ _ b)
      hcomm (lamfam N q κ S₀ lam) ⟨y, hy0, hyT⟩

theorem step_PUSH (lam : ℕ → κ)
    (x : groupCohomology.H1 (XSt N q κ)) (hx0 : x ≠ 0)
    (hxT : ∀ i : Idx N q S₀, HeckeCohomology.heckeH1 (S₁ N q S₀ i) (S₂ N q S₀ i) (cfam N q S₀ i) (XSt N q κ)
        (φSt N q κ S₀ i) (isTwist_st N q κ S₀ i) x = lamfam N q κ S₀ lam i • x) :
    (∃ z : groupCohomology.H1 (XInd N q κ), z ≠ 0 ∧
      ∀ i : Idx N q S₀, HeckeCohomology.heckeH1 (S₁ N q S₀ i) (S₂ N q S₀ i) (cfam N q S₀ i) (XInd N q κ)
        (φfam N q κ S₀ (CuspidalType.ind q κ) i) (isTwist_ind N q κ S₀ i) z = lamfam N q κ S₀ lam i • z) ∨
    ∀ i : Idx N q S₀, lamfam N q κ S₀ lam i = ccfam N q κ S₀ i :=
  HeckeCohomology.exists_eigenvector_H1_or_forall_eq_of_eigenvector_H1_of_shortExact (ses2_shortExact N q κ)
      (S₁ N q S₀) (S₂ N q S₀) (cfam N q S₀)
      (φSt N q κ S₀) (isTwist_st N q κ S₀)
      (φfam N q κ S₀ (CuspidalType.ind q κ)) (isTwist_ind N q κ S₀)
      (fun _ => LinearMap.id) (isTwist_triv N q κ S₀)
      (hf_subtype N q κ S₀) (hg_coeffSum N q κ S₀)
      (ccfam N q κ S₀) (hinv_triv N q κ S₀) (lamfam N q κ S₀ lam) ⟨x, hx0, hxT⟩

end Steps
p2m_reactivate "P2MW.S_CohCarrier_exists_diamondRaw_eq_heckeT_eq_smul_gammaH_bot_mul_or_eisenstein_of_isEigensystemH1_of_steinberg_quotient_of_four_le.RepSES"

end Family
p2m_reactivate "P2MW.S_CohCarrier_exists_diamondRaw_eq_heckeT_eq_smul_gammaH_bot_mul_or_eisenstein_of_isEigensystemH1_of_steinberg_quotient_of_four_le.RepSES"

theorem dock_core
    (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N) (S₀ : Set ℕ)
    (hN4 : 4 ≤ N)
    (κ : Type) [Field κ] (hq1 : (q : κ) + 1 = 0) (h2 : (2 : κ) ≠ 0)
    {V : Type} [AddCommGroup V] [Module κ V] [FiniteDimensional κ V]
    (ρ : Representation κ (CuspidalType.GL2 q) V)
    (π : ↥(CuspidalType.steinberg q κ).toSubmodule →ₗ[κ] V)
    (hπ : ∀ g : CuspidalType.GL2 q, ∀ v : ↥(CuspidalType.steinberg q κ).toSubmodule,
      π ⟨CuspidalType.ind q κ g v, (CuspidalType.steinberg q κ).apply_mem_toSubmodule g v.2⟩ = ρ g (π v))
    (hπsurj : Function.Surjective π)
    (hπker : ∀ v : ↥(CuspidalType.steinberg q κ).toSubmodule, π v = 0 ↔ ∃ c : κ, (v : CuspidalType.ProjLine q →₀ κ) = c • CuspidalType.constFun q κ)
    (lam : ℕ → κ)
    (hocc : HeckeEis.IsEigensystemH1 N (ρ.comp ((Matrix.SpecialLinearGroup.toGL.comp
            (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype))
      (fun ℓ : ℕ =>
        if h : ((ℓ : ZMod q) ≠ 0) then ρ (CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) h)) else LinearMap.id)
      (insert q S₀) lam)
    (hcomm : HCOMM N q κ S₀) (hD3 : D3 N q κ S₀ lam) :
    haveI : NeZero (N * q) := ⟨Nat.mul_ne_zero (NeZero.ne N) (Fact.out : q.Prime).ne_zero⟩
    (∃ v : CohCarrier.H1 (N * q) ⊥ κ, v ≠ 0 ∧
      (∀ σ : CongruenceSubgroup.Gamma0 (N * q), CohCarrier.diamondRaw (N * q) ⊥ κ σ v = v) ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N * q → ℓ ∉ S₀ →
        haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
        CohCarrier.heckeT (N * q) ⊥ ℓ κ v = lam ℓ • v) ∨
      ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ insert q S₀ → lam ℓ = (ℓ : κ) + 1 := by

  have hV := CuspidalType.eq_zero_of_forall_specialLinearGroup_apply_eq_of_steinberg_quotient q κ hq1 ρ π hπ hπsurj hπker

  obtain ⟨hφ, y, hy0, hdia, hT⟩ :=
    HeckeEis.exists_ne_zero_map_conjHom_eq_and_heckeH1_gammaH_bot_eq_smul_of_isEigensystemH1 N q hqN S₀ κ ρ hV lam hocc
  have hyT : ∀ i : Idx N q S₀, HeckeCohomology.heckeH1 (S₁ N q S₀ i) (S₂ N q S₀ i) (cfam N q S₀ i) (Rep.of (vRep N q κ ρ))
      (φfam N q κ S₀ ρ i) (isTwist_V N q κ S₀ ρ i) y = lamfam N q κ S₀ lam i • y := by
    intro i
    rcases i with i | σ
    · exact hT i
    · change HeckeCohomology.heckeH1 ⊤ ⊤ (conjTop N σ) (Rep.of (pull N q κ ρ)) (φfam N q κ S₀ ρ (Sum.inr σ)) _ y = (1 : κ) • y
      rw [one_smul]
      refine heckeH1_conjTop_eq_self_of_forall_map_conjHom N (ρ.comp (red0 N q)) y (fun τ c hc => hdia τ c fun v => ?_) σ
      rw [hc v, MonoidHom.comp_apply, map_inv]

  obtain ⟨x, hx0, hxT⟩ := step_D2 N q κ S₀ ρ π hπ hq1 hπker hN4 hπsurj lam hcomm y hy0 hyT
  rcases step_PUSH N q κ S₀ lam x hx0 hxT with ⟨z, hz0, hzT⟩ | heis
  · exact Or.inl (hD3 z hz0 hzT)
  · exact Or.inr fun ℓ hℓ hℓN hℓS => heis (Sum.inl ⟨ℓ, hℓ, hℓN, hℓS⟩)

theorem dock_core'
    (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N) (S₀ : Set ℕ)
    (hN4 : 4 ≤ N)
    (κ : Type) [Field κ] (hq1 : (q : κ) + 1 = 0) (h2 : (2 : κ) ≠ 0)
    {V : Type} [AddCommGroup V] [Module κ V] [FiniteDimensional κ V]
    (ρ : Representation κ (CuspidalType.GL2 q) V)
    (π : ↥(CuspidalType.steinberg q κ).toSubmodule →ₗ[κ] V)
    (hπ : ∀ g : CuspidalType.GL2 q, ∀ v : ↥(CuspidalType.steinberg q κ).toSubmodule,
      π ⟨CuspidalType.ind q κ g v, (CuspidalType.steinberg q κ).apply_mem_toSubmodule g v.2⟩ = ρ g (π v))
    (hπsurj : Function.Surjective π)
    (hπker : ∀ v : ↥(CuspidalType.steinberg q κ).toSubmodule, π v = 0 ↔ ∃ c : κ, (v : CuspidalType.ProjLine q →₀ κ) = c • CuspidalType.constFun q κ)
    (lam : ℕ → κ)
    (hocc : HeckeEis.IsEigensystemH1 N (ρ.comp ((Matrix.SpecialLinearGroup.toGL.comp
            (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype))
      (fun ℓ : ℕ =>
        if h : ((ℓ : ZMod q) ≠ 0) then ρ (CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) h)) else LinearMap.id)
      (insert q S₀) lam)
    (hcomm : HCOMM N q κ S₀) (hD3 : D3' N q κ S₀ lam) :
    haveI : NeZero (N * q) := ⟨Nat.mul_ne_zero (NeZero.ne N) (Fact.out : q.Prime).ne_zero⟩
    (∃ v : CohCarrier.H1 (N * q) ⊥ κ, v ≠ 0 ∧
      (∀ σ : CongruenceSubgroup.Gamma0 (N * q), CohCarrier.diamondRaw (N * q) ⊥ κ σ v = v) ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N * q → ℓ ∉ S₀ →
        haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
        CohCarrier.heckeT (N * q) ⊥ ℓ κ v = lam ℓ • v) ∨
      ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ insert q S₀ → lam ℓ = (ℓ : κ) + 1 := by

  have hV := CuspidalType.eq_zero_of_forall_specialLinearGroup_apply_eq_of_steinberg_quotient q κ hq1 ρ π hπ hπsurj hπker

  obtain ⟨hφ, y, hy0, hdia, hT⟩ :=
    HeckeEis.exists_ne_zero_map_conjHom_eq_and_heckeH1_gammaH_bot_eq_smul_of_isEigensystemH1 N q hqN S₀ κ ρ hV lam hocc
  have hyT : ∀ i : Idx N q S₀, HeckeCohomology.heckeH1 (S₁ N q S₀ i) (S₂ N q S₀ i) (cfam N q S₀ i) (Rep.of (vRep N q κ ρ))
      (φfam N q κ S₀ ρ i) (isTwist_V N q κ S₀ ρ i) y = lamfam N q κ S₀ lam i • y := by
    intro i
    rcases i with i | σ
    · exact hT i
    · change HeckeCohomology.heckeH1 ⊤ ⊤ (conjTop N σ) (Rep.of (pull N q κ ρ)) (φfam N q κ S₀ ρ (Sum.inr σ)) _ y = (1 : κ) • y
      rw [one_smul]
      refine heckeH1_conjTop_eq_self_of_forall_map_conjHom N (ρ.comp (red0 N q)) y (fun τ c hc => hdia τ c fun v => ?_) σ
      rw [hc v, MonoidHom.comp_apply, map_inv]

  obtain ⟨x, hx0, hxT⟩ := step_D2 N q κ S₀ ρ π hπ hq1 hπker hN4 hπsurj lam hcomm y hy0 hyT
  rcases step_PUSH N q κ S₀ lam x hx0 hxT with ⟨z, hz0, hzT⟩ | heis
  · exact hD3 z hz0 hzT
  · exact Or.inr fun ℓ hℓ hℓN hℓS => heis (Sum.inl ⟨ℓ, hℓ, hℓN, hℓS⟩)

end Core
p2m_reactivate "P2MW.S_CohCarrier_exists_diamondRaw_eq_heckeT_eq_smul_gammaH_bot_mul_or_eisenstein_of_isEigensystemH1_of_steinberg_quotient_of_four_le.RepSES"

section Shapiro
variable (N q : ℕ) [NeZero N] [Fact q.Prime] (κ : Type) [Field κ] (S₀ : Set ℕ)

omit [NeZero N] [Fact q.Prime] in

theorem gamma0_mul_le : Gamma0 (N * q) ≤ Gamma0 N := by
  intro A hA
  rw [Gamma0_mem] at hA ⊢
  have h := congrArg (ZMod.castHom (dvd_mul_right N q) (ZMod N)) hA
  rwa [map_intCast, map_zero] at h

omit [NeZero N] [Fact q.Prime] in

def liftNq (σ : Gamma0 (N * q)) : Gamma0 N := ⟨(σ : SL(2, ℤ)), gamma0_mul_le N q σ.2⟩

omit [NeZero N] [Fact q.Prime] in
@[scoped simp] theorem coe_liftNq (σ : Gamma0 (N * q)) : ((liftNq N q σ : Gamma0 N) : SL(2, ℤ)) = (σ : SL(2, ℤ)) := rfl

noncomputable abbrev XA : Rep κ (Gam N) :=
  Rep.of ((CuspidalType.ind q κ).comp (Matrix.SpecialLinearGroup.toGL.comp
    ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q))).comp (CohCarrier.GammaH N ⊥).subtype)))

theorem XInd_eq_XA : XInd N q κ = XA N q κ := rfl

noncomputable abbrev ρ0 : Representation κ ↥(Gamma0 N) (CuspidalType.ProjLine q →₀ κ) :=
  (CuspidalType.ind q κ).comp (red0 N q)

theorem hD3a_of_shapiro (lam : ℕ → κ)
    (Φ : groupCohomology.H1 (XInd N q κ) →+
      (haveI : NeZero (N * q) := ⟨Nat.mul_ne_zero (NeZero.ne N) (Fact.out : q.Prime).ne_zero⟩
       CohCarrier.H1 (N * q) (Hker N q) κ))
    (hlin : ∀ (a : κ) (x : groupCohomology.H1 (XInd N q κ)), Φ (a • x) = a • Φ x)
    (hbij : Function.Bijective Φ)
    (hdia : ∀ (σ : CongruenceSubgroup.Gamma0 (N * q))
        (c : Rep.res (CohCarrier.conjHom N ⊥ (liftNq N q σ)) (XInd N q κ) ⟶ XInd N q κ),
        (∀ v, c.hom v =
          CuspidalType.ind q κ
            (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q))
              (liftNq N q σ : Matrix.SpecialLinearGroup (Fin 2) ℤ)))⁻¹ v) →
        ∀ x, Φ (groupCohomology.map (CohCarrier.conjHom N ⊥ (liftNq N q σ)) c 1 x) =
          haveI : NeZero (N * q) := ⟨Nat.mul_ne_zero (NeZero.ne N) (Fact.out : q.Prime).ne_zero⟩
          CohCarrier.diamondRaw (N * q) (Hker N q) κ σ (Φ x))
    (hhecke : ∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ¬ ℓ ∣ N * q → ∀ (u : (ZMod q)ˣ), (u : ZMod q) = ℓ →
        ∀ (hφ : HeckeCohomology.IsTwist ⊤ (CohCarrier.GammaHUpper N ⊥ ℓ) (HeckeCohomology.cTop N ⊥ ℓ)
            (XInd N q κ) (CuspidalType.ind q κ (CuspidalType.diagElem q u)))
          (x : groupCohomology.H1 (XInd N q κ)),
          Φ (HeckeCohomology.heckeH1 ⊤ (CohCarrier.GammaHUpper N ⊥ ℓ) (HeckeCohomology.cTop N ⊥ ℓ) _ _ hφ x) =
            haveI : NeZero (N * q) := ⟨Nat.mul_ne_zero (NeZero.ne N) (Fact.out : q.Prime).ne_zero⟩
            CohCarrier.heckeT (N * q) (Hker N q) ℓ κ (Φ x)) :
    ∀ z : groupCohomology.H1 (XInd N q κ), z ≠ 0 →
      (∀ i : Idx N q S₀, HeckeCohomology.heckeH1 (S₁ N q S₀ i) (S₂ N q S₀ i) (cfam N q S₀ i) (XInd N q κ)
          (φfam N q κ S₀ (CuspidalType.ind q κ) i) (isTwist_ind N q κ S₀ i) z = lamfam N q κ S₀ lam i • z) →
      haveI : NeZero (N * q) := ⟨Nat.mul_ne_zero (NeZero.ne N) (Fact.out : q.Prime).ne_zero⟩
      ∃ v' : CohCarrier.H1 (N * q) (Hker N q) κ, v' ≠ 0 ∧
        (∀ σ : CongruenceSubgroup.Gamma0 (N * q), CohCarrier.diamondRaw (N * q) (Hker N q) κ σ v' = v') ∧
        ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N * q → ℓ ∉ S₀ →
          haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
          CohCarrier.heckeT (N * q) (Hker N q) ℓ κ v' = lam ℓ • v' := by
  haveI : NeZero (N * q) := ⟨Nat.mul_ne_zero (NeZero.ne N) (Fact.out : q.Prime).ne_zero⟩
  intro z hz heig
  refine ⟨Φ z, ?_, ?_, ?_⟩
  ·
    intro h0
    apply hz
    apply hbij.1
    rw [h0, map_zero]
  ·
    intro σ
    have hy : ∀ σ' : ↥(Gamma0 N), HeckeCohomology.heckeH1 ⊤ ⊤ (conjTop N σ') (A N (ρ0 N q κ)) (ρ0 N q κ σ')
        (isTwist_conjTop N (ρ0 N q κ) σ') z = z := by
      intro σ'
      have h := heig (Sum.inr σ')
      change HeckeCohomology.heckeH1 ⊤ ⊤ (conjTop N σ') (XInd N q κ) (φfam N q κ S₀ (CuspidalType.ind q κ) (Sum.inr σ'))
        (isTwist_ind N q κ S₀ (Sum.inr σ')) z = (1 : κ) • z at h
      rw [one_smul] at h
      exact h
    have hc : ∀ v, (cHom N (ρ0 N q κ) (liftNq N q σ)).hom v =
        CuspidalType.ind q κ
          (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q))
            (liftNq N q σ : Matrix.SpecialLinearGroup (Fin 2) ℤ)))⁻¹ v := by
      intro v
      rw [cHom_apply, MonoidHom.comp_apply, map_inv]
      rfl
    have h := hdia σ (cHom N (ρ0 N q κ) (liftNq N q σ)) hc z
    rw [map_conjHom_eq_self_of_forall_heckeH1_conjTop N (ρ0 N q κ) z hy (liftNq N q σ)
      (cHom N (ρ0 N q κ) (liftNq N q σ)) (fun v => rfl)] at h
    exact h.symm
  ·
    intro ℓ hℓ hℓNq hℓS
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    have hℓN : ¬ ℓ ∣ N := fun h => hℓNq (h.mul_right q)
    have hℓq : ℓ ≠ q := by
      rintro rfl
      exact hℓNq (Nat.dvd_mul_left _ _)
    let i : GoodIdx N q S₀ := ⟨ℓ, hℓ, hℓN, fun h => (Set.mem_insert_iff.1 h).elim hℓq hℓS⟩
    have hgen : ∀ (φ : (CuspidalType.ProjLine q →₀ κ) →ₗ[κ] (CuspidalType.ProjLine q →₀ κ))
        (hφ : HeckeCohomology.IsTwist ⊤ (CohCarrier.GammaHUpper N ⊥ ℓ) (HeckeCohomology.cTop N ⊥ ℓ) (XInd N q κ) φ),
        φ = φfam N q κ S₀ (CuspidalType.ind q κ) (Sum.inl i) →
        HeckeCohomology.heckeH1 ⊤ (CohCarrier.GammaHUpper N ⊥ ℓ) (HeckeCohomology.cTop N ⊥ ℓ) (XInd N q κ) φ hφ z =
          lam ℓ • z := by
      rintro φ hφ rfl
      exact heig (Sum.inl i)
    have hz' := hgen _ (isTwist_pull_diagElem N q κ (CuspidalType.ind q κ) ℓ (good_ne_zero N q S₀ i))
      (φfam_inl N q κ S₀ (CuspidalType.ind q κ) i).symm
    have key := hhecke ℓ hℓ hℓNq (Units.mk0 ((ℓ : ℕ) : ZMod q) (good_ne_zero N q S₀ i)) rfl
      (isTwist_pull_diagElem N q κ (CuspidalType.ind q κ) ℓ (good_ne_zero N q S₀ i)) z
    rw [hz', hlin] at key
    exact key.symm

theorem d3_of_shapiro (lam : ℕ → κ) (hqN : ¬ q ∣ N) (hq1 : (q : κ) + 1 = 0) (h2 : (2 : κ) ≠ 0)
    (Φ : groupCohomology.H1 (XInd N q κ) →+
      (haveI : NeZero (N * q) := ⟨Nat.mul_ne_zero (NeZero.ne N) (Fact.out : q.Prime).ne_zero⟩
       CohCarrier.H1 (N * q) (Hker N q) κ))
    (hlin : ∀ (a : κ) (x : groupCohomology.H1 (XInd N q κ)), Φ (a • x) = a • Φ x)
    (hbij : Function.Bijective Φ)
    (hdia : ∀ (σ : CongruenceSubgroup.Gamma0 (N * q))
        (c : Rep.res (CohCarrier.conjHom N ⊥ (liftNq N q σ)) (XInd N q κ) ⟶ XInd N q κ),
        (∀ v, c.hom v =
          CuspidalType.ind q κ
            (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q))
              (liftNq N q σ : Matrix.SpecialLinearGroup (Fin 2) ℤ)))⁻¹ v) →
        ∀ x, Φ (groupCohomology.map (CohCarrier.conjHom N ⊥ (liftNq N q σ)) c 1 x) =
          haveI : NeZero (N * q) := ⟨Nat.mul_ne_zero (NeZero.ne N) (Fact.out : q.Prime).ne_zero⟩
          CohCarrier.diamondRaw (N * q) (Hker N q) κ σ (Φ x))
    (hhecke : ∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ¬ ℓ ∣ N * q → ∀ (u : (ZMod q)ˣ), (u : ZMod q) = ℓ →
        ∀ (hφ : HeckeCohomology.IsTwist ⊤ (CohCarrier.GammaHUpper N ⊥ ℓ) (HeckeCohomology.cTop N ⊥ ℓ)
            (XInd N q κ) (CuspidalType.ind q κ (CuspidalType.diagElem q u)))
          (x : groupCohomology.H1 (XInd N q κ)),
          Φ (HeckeCohomology.heckeH1 ⊤ (CohCarrier.GammaHUpper N ⊥ ℓ) (HeckeCohomology.cTop N ⊥ ℓ) _ _ hφ x) =
            haveI : NeZero (N * q) := ⟨Nat.mul_ne_zero (NeZero.ne N) (Fact.out : q.Prime).ne_zero⟩
            CohCarrier.heckeT (N * q) (Hker N q) ℓ κ (Φ x)) :
    D3 N q κ S₀ lam :=
  d3_of_borel_ker N q κ S₀ lam hqN hq1 h2 (hD3a_of_shapiro N q κ S₀ lam Φ hlin hbij hdia hhecke)

end Shapiro
p2m_reactivate "P2MW.S_CohCarrier_exists_diamondRaw_eq_heckeT_eq_smul_gammaH_bot_mul_or_eisenstein_of_isEigensystemH1_of_steinberg_quotient_of_four_le.RepSES"

section HComm
variable (N q : ℕ) [NeZero N] [Fact q.Prime] (κ : Type) [Field κ] (S₀ : Set ℕ)

omit [NeZero N] [Fact q.Prime] in

theorem heckeH1_congr {S₁ S₂ : Subgroup (Gam N)} [S₂.FiniteIndex] {c c' : ↥S₂ →* ↥S₁} (hc : c = c')
    (A : Rep κ (Gam N)) {φ φ' : A →ₗ[κ] A} (hφφ : φ = φ')
    (hφ : HeckeCohomology.IsTwist S₁ S₂ c A φ) (hφ' : HeckeCohomology.IsTwist S₁ S₂ c' A φ') :
    HeckeCohomology.heckeH1 S₁ S₂ c A φ hφ = HeckeCohomology.heckeH1 S₁ S₂ c' A φ' hφ' := by
  subst hc
  subst hφφ
  rfl

def Mq : Submonoid (Matrix (Fin 2) (Fin 2) ℤ) :=
  (IsUnit.submonoid (Matrix (Fin 2) (Fin 2) (ZMod q))).comap (Int.castRingHom (ZMod q)).mapMatrix.toMonoidHom

theorem mem_Mq {g : Matrix (Fin 2) (Fin 2) ℤ} :
    g ∈ Mq q ↔ IsUnit ((Int.castRingHom (ZMod q)).mapMatrix g) := Iff.rfl

theorem sl_mem_Mq (g : SL(2, ℤ)) : (g : Matrix (Fin 2) (Fin 2) ℤ) ∈ Mq q := by
  rw [mem_Mq]
  exact ⟨Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)) g), rfl⟩

noncomputable def toGLq : ↥(Mq q) →* CuspidalType.GL2 q where
  toFun g := ((mem_Mq q).1 g.2).unit
  map_one' := Units.ext (by rw [IsUnit.unit_spec, Units.val_one, OneMemClass.coe_one, map_one])
  map_mul' a b := Units.ext (by rw [IsUnit.unit_spec, Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec, Submonoid.coe_mul, map_mul])

theorem coe_toGLq (g : ↥(Mq q)) :
    ((toGLq q g : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) =
      (Int.castRingHom (ZMod q)).mapMatrix (g : Matrix (Fin 2) (Fin 2) ℤ) :=
  IsUnit.unit_spec _

theorem toGLq_sl (g : SL(2, ℤ)) (hg : (g : Matrix (Fin 2) (Fin 2) ℤ) ∈ Mq q) :
    toGLq q ⟨(g : Matrix (Fin 2) (Fin 2) ℤ), hg⟩ =
      Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)) g) :=
  Units.ext (coe_toGLq q _)

theorem diag_map (ℓ : ℕ) :
    (Int.castRingHom (ZMod q)).mapMatrix !![(ℓ : ℤ), 0; 0, 1] = !![((ℓ : ℕ) : ZMod q), 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem diag_mem_Mq (ℓ : ℕ) (hℓq : ((ℓ : ℕ) : ZMod q) ≠ 0) : !![(ℓ : ℤ), 0; 0, 1] ∈ Mq q := by
  rw [mem_Mq, diag_map]
  exact ⟨CuspidalType.diagElem q (Units.mk0 ((ℓ : ℕ) : ZMod q) hℓq), CuspidalType.diagElem_val q _⟩

theorem toGLq_diag (ℓ : ℕ) (hℓq : ((ℓ : ℕ) : ZMod q) ≠ 0) (h : !![(ℓ : ℤ), 0; 0, 1] ∈ Mq q) :
    toGLq q ⟨!![(ℓ : ℤ), 0; 0, 1], h⟩ = CuspidalType.diagElem q (Units.mk0 ((ℓ : ℕ) : ZMod q) hℓq) := by
  apply Units.ext
  rw [coe_toGLq, CuspidalType.diagElem_val]
  exact diag_map q ℓ

noncomputable abbrev ρSt' : ↥(Mq q) →* Module.End κ ↥(CuspidalType.steinberg q κ).toSubmodule :=
  (CuspidalType.steinbergRep q κ).comp (toGLq q)

theorem conjHom_codRestrict_eq_conjTop (σ : ↥(Gamma0 N)) :
    (((CohCarrier.conjHom N ⊥ σ⁻¹).comp (⊤ : Subgroup (Gam N)).subtype).codRestrict ⊤ fun _ => Subgroup.mem_top _) =
      conjTop N σ := by
  refine MonoidHom.ext fun s => Subtype.ext (Subtype.ext ?_)
  change ((σ⁻¹ : ↥(Gamma0 N)) : SL(2, ℤ)) * ((s : Gam N) : SL(2, ℤ)) * (((σ⁻¹ : ↥(Gamma0 N)) : SL(2, ℤ)))⁻¹ =
    (σ : SL(2, ℤ))⁻¹ * ((s : Gam N) : SL(2, ℤ)) * (σ : SL(2, ℤ))
  rw [InvMemClass.coe_inv, inv_inv]

theorem hcomm_st : HCOMM N q κ S₀ := by

  let T : Idx N q S₀ → (groupCohomology.H1 (XSt N q κ) →ₗ[κ] groupCohomology.H1 (XSt N q κ)) := fun i =>
    HeckeCohomology.heckeH1 (S₁ N q S₀ i) (S₂ N q S₀ i) (cfam N q S₀ i) (XSt N q κ) (φSt N q κ S₀ i) (isTwist_st N q κ S₀ i)
  have hΓ : ∀ g : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      g ∈ CongruenceSubgroup.Gamma0 N → (g : Matrix (Fin 2) (Fin 2) ℤ) ∈ Mq q := fun g _ => sl_mem_Mq q g
  have hρ' : ∀ γ : ↥(CohCarrier.GammaH N ⊥),
      (XSt N q κ).ρ γ = ρSt' q κ ⟨((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ),
        hΓ _ (CohCarrier.mem_GammaH_iff.mp γ.2).1⟩ := by
    intro γ
    change CuspidalType.steinbergRep q κ (red0 N q (incl N γ)) = CuspidalType.steinbergRep q κ (toGLq q _)
    rw [toGLq_sl]
    rfl
  have key := HeckeCohomology.commute_of_forall_eq_heckeH1_cTop_or_eq_heckeH1_conjHom_of_forall_rep_eq_monoidHom_submonoid
    N κ (XSt N q κ) (Mq q) hΓ (ρSt' q κ) hρ' (Idx N q S₀) T ?_
  · exact key

  intro i
  rcases i with i | σ
  · refine Or.inl ⟨i.1, i.2.1, i.2.2.1, diag_mem_Mq q i.1 (good_ne_zero N q S₀ i), ?_⟩
    haveI : NeZero (i.1 : ℕ) := ⟨i.2.1.ne_zero⟩
    have hφeq : φSt N q κ S₀ (Sum.inl i) = ρSt' q κ ⟨!![((i.1 : ℕ) : ℤ), 0; 0, 1], diag_mem_Mq q i.1 (good_ne_zero N q S₀ i)⟩ := by
      rw [φSt_inl, MonoidHom.comp_apply, toGLq_diag q i.1 (good_ne_zero N q S₀ i)]
    refine ⟨hφeq ▸ isTwist_st N q κ S₀ (Sum.inl i), ?_⟩
    exact heckeH1_congr N κ rfl (XSt N q κ) hφeq _ _
  · refine Or.inr ⟨σ⁻¹, ?_⟩
    have hc := (conjHom_codRestrict_eq_conjTop N σ).symm
    have hφeq : φSt N q κ S₀ (Sum.inr σ) =
        ρSt' q κ ⟨((((σ⁻¹)⁻¹ : CongruenceSubgroup.Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
          Matrix (Fin 2) (Fin 2) ℤ), hΓ _ (σ⁻¹⁻¹).2⟩ := by
      change CuspidalType.steinbergRep q κ (red0 N q σ) = CuspidalType.steinbergRep q κ (toGLq q ⟨_, _⟩)
      rw [toGLq_sl, inv_inv]
      rfl
    have hψ : HeckeCohomology.IsTwist ⊤ ⊤
        (((CohCarrier.conjHom N ⊥ σ⁻¹).comp (⊤ : Subgroup ↥(CohCarrier.GammaH N ⊥)).subtype).codRestrict ⊤
          fun _ => Subgroup.mem_top _)
        (XSt N q κ) (ρSt' q κ ⟨((((σ⁻¹)⁻¹ : CongruenceSubgroup.Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
          Matrix (Fin 2) (Fin 2) ℤ), hΓ _ (σ⁻¹⁻¹).2⟩) := by
      rw [conjHom_codRestrict_eq_conjTop, ← hφeq]
      exact isTwist_st N q κ S₀ (Sum.inr σ)
    exact ⟨hψ, heckeH1_congr N κ hc (XSt N q κ) hφeq _ _⟩

end HComm
p2m_reactivate "P2MW.S_CohCarrier_exists_diamondRaw_eq_heckeT_eq_smul_gammaH_bot_mul_or_eisenstein_of_isEigensystemH1_of_steinberg_quotient_of_four_le.RepSES"

end K3aDock
p2m_reactivate "P2MW.S_CohCarrier_exists_diamondRaw_eq_heckeT_eq_smul_gammaH_bot_mul_or_eisenstein_of_isEigensystemH1_of_steinberg_quotient_of_four_le.RepSES P2MW.S_CohCarrier_exists_diamondRaw_eq_heckeT_eq_smul_gammaH_bot_mul_or_eisenstein_of_isEigensystemH1_of_steinberg_quotient_of_four_le.K3aDock"

set_option linter.unusedVariables false in
open CongruenceSubgroup in

theorem solution
    (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N) (S₀ : Set ℕ)
    (hN4 : 4 ≤ N)
    (κ : Type) [Field κ] (hq1 : (q : κ) + 1 = 0) (h2 : (2 : κ) ≠ 0)
    {V : Type} [AddCommGroup V] [Module κ V] [FiniteDimensional κ V]
    (ρ : Representation κ (CuspidalType.GL2 q) V)
    (π : ↥(CuspidalType.steinberg q κ).toSubmodule →ₗ[κ] V)
    (hπ : ∀ g : CuspidalType.GL2 q, ∀ v : ↥(CuspidalType.steinberg q κ).toSubmodule,
      π ⟨CuspidalType.ind q κ g v, (CuspidalType.steinberg q κ).apply_mem_toSubmodule g v.2⟩ = ρ g (π v))
    (hπsurj : Function.Surjective π)
    (hπker : ∀ v : ↥(CuspidalType.steinberg q κ).toSubmodule, π v = 0 ↔ ∃ c : κ, (v : CuspidalType.ProjLine q →₀ κ) = c • CuspidalType.constFun q κ)
    (lam : ℕ → κ)
    (hocc : HeckeEis.IsEigensystemH1 N (ρ.comp ((Matrix.SpecialLinearGroup.toGL.comp
            (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype))
      (fun ℓ : ℕ =>
        if h : ((ℓ : ZMod q) ≠ 0) then ρ (CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) h)) else LinearMap.id)
      (insert q S₀) lam) :
    haveI : NeZero (N * q) := ⟨Nat.mul_ne_zero (NeZero.ne N) (Fact.out : q.Prime).ne_zero⟩
    (∃ v : CohCarrier.H1 (N * q) ⊥ κ, v ≠ 0 ∧
      (∀ σ : CongruenceSubgroup.Gamma0 (N * q), CohCarrier.diamondRaw (N * q) ⊥ κ σ v = v) ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N * q → ℓ ∉ S₀ →
        haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
        CohCarrier.heckeT (N * q) ⊥ ℓ κ v = lam ℓ • v) ∨
      ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ insert q S₀ → lam ℓ = (ℓ : κ) + 1 := by
  obtain ⟨Φ, hbij, hlin, hdia, hhecke⟩ :=
    HeckeCohomology.exists_shapiro_ind_ker_unitsMap_bijective_linear_and_conjHom_eq_diamondRaw_and_heckeH1_eq_heckeT
      N q hqN κ (K3aDock.liftNq N q) (fun _ => rfl)
  exact K3aDock.dock_core N q hqN S₀ hN4 κ hq1 h2 ρ π hπ hπsurj hπker lam hocc (K3aDock.hcomm_st N q κ S₀)
    (K3aDock.d3_of_shapiro N q κ S₀ lam hqN hq1 h2 Φ hlin hbij hdia hhecke)

end S_CohCarrier_exists_diamondRaw_eq_heckeT_eq_smul_gammaH_bot_mul_or_eisenstein_of_isEigensystemH1_of_steinberg_quotient_of_four_le
end P2MW
export P2MW.S_CohCarrier_exists_diamondRaw_eq_heckeT_eq_smul_gammaH_bot_mul_or_eisenstein_of_isEigensystemH1_of_steinberg_quotient_of_four_le (solution)
