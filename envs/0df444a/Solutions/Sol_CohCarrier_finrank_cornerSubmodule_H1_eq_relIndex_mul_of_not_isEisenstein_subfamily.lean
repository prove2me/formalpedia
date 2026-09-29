-- Prove2me | solution 1 for CohCarrier.finrank_cornerSubmodule_H1_eq_relIndex_mul_of_not_isEisenstein_subfamily
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/4a4873f7-e671-5b29-aa42-9552c37822ee

import Mathlib
import Definitions.Def_CohCarrier_SubfamilyHeckeData
import Definitions.Def_IharaLemma_IdempotentSplitting
import Theorems.Thm_CohCarrier_surjective_jDeg_one_and_jDeg_eq_zero_iff_of_four_le
import Theorems.Thm_CohCarrier_map_jDegL_one_cornerSubmodule_eq_and_exists_algHom_cornerRing_subfamily
import Theorems.Thm_CohCarrier_exists_iDeg_eq_heckeT_sub_smul_of_forall_diamondRaw_eq
import Theorems.Thm_Representation_finrank_eq_card_mul_finrank_coinvariants_of_isPGroup
import Theorems.Thm_CohCarrier_H1_moduleFinite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_finrank_cornerSubmodule_H1_eq_relIndex_mul_of_not_isEisenstein_subfamily

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups

noncomputable section

namespace RKRelIndexSubSol

open CohCarrier

section Groups

variable (L : ℕ) [NeZero L] (H H' : Subgroup (ZMod L)ˣ)

theorem levelLE (hHH' : H ≤ H') : LevelLE L L H' H 1 where
  dvd := dvd_rfl
  ddvd := one_dvd _
  red u hu := by
    rw [ZMod.unitsMap_self]
    exact hHH' hu

theorem conjLowerMat_one (A : SL(2, ℤ)) (h : ((1 : ℕ) : ℤ) ∣ A 1 0) :
    conjLowerMat 1 A h = A := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [conjLowerMat]

variable (h : LevelLE L L H' H 1)

theorem coe_iotaDeg_one (γ : ↥(GammaH L H)) :
    ((iotaDeg L L H' H 1 h γ : ↥(GammaH L H')) : SL(2, ℤ)) = γ :=
  conjLowerMat_one (γ : SL(2, ℤ)) (h.dvd_entry γ)

noncomputable def unitsChar : ↥(GammaH L H') →* (ZMod L)ˣ :=
  (gamma0Units L).comp (Subgroup.inclusion (GammaH_le_Gamma0 (M := L) H'))

theorem unitsChar_mem (γ : ↥(GammaH L H')) : unitsChar L H' γ ∈ H' := by
  obtain ⟨hγ0, hγH⟩ := mem_GammaH_iff.mp γ.2
  exact hγH

theorem exists_unitsChar_eq {u : (ZMod L)ˣ} (hu : u ∈ H') :
    ∃ γ : ↥(GammaH L H'), unitsChar L H' γ = u := by
  obtain ⟨σ, hσ⟩ := gamma0Units_surjective L u
  have hσ' : (σ : SL(2, ℤ)) ∈ GammaH L H' := by
    rw [mem_GammaH_iff]
    refine ⟨σ.2, ?_⟩
    have : (⟨(σ : SL(2, ℤ)), σ.2⟩ : Gamma0 L) = σ := Subtype.coe_eta _ _
    rw [this, hσ]
    exact hu
  refine ⟨⟨(σ : SL(2, ℤ)), hσ'⟩, ?_⟩
  rw [← hσ]
  rfl

def toGamma0 (g : ↥(GammaH L H')) : Gamma0 L := ⟨g, GammaH_le_Gamma0 H' g.2⟩

@[scoped simp] theorem coe_toGamma0 (g : ↥(GammaH L H')) : ((toGamma0 L H' g : Gamma0 L) : SL(2, ℤ)) = g :=
  rfl

theorem gamma0Units_toGamma0 (g : ↥(GammaH L H')) : gamma0Units L (toGamma0 L H' g) = unitsChar L H' g :=
  rfl

theorem range_iotaDeg_one_eq_comap :
    (iotaDeg L L H' H 1 h).range = H.comap (unitsChar L H') := by
  ext x
  constructor
  · rintro ⟨γ, rfl⟩
    obtain ⟨hγ0, hγH⟩ := mem_GammaH_iff.mp γ.2
    rw [Subgroup.mem_comap]
    have hx : (iotaDeg L L H' H 1 h γ : SL(2, ℤ)) = γ := coe_iotaDeg_one L H H' h γ
    have : unitsChar L H' (iotaDeg L L H' H 1 h γ) = gamma0Units L ⟨γ, hγ0⟩ := by
      show gamma0Units L ⟨(iotaDeg L L H' H 1 h γ : SL(2, ℤ)), _⟩ = _
      congr 1
      exact Subtype.ext hx
    rw [this]
    exact hγH
  · intro hx
    rw [Subgroup.mem_comap] at hx
    have hx0 : (x : SL(2, ℤ)) ∈ Gamma0 L := GammaH_le_Gamma0 H' x.2
    have hxH : (x : SL(2, ℤ)) ∈ GammaH L H := mem_GammaH_iff.mpr ⟨hx0, hx⟩
    refine ⟨⟨x, hxH⟩, Subtype.ext ?_⟩
    exact coe_iotaDeg_one L H H' h ⟨x, hxH⟩

scoped instance range_iotaDeg_one_normal : ((iotaDeg L L H' H 1 h).range).Normal := by
  rw [range_iotaDeg_one_eq_comap]
  infer_instance

noncomputable def unitsChar' : ↥(GammaH L H') →* ↥H' :=
  (unitsChar L H').codRestrict H' (unitsChar_mem L H')

theorem unitsChar'_surjective : Function.Surjective (unitsChar' L H') := by
  rintro ⟨u, hu⟩
  obtain ⟨γ, hγ⟩ := exists_unitsChar_eq L H' hu
  exact ⟨γ, Subtype.ext hγ⟩

theorem index_range_iotaDeg_one : (iotaDeg L L H' H 1 h).range.index = H.relIndex H' := by
  have : (iotaDeg L L H' H 1 h).range = (H.subgroupOf H').comap (unitsChar' L H') := by
    rw [range_iotaDeg_one_eq_comap]
    ext x
    simp only [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    rfl
  rw [this, Subgroup.index_comap_of_surjective _ (unitsChar'_surjective L H')]
  rfl

theorem mem_range_iff (x : ↥(GammaH L H')) :
    x ∈ (iotaDeg L L H' H 1 h).range ↔ unitsChar L H' x ∈ H := by
  rw [range_iotaDeg_one_eq_comap, Subgroup.mem_comap]

end Groups

section Res

variable (L : ℕ) [NeZero L] (H H' : Subgroup (ZMod L)ˣ) (h : LevelLE L L H' H 1)
variable (A : Type) [AddCommGroup A]

theorem pushChar_apply (φ : H1 L H A)
    (x : ↥((iotaDeg L L H' H 1 h).range)) (γ' : ↥(GammaH L H))
    (hx : (x : ↥(GammaH L H')) = iotaDeg L L H' H 1 h γ') :
    pushChar L L H' H 1 A h φ (Additive.ofMul x) = φ (Additive.ofMul γ') := by
  have hinj := iotaDeg_injective L L H' H 1 h
  have hsymm : (MonoidHom.ofInjective hinj).symm x = γ' := by
    apply (MonoidHom.ofInjective hinj).injective
    rw [MulEquiv.apply_symm_apply]
    exact Subtype.ext hx
  show φ (Additive.ofMul ((MonoidHom.ofInjective hinj).symm.toMonoidHom x)) = _
  rw [MulEquiv.coe_toMonoidHom, hsymm]

theorem iDeg'_injective [IsAddTorsionFree A] : Function.Injective (iDeg' L L H' H 1 A h) := by
  set K := (iotaDeg L L H' H 1 h).range with hK
  haveI : K.Normal := range_iotaDeg_one_normal L H H' h
  intro ψ₁ ψ₂ hψ
  rw [← sub_eq_zero] at hψ ⊢
  set ψ := ψ₁ - ψ₂ with hψdef
  have hres : iDeg' L L H' H 1 A h ψ = 0 := by
    rw [hψdef, map_sub, hψ]

  have hK0 : ∀ x : ↥(GammaH L H'), x ∈ K → ψ (Additive.ofMul x) = 0 := by
    rintro x ⟨γ, rfl⟩
    exact DFunLike.congr_fun hres (Additive.ofMul γ)
  refine AddMonoidHom.ext fun a => ?_
  set g := Additive.toMul a with hg
  have ha : a = Additive.ofMul g := (ofMul_toMul a).symm
  have hpow : g ^ K.index ∈ K := Subgroup.pow_index_mem K g
  have h1 : K.index • ψ (Additive.ofMul g) = 0 := by
    rw [← AddMonoidHom.map_nsmul, ← ofMul_pow]
    exact hK0 _ hpow
  have hidx : K.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  rw [ha, AddMonoidHom.zero_apply]
  refine (nsmul_right_injective hidx) ?_
  show K.index • ψ (Additive.ofMul g) = K.index • (0 : A)
  rw [h1, nsmul_zero]

end Res

section Diamond

variable (L : ℕ) [NeZero L] (H : Subgroup (ZMod L)ˣ) (A : Type) [AddCommGroup A]

theorem diamondRaw_apply (σ : Gamma0 L) (φ : H1 L H A) (a : Additive ↥(GammaH L H)) :
    diamondRaw L H A σ φ a = φ (Additive.ofMul (conjHom L H σ (Additive.toMul a))) := rfl

theorem diamondRaw_mul (σ τ : Gamma0 L) (φ : H1 L H A) :
    diamondRaw L H A (σ * τ) φ = diamondRaw L H A τ (diamondRaw L H A σ φ) := by
  refine AddMonoidHom.ext fun a => ?_
  simp only [diamondRaw_apply, toMul_ofMul]
  congr 2
  apply Subtype.ext
  simp only [conjHom, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_mul, mul_inv_rev]
  group

theorem diamondRaw_one (φ : H1 L H A) : diamondRaw L H A 1 φ = φ := by
  refine AddMonoidHom.ext fun a => ?_
  rw [diamondRaw_apply]
  congr 1
  have : conjHom L H 1 (Additive.toMul a) = Additive.toMul a := by
    apply Subtype.ext
    simp [conjHom]
  rw [this, ofMul_toMul]

theorem diamondRaw_eq_self_of_mem (σ : Gamma0 L) (hσ : (σ : SL(2, ℤ)) ∈ GammaH L H) (φ : H1 L H A) :
    diamondRaw L H A σ φ = φ := by
  set κ : ↥(GammaH L H) := ⟨(σ : SL(2, ℤ)), hσ⟩ with hκ
  refine AddMonoidHom.ext fun a => ?_
  rw [diamondRaw_apply]
  have hconj : conjHom L H σ (Additive.toMul a) = κ * Additive.toMul a * κ⁻¹ := by
    apply Subtype.ext
    simp [conjHom, hκ]
  rw [hconj, ofMul_mul, ofMul_mul, ofMul_inv, map_add, map_add, map_neg, ofMul_toMul]
  abel

end Diamond

section Hecke

open scoped IsMulCommutative

variable (L : ℕ) [NeZero L] (S : Set ℕ) (H H' : Subgroup (ZMod L)ˣ)
  (𝒪 : Type) [CommRing 𝒪] (k : Type) [Field k] [Algebra 𝒪 k]
  {G : Type} (fam : G → Gen L S) (dG : ↥H' → G)
  (hdG : ∀ u : ↥H', fam (dG u) = Gen.dia (u : (ZMod L)ˣ))
  (hcomm : ∀ g g' : G,
      opFamily L H S 𝒪 (fam g) * opFamily L H S 𝒪 (fam g') = opFamily L H S 𝒪 (fam g') * opFamily L H S 𝒪 (fam g))
  (θbar : G → k)

local notation3 "𝕋" => (CohCarrier.hdataSub L H S 𝒪 k fam hcomm θbar).opSubalgebra

noncomputable def gOp (g : G) : ↥𝕋 :=
  ⟨(hdataSub L H S 𝒪 k fam hcomm θbar).op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩

@[scoped simp] theorem coe_gOp (g : G) :
    ((gOp L S H 𝒪 k fam hcomm θbar g : ↥𝕋) : Module.End 𝒪 (H1 L H 𝒪)) = opFamily L H S 𝒪 (fam g) := rfl

noncomputable def dOp (u : ↥H') : ↥𝕋 := gOp L S H 𝒪 k fam hcomm θbar (dG u)

include hdG in
theorem coe_dOp (u : ↥H') :
    ((dOp L S H H' 𝒪 k fam dG hcomm θbar u : ↥𝕋) : Module.End 𝒪 (H1 L H 𝒪)) = diamondL L H 𝒪 u := by
  show opFamily L H S 𝒪 (fam (dG u)) = diamondL L H 𝒪 u
  rw [hdG u]
  rfl

include hdG in
theorem dOp_apply (u : ↥H') (m : H1 L H 𝒪) :
    ((dOp L S H H' 𝒪 k fam dG hcomm θbar u : ↥𝕋) : Module.End 𝒪 (H1 L H 𝒪)) m = diamondL L H 𝒪 u m := by
  rw [coe_dOp L S H H' 𝒪 k fam dG hdG hcomm θbar u]

theorem subalg_smul_def (b : ↥𝕋) (m : H1 L H 𝒪) :
    b • m = (b : Module.End 𝒪 (H1 L H 𝒪)) m := rfl

include hdG in
theorem dOp_mul (u v : ↥H') :
    dOp L S H H' 𝒪 k fam dG hcomm θbar (u * v) =
      dOp L S H H' 𝒪 k fam dG hcomm θbar u * dOp L S H H' 𝒪 k fam dG hcomm θbar v := by
  obtain ⟨σ, hσ⟩ := gamma0Units_surjective L (u : (ZMod L)ˣ)
  obtain ⟨τ, hτ⟩ := gamma0Units_surjective L (v : (ZMod L)ˣ)

  have hvu : dOp L S H H' 𝒪 k fam dG hcomm θbar (u * v) =
      dOp L S H H' 𝒪 k fam dG hcomm θbar v * dOp L S H H' 𝒪 k fam dG hcomm θbar u := by
    apply Subtype.ext
    rw [Subalgebra.coe_mul, coe_dOp L S H H' 𝒪 k fam dG hdG hcomm θbar,
      coe_dOp L S H H' 𝒪 k fam dG hdG hcomm θbar, coe_dOp L S H H' 𝒪 k fam dG hdG hcomm θbar,
      Subgroup.coe_mul]
    refine LinearMap.ext fun φ => ?_
    rw [Module.End.mul_apply,
      diamondL_eq_diamondRaw L H 𝒪 ((u : (ZMod L)ˣ) * v) (σ * τ) (by rw [map_mul, hσ, hτ]) φ,
      diamondL_eq_diamondRaw L H 𝒪 (u : (ZMod L)ˣ) σ hσ φ, diamondL_eq_diamondRaw L H 𝒪 (v : (ZMod L)ˣ) τ hτ]
    exact diamondRaw_mul L H 𝒪 σ τ φ
  rw [hvu]
  apply Subtype.ext
  rw [Subalgebra.coe_mul, Subalgebra.coe_mul]
  exact hcomm (dG v) (dG u)

include hdG in
theorem dOp_one : dOp L S H H' 𝒪 k fam dG hcomm θbar 1 = 1 := by
  apply Subtype.ext
  rw [coe_dOp L S H H' 𝒪 k fam dG hdG hcomm θbar, Subalgebra.coe_one]
  refine LinearMap.ext fun φ => ?_
  rw [diamondL_eq_diamondRaw L H 𝒪 ((1 : ↥H') : (ZMod L)ˣ) 1 (by rw [map_one, OneMemClass.coe_one]) φ,
    diamondRaw_one]
  rfl

include hdG in

theorem dOp_eq_one_of_mem {u : ↥H'} (hu : (u : (ZMod L)ˣ) ∈ H) :
    dOp L S H H' 𝒪 k fam dG hcomm θbar u = 1 := by
  obtain ⟨σ, hσ⟩ := gamma0Units_surjective L (u : (ZMod L)ˣ)
  have hσH : (σ : SL(2, ℤ)) ∈ GammaH L H := by
    rw [mem_GammaH_iff]
    refine ⟨σ.2, ?_⟩
    have : (⟨(σ : SL(2, ℤ)), σ.2⟩ : Gamma0 L) = σ := Subtype.coe_eta _ _
    rw [this, hσ]
    exact hu
  apply Subtype.ext
  rw [coe_dOp L S H H' 𝒪 k fam dG hdG hcomm θbar, Subalgebra.coe_one]
  refine LinearMap.ext fun φ => ?_
  rw [diamondL_eq_diamondRaw L H 𝒪 (u : (ZMod L)ˣ) σ hσ φ, diamondRaw_eq_self_of_mem L H 𝒪 σ hσH]
  rfl

noncomputable def dHom : ↥H' →* ↥𝕋 where
  toFun := dOp L S H H' 𝒪 k fam dG hcomm θbar
  map_one' := dOp_one L S H H' 𝒪 k fam dG hdG hcomm θbar
  map_mul' := dOp_mul L S H H' 𝒪 k fam dG hdG hcomm θbar

@[scoped simp] theorem dHom_apply (u : ↥H') :
    dHom L S H H' 𝒪 k fam dG hdG hcomm θbar u = dOp L S H H' 𝒪 k fam dG hcomm θbar u :=
  rfl

variable (Sp : IharaLemma.IdempotentSplitting ↥(CohCarrier.hdataSub L H S 𝒪 k fam hcomm θbar).opSubalgebra)
  (i₀ : Fin Sp.n)

abbrev Pcs : Submodule 𝒪 (H1 L H 𝒪) :=
  (IharaLemma.cornerSubmodule (M := H1 L H 𝒪) (Sp.e i₀)).restrictScalars 𝒪

abbrev Pc : Type := ↥(Pcs L S H 𝒪 k fam hcomm θbar Sp i₀)

local notation3 "PPs" => Pcs L S H 𝒪 k fam hcomm θbar Sp i₀
local notation3 "PP" => Pc L S H 𝒪 k fam hcomm θbar Sp i₀

theorem mem_corner (m : PP) : (m : H1 L H 𝒪) ∈ IharaLemma.cornerSubmodule (M := H1 L H 𝒪) (Sp.e i₀) := m.2

noncomputable def actP (b : ↥𝕋) : PP →ₗ[𝒪] PP where
  toFun m := ⟨(b : Module.End 𝒪 (H1 L H 𝒪)) m,
    (IharaLemma.cornerSubmodule (M := H1 L H 𝒪) (Sp.e i₀)).smul_mem b (mem_corner L S H 𝒪 k fam hcomm θbar Sp i₀ m)⟩
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' r m := Subtype.ext (LinearMap.map_smul _ r _)

theorem coe_actP_apply (b : ↥𝕋) (m : PP) :
    ((actP L S H 𝒪 k fam hcomm θbar Sp i₀ b m : PP) : H1 L H 𝒪) = (b : Module.End 𝒪 (H1 L H 𝒪)) m := rfl

noncomputable def actPHom : ↥𝕋 →* Module.End 𝒪 PP where
  toFun := actP L S H 𝒪 k fam hcomm θbar Sp i₀
  map_one' := LinearMap.ext fun m => Subtype.ext (by rw [coe_actP_apply, Subalgebra.coe_one]; rfl)
  map_mul' b c := LinearMap.ext fun m => Subtype.ext (by
    rw [coe_actP_apply, Subalgebra.coe_mul]; rfl)

variable (h : LevelLE L L H' H 1)

noncomputable def rho0 : ↥(GammaH L H') →* Module.End 𝒪 PP :=
  (actPHom L S H 𝒪 k fam hcomm θbar Sp i₀).comp
    ((dHom L S H H' 𝒪 k fam dG hdG hcomm θbar).comp (unitsChar' L H'))

theorem rho0_apply_coe (x : ↥(GammaH L H')) (m : PP) :
    ((rho0 L S H H' 𝒪 k fam dG hdG hcomm θbar Sp i₀ x m : PP) : H1 L H 𝒪) =
      diamondL L H 𝒪 (unitsChar L H' x) (m : H1 L H 𝒪) := by
  show ((dOp L S H H' 𝒪 k fam dG hcomm θbar (unitsChar' L H' x) : ↥𝕋) : Module.End 𝒪 (H1 L H 𝒪)) m = _
  rw [coe_dOp L S H H' 𝒪 k fam dG hdG hcomm θbar]
  rfl

theorem range_le_ker_rho0 :
    (iotaDeg L L H' H 1 h).range ≤ (rho0 L S H H' 𝒪 k fam dG hdG hcomm θbar Sp i₀).ker := by
  intro x hx
  rw [mem_range_iff] at hx
  rw [MonoidHom.mem_ker]
  show actPHom L S H 𝒪 k fam hcomm θbar Sp i₀
    (dHom L S H H' 𝒪 k fam dG hdG hcomm θbar (unitsChar' L H' x)) = 1
  rw [dHom_apply, dOp_eq_one_of_mem L S H H' 𝒪 k fam dG hdG hcomm θbar hx, map_one]

abbrev Delta : Type := ↥(GammaH L H') ⧸ (iotaDeg L L H' H 1 h).range

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

noncomputable def rho : Representation 𝒪 (Delta L H H' h) PP :=
  QuotientGroup.lift _ (rho0 L S H H' 𝒪 k fam dG hdG hcomm θbar Sp i₀)
    (range_le_ker_rho0 L S H H' 𝒪 k fam dG hdG hcomm θbar Sp i₀ h)

theorem rho_mk (x : ↥(GammaH L H')) :
    rho L S H H' 𝒪 k fam dG hdG hcomm θbar Sp i₀ h (QuotientGroup.mk x) =
      rho0 L S H H' 𝒪 k fam dG hdG hcomm θbar Sp i₀ x :=
  QuotientGroup.lift_mk _ _ x

theorem rho_mk_apply_coe (x : ↥(GammaH L H')) (m : PP) :
    ((rho L S H H' 𝒪 k fam dG hdG hcomm θbar Sp i₀ h (QuotientGroup.mk x) m : PP) : H1 L H 𝒪) =
      diamondRaw L H 𝒪 (toGamma0 L H' x) (m : H1 L H 𝒪) := by
  rw [rho_mk, rho0_apply_coe]
  exact diamondL_eq_diamondRaw L H 𝒪 (unitsChar L H' x) (toGamma0 L H' x) rfl _

theorem rho_mk_apply_coe' (x : ↥(GammaH L H')) (m : PP) :
    ((rho L S H H' 𝒪 k fam dG hdG hcomm θbar Sp i₀ h (QuotientGroup.mk x) m : PP) : H1 L H 𝒪) =
      ((dOp L S H H' 𝒪 k fam dG hcomm θbar (unitsChar' L H' x) : ↥𝕋) : Module.End 𝒪 (H1 L H 𝒪))
        (m : H1 L H 𝒪) := by
  rw [rho_mk]; rfl

noncomputable def rep (q : Delta L H H' h) : ↥(GammaH L H') :=
  ((default : ((iotaDeg L L H' H 1 h).range).LeftTransversal).2.leftQuotientEquiv q : ↥(GammaH L H'))

theorem mk_rep (q : Delta L H H' h) : (QuotientGroup.mk (rep L H H' h q) : Delta L H H' h) = q :=
  Subgroup.IsComplement.quotientGroupMk_leftQuotientEquiv _ q

theorem transfer_apply_of_normal {G₀ : Type} [Group G₀] (K : Subgroup G₀) [K.FiniteIndex]
    [hK : K.Normal] {C : Type} [CommGroup C] (ψ : K →* C) (g : K) :
    MonoidHom.transfer ψ g =
      ∏ q : G₀ ⧸ K, ψ ⟨((default : K.LeftTransversal).2.leftQuotientEquiv q : G₀)⁻¹ * g *
          ((default : K.LeftTransversal).2.leftQuotientEquiv q : G₀), hK.conj_mem' _ g.2 _⟩ := by
  classical
  set T : K.LeftTransversal := default with hT
  rw [MonoidHom.transfer_def ψ T g]
  simp only [Subgroup.leftTransversals.diff]
  refine Finset.prod_congr rfl fun q _ => ?_
  set α : G₀ ⧸ K → G₀ := fun q => (T.2.leftQuotientEquiv q : G₀) with hα
  have hq : (g : G₀)⁻¹ • q = q := by
    induction q using QuotientGroup.induction_on with
    | H x =>
      rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, smul_eq_mul]
      have : ((g : G₀)⁻¹ * x)⁻¹ * x = x⁻¹ * g * x := by group
      rw [this]
      exact hK.conj_mem' _ g.2 x
  have hβ : (((g : G₀) • T).2.leftQuotientEquiv q : G₀) = g * α q := by
    rw [Subgroup.smul_apply_eq_smul_apply_inv_smul, hq]
    rfl
  congr 1
  apply Subtype.ext
  show (α q)⁻¹ * (((g : G₀) • T).2.leftQuotientEquiv q : G₀) = (α q)⁻¹ * g * α q
  rw [hβ, mul_assoc]

theorem iotaDeg_conjHom_inv (t : ↥(GammaH L H')) (γ : ↥(GammaH L H)) :
    iotaDeg L L H' H 1 h (conjHom L H (toGamma0 L H' t)⁻¹ γ) = t⁻¹ * iotaDeg L L H' H 1 h γ * t := by
  apply Subtype.ext
  rw [coe_iotaDeg_one]
  simp only [Subgroup.coe_mul, InvMemClass.coe_inv, coe_iotaDeg_one]
  show ((toGamma0 L H' t)⁻¹ : Gamma0 L) * (γ : SL(2, ℤ)) * (((toGamma0 L H' t)⁻¹ : Gamma0 L) : SL(2, ℤ))⁻¹ = _
  simp only [InvMemClass.coe_inv, coe_toGamma0, inv_inv]

theorem iDeg'_jDeg_apply (m : H1 L H 𝒪) (γ : ↥(GammaH L H)) :
    iDeg' L L H' H 1 𝒪 h (jDeg L L H' H 1 𝒪 h m) (Additive.ofMul γ) =
      ∑ q : Delta L H H' h, diamondRaw L H 𝒪 (toGamma0 L H' (rep L H H' h q))⁻¹ m (Additive.ofMul γ) := by
  set K := (iotaDeg L L H' H 1 h).range with hK
  set ψa := pushChar L L H' H 1 𝒪 h m with hψa
  set κ : K := ⟨iotaDeg L L H' H 1 h γ, γ, rfl⟩ with hκ
  have hL : iDeg' L L H' H 1 𝒪 h (jDeg L L H' H 1 𝒪 h m) (Additive.ofMul γ) =
      Additive.toMul.symm ((MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight ψa))
        (κ : ↥(GammaH L H'))) := rfl
  rw [hL, transfer_apply_of_normal K (AddMonoidHom.toMultiplicativeRight ψa) κ]
  rw [show (Additive.toMul.symm : Multiplicative 𝒪 → 𝒪) = Multiplicative.toAdd from rfl, toAdd_prod]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [AddMonoidHom.toMultiplicativeRight_apply_apply, toAdd_ofAdd, diamondRaw_apply, toMul_ofMul]
  refine pushChar_apply L H H' h 𝒪 m _ _ ?_
  rw [iotaDeg_conjHom_inv]
  rfl

noncomputable def normOp : ↥𝕋 :=
  ∑ q : Delta L H H' h, dHom L S H H' 𝒪 k fam dG hdG hcomm θbar ((unitsChar' L H' (rep L H H' h q))⁻¹)

theorem normOp_apply (m : H1 L H 𝒪) :
    ((normOp L S H H' 𝒪 k fam dG hdG hcomm θbar h : ↥𝕋) : Module.End 𝒪 (H1 L H 𝒪)) m =
      iDeg' L L H' H 1 𝒪 h (jDeg L L H' H 1 𝒪 h m) := by
  refine AddMonoidHom.ext fun a => ?_
  obtain ⟨γ, rfl⟩ : ∃ γ, Additive.ofMul γ = a := ⟨Additive.toMul a, ofMul_toMul a⟩
  rw [iDeg'_jDeg_apply, normOp, AddSubmonoidClass.coe_finsetSum, LinearMap.sum_apply, AddMonoidHom.finsetSum_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hlift : gamma0Units L (toGamma0 L H' (rep L H H' h q))⁻¹ =
      (((unitsChar' L H' (rep L H H' h q))⁻¹ : ↥H') : (ZMod L)ˣ) := by
    rw [map_inv, InvMemClass.coe_inv]; rfl
  rw [dHom_apply, dOp_apply L S H H' 𝒪 k fam dG hdG hcomm θbar, diamondL_eq_diamondRaw L H 𝒪 _ _ hlift]

theorem coe_norm_apply (m : PP) :
    (((rho L S H H' 𝒪 k fam dG hdG hcomm θbar Sp i₀ h).norm m : PP) : H1 L H 𝒪) =
      ((normOp L S H H' 𝒪 k fam dG hdG hcomm θbar h : ↥𝕋) : Module.End 𝒪 (H1 L H 𝒪)) (m : H1 L H 𝒪) := by
  rw [Representation.norm, LinearMap.sum_apply, Submodule.coe_sum, normOp, AddSubmonoidClass.coe_finsetSum,
    LinearMap.sum_apply]

  rw [← Fintype.sum_equiv (Equiv.inv (Delta L H H' h))
    (fun q => ((rho L S H H' 𝒪 k fam dG hdG hcomm θbar Sp i₀ h q⁻¹ m : PP) : H1 L H 𝒪))
    (fun q => ((rho L S H H' 𝒪 k fam dG hdG hcomm θbar Sp i₀ h q m : PP) : H1 L H 𝒪)) (fun q => rfl)]
  refine Finset.sum_congr rfl fun q _ => ?_
  conv_lhs => rw [← mk_rep L H H' h q, ← QuotientGroup.mk_inv, rho_mk_apply_coe']
  rw [map_inv, dHom_apply]

theorem norm_eq_zero_iff [CharZero 𝒪] [IsDomain 𝒪] (v : PP) :
    (rho L S H H' 𝒪 k fam dG hdG hcomm θbar Sp i₀ h).norm v = 0 ↔ jDeg L L H' H 1 𝒪 h (v : H1 L H 𝒪) = 0 := by
  rw [← Submodule.coe_eq_zero, coe_norm_apply, normOp_apply]
  constructor
  · intro h0
    exact iDeg'_injective L H H' h 𝒪 (by rw [h0, map_zero])
  · intro h0
    rw [h0, map_zero]

theorem diamondRaw_eq_of_invariant (w : PP)
    (hw : ∀ g : Delta L H H' h, rho L S H H' 𝒪 k fam dG hdG hcomm θbar Sp i₀ h g w = w)
    (σ : Gamma0 L) (hσ : (σ : SL(2, ℤ)) ∈ GammaH L H') :
    diamondRaw L H 𝒪 σ (w : H1 L H 𝒪) = w := by
  have := congrArg (fun x : PP => (x : H1 L H 𝒪)) (hw (QuotientGroup.mk ⟨(σ : SL(2, ℤ)), hσ⟩))
  beta_reduce at this
  rw [rho_mk_apply_coe] at this
  convert this using 2
  exact congrArg (diamondRaw L H 𝒪) (Subtype.ext rfl)

def incl : PP →ₗ[𝒪] H1 L H 𝒪 where
  toFun m := (m : H1 L H 𝒪)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[scoped simp] theorem incl_apply (m : PP) : incl L S H 𝒪 k fam hcomm θbar Sp i₀ m = (m : H1 L H 𝒪) := rfl

theorem incl_injective : Function.Injective (incl L S H 𝒪 k fam hcomm θbar Sp i₀) :=
  fun _ _ hxy => Subtype.ext hxy

theorem span_kernelGens_le_map :
    Submodule.span 𝒪 {y : H1 L H 𝒪 | ∃ u ∈ H', ∃ x ∈ IharaLemma.cornerSubmodule (M := H1 L H 𝒪) (Sp.e i₀),
        y = diamondL L H 𝒪 u x - x} ≤
      Submodule.map (incl L S H 𝒪 k fam hcomm θbar Sp i₀)
        (Representation.Coinvariants.ker (rho L S H H' 𝒪 k fam dG hdG hcomm θbar Sp i₀ h)) := by
  rw [Submodule.span_le]
  rintro y ⟨u, hu, x, hx, rfl⟩
  obtain ⟨σ, hσ⟩ := exists_unitsChar_eq L H' hu
  refine ⟨rho L S H H' 𝒪 k fam dG hdG hcomm θbar Sp i₀ h (QuotientGroup.mk σ) ⟨x, hx⟩ - ⟨x, hx⟩,
    Representation.Coinvariants.sub_mem_ker _ _, ?_⟩
  rw [map_sub, incl_apply, incl_apply, rho_mk_apply_coe', dOp_apply L S H H' 𝒪 k fam dG hdG hcomm θbar]
  show diamondL L H 𝒪 (unitsChar L H' σ) x - x = _
  rw [hσ]

theorem jDeg_eq_zero_of_mem_ker
    (hW2 : ∀ m : H1 L H 𝒪, m ∈ IharaLemma.cornerSubmodule (M := H1 L H 𝒪) (Sp.e i₀) →
      (jDegL L L H' H 1 𝒪 𝒪 h m = 0 ↔
        m ∈ Submodule.span 𝒪 {y : H1 L H 𝒪 | ∃ u ∈ H',
          ∃ x ∈ IharaLemma.cornerSubmodule (M := H1 L H 𝒪) (Sp.e i₀), y = diamondL L H 𝒪 u x - x}))
    (v : PP) (hv : v ∈ Representation.Coinvariants.ker (rho L S H H' 𝒪 k fam dG hdG hcomm θbar Sp i₀ h)) :
    jDegL L L H' H 1 𝒪 𝒪 h (v : H1 L H 𝒪) = 0 := by
  induction hv using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨g, x⟩, rfl⟩ := hy
    induction g using QuotientGroup.induction_on with
    | H σ =>
      rw [hW2 _ (Submodule.coe_mem _)]
      apply Submodule.subset_span
      refine ⟨unitsChar L H' σ, unitsChar_mem L H' σ, (x : H1 L H 𝒪), x.2, ?_⟩
      rw [Submodule.coe_sub, rho_mk_apply_coe', dOp_apply L S H H' 𝒪 k fam dG hdG hcomm θbar]
      rfl
  | zero => rw [Submodule.coe_zero, map_zero]
  | add x y _ _ hx hy => rw [Submodule.coe_add, map_add, hx, hy, add_zero]
  | smul r x _ hx =>
    have : ((r • x : PP) : H1 L H 𝒪) = r • (x : H1 L H 𝒪) := rfl
    rw [this, map_smul, hx, smul_zero]

theorem mem_ker_of_norm_eq_zero [CharZero 𝒪] [IsDomain 𝒪]
    (hW2 : ∀ m : H1 L H 𝒪, m ∈ IharaLemma.cornerSubmodule (M := H1 L H 𝒪) (Sp.e i₀) →
      (jDegL L L H' H 1 𝒪 𝒪 h m = 0 ↔
        m ∈ Submodule.span 𝒪 {y : H1 L H 𝒪 | ∃ u ∈ H',
          ∃ x ∈ IharaLemma.cornerSubmodule (M := H1 L H 𝒪) (Sp.e i₀), y = diamondL L H 𝒪 u x - x}))
    (v : PP) (hv : (rho L S H H' 𝒪 k fam dG hdG hcomm θbar Sp i₀ h).norm v = 0) :
    v ∈ Representation.Coinvariants.ker (rho L S H H' 𝒪 k fam dG hdG hcomm θbar Sp i₀ h) := by
  rw [norm_eq_zero_iff] at hv
  have hv' : jDegL L L H' H 1 𝒪 𝒪 h (v : H1 L H 𝒪) = 0 := hv
  rw [hW2 _ v.2] at hv'
  obtain ⟨w, hw, hwv⟩ := span_kernelGens_le_map L S H H' 𝒪 k fam dG hdG hcomm θbar Sp i₀ h hv'
  have : w = v := incl_injective L S H 𝒪 k fam hcomm θbar Sp i₀ hwv
  rwa [← this]

def chi (πk : Sp.CornerRing i₀ →ₐ[𝒪] k) : ↥𝕋 →+* k :=
  πk.toRingHom.comp (Sp.toCornerRing i₀)

theorem chi_apply (πk : Sp.CornerRing i₀ →ₐ[𝒪] k) (b : ↥𝕋) :
    chi L S H 𝒪 k fam hcomm θbar Sp i₀ πk b = πk (Sp.toCornerRing i₀ b) := rfl

theorem toCornerRing_e : Sp.toCornerRing i₀ (Sp.e i₀) = 1 := by
  apply Subtype.ext
  show Sp.e i₀ * Sp.e i₀ * Sp.e i₀ = Sp.e i₀
  rw [(Sp.idem i₀).eq, (Sp.idem i₀).eq]

theorem ker_chi_eq (πk : Sp.CornerRing i₀ →ₐ[𝒪] k) (hk : Function.Surjective (algebraMap 𝒪 k)) :
    RingHom.ker (chi L S H 𝒪 k fam hcomm θbar Sp i₀ πk) = Sp.𝔪 i₀ := by
  have hsurj : Function.Surjective (chi L S H 𝒪 k fam hcomm θbar Sp i₀ πk) := by
    intro c
    obtain ⟨r, rfl⟩ := hk c
    refine ⟨algebraMap 𝒪 _ r, ?_⟩
    rw [chi_apply]
    exact πk.commutes r
  have hmax := RingHom.ker_isMaximal_of_surjective _ hsurj
  obtain ⟨j, hj⟩ := Sp.exists_eq _ hmax
  have hji : j = i₀ := by
    by_contra hne
    have hmem : Sp.e i₀ ∈ Sp.𝔪 j := (Sp.mem_iff i₀ j).mpr (Ne.symm hne)
    rw [hj, RingHom.mem_ker, chi_apply, toCornerRing_e, map_one] at hmem
    exact one_ne_zero hmem
  rw [← hj, hji]

theorem exists_mul_mul_e_eq (πk : Sp.CornerRing i₀ →ₐ[𝒪] k) (hk : Function.Surjective (algebraMap 𝒪 k))
    (b : ↥𝕋) (hb : πk (Sp.toCornerRing i₀ b) ≠ 0) : ∃ t : ↥𝕋, t * b * Sp.e i₀ = Sp.e i₀ := by
  have hb' : b ∉ Sp.𝔪 i₀ := by
    rw [← ker_chi_eq L S H 𝒪 k fam hcomm θbar Sp i₀ πk hk, RingHom.mem_ker]
    exact hb
  exact IharaLemma.exists_mul_mul_eq_of_notMem (Sp.idem i₀) (Sp.𝔪 i₀) (Sp.mem_of_isMaximal_of_ne i₀) hb'

variable [CharZero 𝒪] [IsDomain 𝒪]

theorem exists_norm_eq_of_invariant
    (hA : ∀ a : 𝒪, H.relIndex H' • a = 0 → a = 0)
    (r : ℕ) (hrL : r ∣ L) (hr : 4 ≤ r) (hH' : ∀ u ∈ H', ZMod.castHom hrL (ZMod r) (u : ZMod L) = 1)
    (πk : Sp.CornerRing i₀ →ₐ[𝒪] k) (hk : Function.Surjective (algebraMap 𝒪 k))
    (hπk : ∀ g : G, πk (Sp.toCornerRing i₀ (gOp L S H 𝒪 k fam hcomm θbar g)) = θbar g)
    (g₀ : G) (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ L)
    (hg₀ : fam g₀ = Gen.T ℓ hℓ hℓS hℓL)
    (hθ : θbar g₀ ≠ (ℓ : k) + 1)
    (w : PP) (hw : ∀ g : Delta L H H' h, rho L S H H' 𝒪 k fam dG hdG hcomm θbar Sp i₀ h g w = w) :
    ∃ m : PP, (rho L S H H' 𝒪 k fam dG hdG hcomm θbar Sp i₀ h).norm m = w := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩

  have hwM : ∀ σ : Gamma0 L, (σ : SL(2, ℤ)) ∈ GammaH L H' →
      diamondRaw L H 𝒪 σ (w : H1 L H 𝒪) = w :=
    diamondRaw_eq_of_invariant L S H H' 𝒪 k fam dG hdG hcomm θbar Sp i₀ h w hw

  obtain ⟨ψ, hψ⟩ := CohCarrier.exists_iDeg_eq_heckeT_sub_smul_of_forall_diamondRaw_eq L 𝒪 H H' h hA
    ℓ hℓ hℓL (w : H1 L H 𝒪) hwM
  obtain ⟨m₀, hm₀⟩ := (CohCarrier.surjective_jDeg_one_and_jDeg_eq_zero_iff_of_four_le L 𝒪 H H' h
    r hrL hr hH').1 ψ

  set c : 𝒪 := (ℓ : 𝒪) + 1 with hcdef
  set b : ↥𝕋 := gOp L S H 𝒪 k fam hcomm θbar g₀ - algebraMap 𝒪 (↥𝕋) c with hbdef
  have hb_coe : (b : Module.End 𝒪 (H1 L H 𝒪)) =
      opFamily L H S 𝒪 (fam g₀) - algebraMap 𝒪 (Module.End 𝒪 (H1 L H 𝒪)) c := by
    rw [hbdef, Subalgebra.coe_sub, coe_gOp, Subalgebra.coe_algebraMap]
  have hb_apply : ∀ x : H1 L H 𝒪, (b : Module.End 𝒪 (H1 L H 𝒪)) x = heckeT L H ℓ 𝒪 x - (ℓ + 1) • x := by
    intro x
    rw [hb_coe, LinearMap.sub_apply, Module.algebraMap_end_apply, hcdef, ← Nat.cast_succ,
      Nat.cast_smul_eq_nsmul, hg₀]
    rfl
  have hbN : (b : Module.End 𝒪 (H1 L H 𝒪)) (w : H1 L H 𝒪) =
      ((normOp L S H H' 𝒪 k fam dG hdG hcomm θbar h : ↥𝕋) : Module.End 𝒪 (H1 L H 𝒪)) m₀ := by
    rw [hb_apply, ← hψ, ← hm₀, normOp_apply]

  have hbval : πk (Sp.toCornerRing i₀ b) ≠ 0 := by
    have h1 : πk (Sp.toCornerRing i₀ (algebraMap 𝒪 (↥𝕋) c)) = (ℓ : k) + 1 := by
      have : πk (Sp.toCornerRing i₀ (algebraMap 𝒪 (↥𝕋) c)) = algebraMap 𝒪 k c := πk.commutes c
      rw [this, hcdef, map_add, map_natCast, map_one]
    have h2 : πk (Sp.toCornerRing i₀ b) = θbar g₀ - ((ℓ : k) + 1) := by
      have := (chi L S H 𝒪 k fam hcomm θbar Sp i₀ πk).map_sub (gOp L S H 𝒪 k fam hcomm θbar g₀)
        (algebraMap 𝒪 (↥𝕋) c)
      rw [chi_apply, chi_apply, chi_apply, hπk, h1] at this
      rw [hbdef]
      exact this
    rw [h2, sub_ne_zero]
    exact hθ
  obtain ⟨t, ht⟩ := exists_mul_mul_e_eq L S H 𝒪 k fam hcomm θbar Sp i₀ πk hk b hbval

  set e : ↥𝕋 := Sp.e i₀ with hedef
  set N : ↥𝕋 := normOp L S H H' 𝒪 k fam dG hdG hcomm θbar h with hNdef
  have hmem : (t : Module.End 𝒪 (H1 L H 𝒪)) ((e : Module.End 𝒪 (H1 L H 𝒪)) m₀) ∈
      IharaLemma.cornerSubmodule (M := H1 L H 𝒪) (Sp.e i₀) :=
    (IharaLemma.cornerSubmodule (M := H1 L H 𝒪) (Sp.e i₀)).smul_mem t
      (IharaLemma.toCorner (M := H1 L H 𝒪) (Sp.e i₀) m₀).2
  refine ⟨⟨(t : Module.End 𝒪 (H1 L H 𝒪)) ((e : Module.End 𝒪 (H1 L H 𝒪)) m₀), hmem⟩, ?_⟩
  apply Subtype.ext
  rw [coe_norm_apply]
  have hew : (e : Module.End 𝒪 (H1 L H 𝒪)) (w : H1 L H 𝒪) = w :=
    Sp.e_smul_coe i₀ ⟨(w : H1 L H 𝒪), mem_corner L S H 𝒪 k fam hcomm θbar Sp i₀ w⟩

  have hmul : ∀ (x y : ↥𝕋) (v : H1 L H 𝒪), (x : Module.End 𝒪 (H1 L H 𝒪)) ((y : Module.End 𝒪 (H1 L H 𝒪)) v)
      = ((x * y : ↥𝕋) : Module.End 𝒪 (H1 L H 𝒪)) v := fun x y v => rfl
  show (N : Module.End 𝒪 (H1 L H 𝒪)) ((t : Module.End 𝒪 (H1 L H 𝒪)) ((e : Module.End 𝒪 (H1 L H 𝒪)) m₀))
    = (w : H1 L H 𝒪)
  calc (N : Module.End 𝒪 (H1 L H 𝒪)) ((t : Module.End 𝒪 (H1 L H 𝒪)) ((e : Module.End 𝒪 (H1 L H 𝒪)) m₀))
      = ((t * e : ↥𝕋) : Module.End 𝒪 (H1 L H 𝒪)) ((N : Module.End 𝒪 (H1 L H 𝒪)) m₀) := by
        rw [hmul, hmul, hmul, show N * t * e = t * e * N from by ring]
    _ = ((t * e : ↥𝕋) : Module.End 𝒪 (H1 L H 𝒪))
          ((b : Module.End 𝒪 (H1 L H 𝒪)) ((e : Module.End 𝒪 (H1 L H 𝒪)) (w : H1 L H 𝒪))) := by
        rw [← hbN, hew]
    _ = ((t * b * e * e : ↥𝕋) : Module.End 𝒪 (H1 L H 𝒪)) (w : H1 L H 𝒪) := by
        rw [hmul, hmul, show t * e * b * e = t * b * e * e from by ring]
    _ = (w : H1 L H 𝒪) := by rw [ht, ← hmul, hew, hew]

theorem finrank_coinvariants_eq
    (Q : Submodule 𝒪 (H1 L H' 𝒪))
    (hW1 : Submodule.map (jDegL L L H' H 1 𝒪 𝒪 h) PPs = Q)
    (hW2 : ∀ m : H1 L H 𝒪, m ∈ IharaLemma.cornerSubmodule (M := H1 L H 𝒪) (Sp.e i₀) →
      (jDegL L L H' H 1 𝒪 𝒪 h m = 0 ↔
        m ∈ Submodule.span 𝒪 {y : H1 L H 𝒪 | ∃ u ∈ H',
          ∃ x ∈ IharaLemma.cornerSubmodule (M := H1 L H 𝒪) (Sp.e i₀), y = diamondL L H 𝒪 u x - x}))
    (h1 : ∀ v : PP, (rho L S H H' 𝒪 k fam dG hdG hcomm θbar Sp i₀ h).norm v = 0 →
      v ∈ Representation.Coinvariants.ker (rho L S H H' 𝒪 k fam dG hdG hcomm θbar Sp i₀ h)) :
    Module.finrank 𝒪 (Representation.Coinvariants (rho L S H H' 𝒪 k fam dG hdG hcomm θbar Sp i₀ h)) =
      Module.finrank 𝒪 ↥Q := by
  have hmemQ : ∀ m : PP, jDegL L L H' H 1 𝒪 𝒪 h (m : H1 L H 𝒪) ∈ Q := by
    intro m
    rw [← hW1]
    exact Submodule.mem_map_of_mem m.2
  let f : PP →ₗ[𝒪] ↥Q :=
    LinearMap.codRestrict Q ((jDegL L L H' H 1 𝒪 𝒪 h).comp (incl L S H 𝒪 k fam hcomm θbar Sp i₀)) hmemQ
  have hf_apply : ∀ m : PP, (f m : H1 L H' 𝒪) = jDegL L L H' H 1 𝒪 𝒪 h (m : H1 L H 𝒪) := fun m => rfl
  have hfsurj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    rw [← hW1] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, Subtype.ext rfl⟩
  have hker : Representation.Coinvariants.ker (rho L S H H' 𝒪 k fam dG hdG hcomm θbar Sp i₀ h) =
      LinearMap.ker f := by
    apply le_antisymm
    · intro v hv
      rw [LinearMap.mem_ker]
      apply Subtype.ext
      rw [hf_apply]
      exact jDeg_eq_zero_of_mem_ker L S H H' 𝒪 k fam dG hdG hcomm θbar Sp i₀ h hW2 v hv
    · intro v hv
      rw [LinearMap.mem_ker] at hv
      have hv' : jDegL L L H' H 1 𝒪 𝒪 h (v : H1 L H 𝒪) = 0 := by
        rw [← hf_apply, hv]; rfl
      apply h1
      rw [norm_eq_zero_iff]
      exact hv'
  exact ((Submodule.quotEquivOfEq _ _ hker).trans (f.quotKerEquivOfSurjective hfsurj)).finrank_eq

end Hecke

section Main

open scoped IsMulCommutative

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

theorem main
    (L : ℕ) [NeZero L] (S : Set ℕ)
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [CharZero 𝒪]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField 𝒪) p]
    (H H' : Subgroup (ZMod L)ˣ) (hHH' : H ≤ H') (hidx : ∃ n : ℕ, H.relIndex H' = p ^ n)
    (r : ℕ) (hrL : r ∣ L) (hr : 4 ≤ r)
    (hH' : ∀ u ∈ H', ZMod.castHom hrL (ZMod r) (u : ZMod L) = 1)
    {G : Type} (φ : G → CohCarrier.Gen L S)
    (dG : ↥H' → G) (hdG : ∀ u : ↥H', φ (dG u) = CohCarrier.Gen.dia (u : (ZMod L)ˣ))
    (hcomm : ∀ g g' : G,
      CohCarrier.opFamily L H S 𝒪 (φ g) * CohCarrier.opFamily L H S 𝒪 (φ g') =
        CohCarrier.opFamily L H S 𝒪 (φ g') * CohCarrier.opFamily L H S 𝒪 (φ g))
    (hcomm' : ∀ g g' : G,
      CohCarrier.opFamily L H' S 𝒪 (φ g) * CohCarrier.opFamily L H' S 𝒪 (φ g') =
        CohCarrier.opFamily L H' S 𝒪 (φ g') * CohCarrier.opFamily L H' S 𝒪 (φ g))
    (θbar : G → IsLocalRing.ResidueField 𝒪)
    (Sp : IharaLemma.IdempotentSplitting
      ↥(CohCarrier.hdataSub L H S 𝒪 (IsLocalRing.ResidueField 𝒪) φ hcomm θbar).opSubalgebra)
    (i₀ : Fin Sp.n) (πk : Sp.CornerRing i₀ →ₐ[𝒪] IsLocalRing.ResidueField 𝒪)
    (hπk : ∀ g : G, πk (Sp.toCornerRing i₀
      ⟨(CohCarrier.hdataSub L H S 𝒪 (IsLocalRing.ResidueField 𝒪) φ hcomm θbar).op g,
        Algebra.subset_adjoin (Set.mem_range_self g)⟩) = θbar g)
    (Sp' : IharaLemma.IdempotentSplitting
      ↥(CohCarrier.hdataSub L H' S 𝒪 (IsLocalRing.ResidueField 𝒪) φ hcomm' θbar).opSubalgebra)
    (i₀' : Fin Sp'.n) (πk' : Sp'.CornerRing i₀' →ₐ[𝒪] IsLocalRing.ResidueField 𝒪)
    (hπk' : ∀ g : G, πk' (Sp'.toCornerRing i₀'
      ⟨(CohCarrier.hdataSub L H' S 𝒪 (IsLocalRing.ResidueField 𝒪) φ hcomm' θbar).op g,
        Algebra.subset_adjoin (Set.mem_range_self g)⟩) = θbar g)
    (hEis : ∃ (g : G) (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ L),
      φ g = CohCarrier.Gen.T ℓ hℓ hℓS hℓL ∧ ℓ ≡ 1 [MOD L] ∧
        θbar g ≠ (ℓ : IsLocalRing.ResidueField 𝒪) + 1) :
    Module.finrank 𝒪 ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 L H 𝒪) (Sp.e i₀)) =
      H.relIndex H' *
        Module.finrank 𝒪 ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 L H' 𝒪) (Sp'.e i₀')) := by
  have h : LevelLE L L H' H 1 := levelLE L H H' hHH'

  obtain ⟨hW1, hW2, -⟩ :=
    CohCarrier.map_jDegL_one_cornerSubmodule_eq_and_exists_algHom_cornerRing_subfamily L S 𝒪
      H H' h r hrL hr hH' φ dG hdG hcomm hcomm' θbar Sp i₀ πk hπk Sp' i₀' πk' hπk'
  obtain ⟨g₀, ℓ, hℓ, hℓS, hℓL, hg₀, -, hθ⟩ := hEis

  haveI hMfin : Module.Finite 𝒪 (H1 L H 𝒪) := CohCarrier.H1_moduleFinite L H 𝒪 𝒪
  haveI hMtf : Module.IsTorsionFree 𝒪 (H1 L H 𝒪) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun c φ hc => ?_
    by_cases hc0 : c = 0
    · exact Or.inl hc0
    · right
      refine AddMonoidHom.ext fun a => ?_
      have := DFunLike.congr_fun hc a
      rw [AddMonoidHom.smul_apply, AddMonoidHom.zero_apply, smul_eq_mul] at this
      exact (mul_eq_zero.mp this).resolve_left hc0
  haveI hPfin : Module.Finite 𝒪 (Pc L S H 𝒪 (IsLocalRing.ResidueField 𝒪) φ hcomm θbar Sp i₀) :=
    Module.Finite.of_injective (incl L S H 𝒪 (IsLocalRing.ResidueField 𝒪) φ hcomm θbar Sp i₀)
      (incl_injective L S H 𝒪 (IsLocalRing.ResidueField 𝒪) φ hcomm θbar Sp i₀)
  haveI hPtf : Module.IsTorsionFree 𝒪 (Pc L S H 𝒪 (IsLocalRing.ResidueField 𝒪) φ hcomm θbar Sp i₀) :=
    (incl_injective L S H 𝒪 (IsLocalRing.ResidueField 𝒪) φ hcomm θbar Sp i₀).moduleIsTorsionFree _
      (fun c m => rfl)

  have hcard : Fintype.card (Delta L H H' h) = H.relIndex H' := by
    rw [← index_range_iotaDeg_one L H H' h, Subgroup.index_eq_card, Nat.card_eq_fintype_card]
  have hG : IsPGroup p (Delta L H H' h) := by
    obtain ⟨n, hn⟩ := hidx
    exact IsPGroup.of_card (by rw [Nat.card_eq_fintype_card, hcard, hn])

  have hA : ∀ a : 𝒪, H.relIndex H' • a = 0 → a = 0 := by
    intro a ha
    have hne : H.relIndex H' ≠ 0 := by
      rw [← index_range_iotaDeg_one L H H' h]; exact Subgroup.FiniteIndex.index_ne_zero
    rw [← Nat.cast_smul_eq_nsmul 𝒪, smul_eq_mul] at ha
    exact (mul_eq_zero.mp ha).resolve_left (Nat.cast_ne_zero.mpr hne)

  have h0 : ∀ w, (∀ g, rho L S H H' 𝒪 (IsLocalRing.ResidueField 𝒪) φ dG hdG hcomm θbar Sp i₀ h g w = w) →
      ∃ m, (rho L S H H' 𝒪 (IsLocalRing.ResidueField 𝒪) φ dG hdG hcomm θbar Sp i₀ h).norm m = w :=
    fun w hw =>
    exists_norm_eq_of_invariant L S H H' 𝒪 (IsLocalRing.ResidueField 𝒪) φ dG hdG hcomm θbar Sp i₀ h hA
      r hrL hr hH' πk IsLocalRing.residue_surjective (fun g => hπk g) g₀ ℓ hℓ hℓS hℓL hg₀ hθ w hw
  have h1 : ∀ v, (rho L S H H' 𝒪 (IsLocalRing.ResidueField 𝒪) φ dG hdG hcomm θbar Sp i₀ h).norm v = 0 →
      v ∈ Representation.Coinvariants.ker
        (rho L S H H' 𝒪 (IsLocalRing.ResidueField 𝒪) φ dG hdG hcomm θbar Sp i₀ h) :=
    fun v hv => mem_ker_of_norm_eq_zero L S H H' 𝒪 (IsLocalRing.ResidueField 𝒪) φ dG hdG hcomm θbar
      Sp i₀ h hW2 v hv

  have hrank := Representation.finrank_eq_card_mul_finrank_coinvariants_of_isPGroup p hG
    (rho L S H H' 𝒪 (IsLocalRing.ResidueField 𝒪) φ dG hdG hcomm θbar Sp i₀ h) h0 h1
  rw [hcard, finrank_coinvariants_eq L S H H' 𝒪 (IsLocalRing.ResidueField 𝒪) φ dG hdG hcomm θbar Sp i₀ h
    ((IharaLemma.cornerSubmodule (M := CohCarrier.H1 L H' 𝒪) (Sp'.e i₀')).restrictScalars 𝒪)
    hW1 hW2 h1] at hrank

  let eP : Pc L S H 𝒪 (IsLocalRing.ResidueField 𝒪) φ hcomm θbar Sp i₀ ≃ₗ[𝒪]
      ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 L H 𝒪) (Sp.e i₀)) :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let eP' : ↥((IharaLemma.cornerSubmodule (M := CohCarrier.H1 L H' 𝒪) (Sp'.e i₀')).restrictScalars 𝒪) ≃ₗ[𝒪]
      ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 L H' 𝒪) (Sp'.e i₀')) :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← eP.finrank_eq, ← eP'.finrank_eq]
  exact hrank

end Main

end RKRelIndexSubSol
p2m_reactivate "P2MW.S_CohCarrier_finrank_cornerSubmodule_H1_eq_relIndex_mul_of_not_isEisenstein_subfamily.RKRelIndexSubSol"

end
p2m_reactivate "P2MW.S_CohCarrier_finrank_cornerSubmodule_H1_eq_relIndex_mul_of_not_isEisenstein_subfamily.RKRelIndexSubSol"

open scoped IsMulCommutative in
theorem solution
    (L : ℕ) [NeZero L] (S : Set ℕ)
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [CharZero 𝒪]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField 𝒪) p]
    (H H' : Subgroup (ZMod L)ˣ) (hHH' : H ≤ H') (hidx : ∃ n : ℕ, H.relIndex H' = p ^ n)
    (r : ℕ) (hrL : r ∣ L) (hr : 4 ≤ r)
    (hH' : ∀ u ∈ H', ZMod.castHom hrL (ZMod r) (u : ZMod L) = 1)

    {G : Type} (φ : G → CohCarrier.Gen L S)
    (dG : ↥H' → G) (hdG : ∀ u : ↥H', φ (dG u) = CohCarrier.Gen.dia (u : (ZMod L)ˣ))
    (hcomm : ∀ g g' : G,
      CohCarrier.opFamily L H S 𝒪 (φ g) * CohCarrier.opFamily L H S 𝒪 (φ g') =
        CohCarrier.opFamily L H S 𝒪 (φ g') * CohCarrier.opFamily L H S 𝒪 (φ g))
    (hcomm' : ∀ g g' : G,
      CohCarrier.opFamily L H' S 𝒪 (φ g) * CohCarrier.opFamily L H' S 𝒪 (φ g') =
        CohCarrier.opFamily L H' S 𝒪 (φ g') * CohCarrier.opFamily L H' S 𝒪 (φ g))
    (θbar : G → IsLocalRing.ResidueField 𝒪)
    (Sp : IharaLemma.IdempotentSplitting
      ↥(CohCarrier.hdataSub L H S 𝒪 (IsLocalRing.ResidueField 𝒪) φ hcomm θbar).opSubalgebra)
    (i₀ : Fin Sp.n) (πk : Sp.CornerRing i₀ →ₐ[𝒪] IsLocalRing.ResidueField 𝒪)
    (hπk : ∀ g : G, πk (Sp.toCornerRing i₀
      ⟨(CohCarrier.hdataSub L H S 𝒪 (IsLocalRing.ResidueField 𝒪) φ hcomm θbar).op g,
        Algebra.subset_adjoin (Set.mem_range_self g)⟩) = θbar g)
    (Sp' : IharaLemma.IdempotentSplitting
      ↥(CohCarrier.hdataSub L H' S 𝒪 (IsLocalRing.ResidueField 𝒪) φ hcomm' θbar).opSubalgebra)
    (i₀' : Fin Sp'.n) (πk' : Sp'.CornerRing i₀' →ₐ[𝒪] IsLocalRing.ResidueField 𝒪)
    (hπk' : ∀ g : G, πk' (Sp'.toCornerRing i₀'
      ⟨(CohCarrier.hdataSub L H' S 𝒪 (IsLocalRing.ResidueField 𝒪) φ hcomm' θbar).op g,
        Algebra.subset_adjoin (Set.mem_range_self g)⟩) = θbar g)

    (hEis : ∃ (g : G) (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ L),
      φ g = CohCarrier.Gen.T ℓ hℓ hℓS hℓL ∧ ℓ ≡ 1 [MOD L] ∧
        θbar g ≠ (ℓ : IsLocalRing.ResidueField 𝒪) + 1) :
    Module.finrank 𝒪 ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 L H 𝒪) (Sp.e i₀)) =
      H.relIndex H' *
        Module.finrank 𝒪 ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 L H' 𝒪) (Sp'.e i₀')) :=
  RKRelIndexSubSol.main L S 𝒪 p H H' hHH' hidx r hrL hr hH' φ dG hdG hcomm hcomm' θbar Sp i₀ πk hπk
    Sp' i₀' πk' hπk' hEis

end S_CohCarrier_finrank_cornerSubmodule_H1_eq_relIndex_mul_of_not_isEisenstein_subfamily
end P2MW
export P2MW.S_CohCarrier_finrank_cornerSubmodule_H1_eq_relIndex_mul_of_not_isEisenstein_subfamily (solution)
