-- Prove2me | solution 1 for CuspForm.TWLevel.exists_linearMap_ML_HQ_HR_surjective_and_ker_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/0b32696c-1246-5812-a5b4-33d45f503e0a

import Definitions.Def_CuspForm_TWLevelHeckeModule
import Theorems.Thm_CohCarrier_surjective_jDeg_one_and_jDeg_eq_zero_iff_of_four_le
import Theorems.Thm_CohCarrier_jDeg_heckeT_comm_flat
import Theorems.Thm_CohCarrier_jDeg_heckeT_comm_of_dvd
import Theorems.Thm_CohCarrier_jDeg_diamondRaw_comm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_TWLevel_exists_linearMap_ML_HQ_HR_surjective_and_ker_eq_span

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false

open IsLocalRing CuspForm.TWLevel

noncomputable section

namespace TWTraceSol

open CongruenceSubgroup
open scoped MatrixGroups

section GenLinear

variable {𝒪 : Type} [CommRing 𝒪] {σ : Type}
  {P : Type} [AddCommGroup P] [Module (MvPolynomial σ 𝒪) P] [Module 𝒪 P]
  [IsScalarTower 𝒪 (MvPolynomial σ 𝒪) P]
  {Q : Type} [AddCommGroup Q] [Module (MvPolynomial σ 𝒪) Q] [Module 𝒪 Q]
  [IsScalarTower 𝒪 (MvPolynomial σ 𝒪) Q]

def commSubalgebra (f : P →ₗ[𝒪] Q) : Subalgebra 𝒪 (MvPolynomial σ 𝒪) where
  carrier := {t | ∀ x, f (t • x) = t • f x}
  mul_mem' {a b} ha hb x := by rw [mul_smul, ha, hb, mul_smul]
  one_mem' x := by rw [one_smul, one_smul]
  add_mem' {a b} ha hb x := by rw [add_smul, map_add, ha, hb, add_smul]
  zero_mem' x := by rw [zero_smul, map_zero, zero_smul]
  algebraMap_mem' a x := by rw [algebraMap_smul, algebraMap_smul, map_smul]

def linearMapOfX (f : P →ₗ[𝒪] Q) (hf : ∀ (i : σ) (x : P), f ((MvPolynomial.X i : MvPolynomial σ 𝒪) • x) =
    (MvPolynomial.X i : MvPolynomial σ 𝒪) • f x) : P →ₗ[MvPolynomial σ 𝒪] Q :=
  { f with
    map_smul' := fun t x => by
      have hle : (⊤ : Subalgebra 𝒪 (MvPolynomial σ 𝒪)) ≤ commSubalgebra f := by
        rw [← MvPolynomial.adjoin_range_X]
        exact Algebra.adjoin_le (by rintro _ ⟨i, rfl⟩ x; exact hf i x)
      exact hle Algebra.mem_top x }

@[scoped simp] theorem linearMapOfX_apply (f : P →ₗ[𝒪] Q)
    (hf : ∀ (i : σ) (x : P), f ((MvPolynomial.X i : MvPolynomial σ 𝒪) • x) =
      (MvPolynomial.X i : MvPolynomial σ 𝒪) • f x) (x : P) :
    linearMapOfX f hf x = f x := rfl

end GenLinear

section Level

variable (N r : ℕ) {t : ℕ} (qv : Fin t → ℕ) (p : ℕ)
  (πΔ : ∀ i, (ZMod (qv i))ˣ →* Multiplicative (ZMod (p ^ padicValNat p (qv i - 1))))

theorem levelLE_HR_HQ : CohCarrier.LevelLE (level N r qv) (level N r qv) (HR N r qv) (HQ N r qv p πΔ) 1 where
  dvd := dvd_rfl
  ddvd := one_dvd _
  red u hu := by
    rw [ZMod.unitsMap_self]
    exact HQ_le_HR N r qv p πΔ hu

theorem castHom_eq_one_of_mem_HR (u : (ZMod (level N r qv))ˣ) (hu : u ∈ HR N r qv) :
    ZMod.castHom (dvd_level_r N r qv) (ZMod r) (u : ZMod (level N r qv)) = 1 := by
  have h1 : ZMod.unitsMap (dvd_level_r N r qv) u = 1 := hu
  have := congrArg (fun x : (ZMod r)ˣ => (x : ZMod r)) h1
  simpa [ZMod.unitsMap_def] using this

end Level

section Diamond

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (A : Type) [AddCommGroup A]

theorem diamondRaw_eq_self_of_mem (σ : Gamma0 M) (hσ : (σ : SL(2, ℤ)) ∈ CohCarrier.GammaH M H)
    (φ : CohCarrier.H1 M H A) : CohCarrier.diamondRaw M H A σ φ = φ := by
  set κ : ↥(CohCarrier.GammaH M H) := ⟨(σ : SL(2, ℤ)), hσ⟩ with hκdef
  have hconj : ∀ γ : ↥(CohCarrier.GammaH M H), CohCarrier.conjHom M H σ γ = κ * γ * κ⁻¹ := by
    intro γ
    apply Subtype.ext
    simp only [CohCarrier.conjHom, MonoidHom.coe_mk, OneHom.coe_mk, hκdef, Subgroup.coe_mul,
      InvMemClass.coe_inv]
  ext γ
  show φ (Additive.ofMul (CohCarrier.conjHom M H σ (Additive.toMul γ))) = φ γ
  rw [hconj (Additive.toMul γ)]
  have hsplit : Additive.ofMul (κ * Additive.toMul γ * κ⁻¹) =
      Additive.ofMul κ + Additive.ofMul (Additive.toMul γ) + (-(Additive.ofMul κ)) := by
    rw [ofMul_mul, ofMul_mul, ofMul_inv]
  rw [hsplit, map_add, map_add, map_neg, ofMul_toMul]
  abel

theorem diamondL_eq_self_of_mem [NeZero M] (𝒪 : Type) [CommRing 𝒪] (u : (ZMod M)ˣ) (hu : u ∈ H)
    (φ : CohCarrier.H1 M H 𝒪) : CohCarrier.diamondL M H 𝒪 u φ = φ := by
  obtain ⟨σ, hσ⟩ := CohCarrier.gamma0Units_surjective M u
  rw [CohCarrier.diamondL_eq_diamondRaw M H 𝒪 u σ hσ]
  refine diamondRaw_eq_self_of_mem M H 𝒪 σ ?_ φ
  rw [CohCarrier.mem_GammaH_iff]
  exact ⟨σ.2, by rw [Subtype.coe_eta, hσ]; exact hu⟩

end Diamond

section Main

variable {𝒪 : Type} [CommRing 𝒪]
  (p : ℕ) (S : Set ℕ) (N : ℕ) [NeZero N] (r : ℕ) [NeZero r]
  {t : ℕ} (qv : Fin t → ℕ) [∀ i, NeZero (qv i)]
  (πΔ : ∀ i, (ZMod (qv i))ˣ →* Multiplicative (ZMod (p ^ padicValNat p (qv i - 1))))

def coresO : Carrier N r qv 𝒪 (HQ N r qv p πΔ) →ₗ[𝒪] Carrier N r qv 𝒪 (HR N r qv) :=
  CohCarrier.jDegL (level N r qv) (level N r qv) (HR N r qv) (HQ N r qv p πΔ) 1 𝒪 𝒪
    (levelLE_HR_HQ N r qv p πΔ)

theorem coresO_apply (v : Carrier N r qv 𝒪 (HQ N r qv p πΔ)) :
    coresO p N r qv πΔ v =
      CohCarrier.jDeg (level N r qv) (level N r qv) (HR N r qv) (HQ N r qv p πΔ) 1 𝒪
        (levelLE_HR_HQ N r qv p πΔ) v := rfl

theorem coresO_op (g : Gen (level N r qv) S t) (v : Carrier N r qv 𝒪 (HQ N r qv p πΔ)) :
    coresO p N r qv πΔ (op N r qv S 𝒪 (HQ N r qv p πΔ) g v) =
      op N r qv S 𝒪 (HR N r qv) g (coresO p N r qv πΔ v) := by
  cases g with
  | T ℓ hℓ hℓS hℓL =>
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    change coresO p N r qv πΔ (CohCarrier.heckeT (level N r qv) (HQ N r qv p πΔ) ℓ 𝒪 v) =
      CohCarrier.heckeT (level N r qv) (HR N r qv) ℓ 𝒪 (coresO p N r qv πΔ v)
    rw [coresO_apply, coresO_apply]
    exact (CohCarrier.jDeg_heckeT_comm_flat (levelLE_HR_HQ N r qv p πΔ) (Nat.coprime_one_right ℓ) hℓ
      hℓL v).symm
  | U i =>
    change coresO p N r qv πΔ (CohCarrier.heckeT (level N r qv) (HQ N r qv p πΔ) (qv i) 𝒪 v) =
      CohCarrier.heckeT (level N r qv) (HR N r qv) (qv i) 𝒪 (coresO p N r qv πΔ v)
    rw [coresO_apply, coresO_apply]
    exact (CohCarrier.jDeg_heckeT_comm_of_dvd (levelLE_HR_HQ N r qv p πΔ) (dvd_level_q N r qv i) v).symm

theorem coresO_surjective (hr4 : 4 ≤ r) : Function.Surjective (coresO p N r qv πΔ (𝒪 := 𝒪)) := by
  have hs := (CohCarrier.surjective_jDeg_one_and_jDeg_eq_zero_iff_of_four_le (level N r qv) 𝒪
    (HQ N r qv p πΔ) (HR N r qv) (levelLE_HR_HQ N r qv p πΔ) r (dvd_level_r N r qv) hr4
    (castHom_eq_one_of_mem_HR N r qv)).1
  intro y
  obtain ⟨x, hx⟩ := hs y
  exact ⟨x, hx⟩

theorem coresO_diamondL (u : (ZMod (level N r qv))ˣ) (hu : u ∈ HR N r qv)
    (v : Carrier N r qv 𝒪 (HQ N r qv p πΔ)) :
    coresO p N r qv πΔ (CohCarrier.diamondL (level N r qv) (HQ N r qv p πΔ) 𝒪 u v) = coresO p N r qv πΔ v := by
  obtain ⟨σ, hσ⟩ := CohCarrier.gamma0Units_surjective (level N r qv) u
  have hσR : (σ : SL(2, ℤ)) ∈ CohCarrier.GammaH (level N r qv) (HR N r qv) := by
    rw [CohCarrier.mem_GammaH_iff]
    exact ⟨σ.2, by rw [Subtype.coe_eta, hσ]; exact hu⟩
  rw [CohCarrier.diamondL_eq_diamondRaw (level N r qv) (HQ N r qv p πΔ) 𝒪 u σ hσ, coresO_apply, coresO_apply]
  have key := CohCarrier.jDeg_diamondRaw_comm (A := 𝒪) σ σ.2 (levelLE_HR_HQ N r qv p πΔ) v
  rw [Subtype.coe_eta] at key
  rw [← key]
  exact diamondRaw_eq_self_of_mem (level N r qv) (HR N r qv) 𝒪 σ hσR _

variable [IsLocalRing 𝒪]
  (θ : CuspForm.heckeAlgebra N 2 S →+* ResidueField 𝒪)
  (α : Fin t → ResidueField 𝒪)
  (hcQ : OpComm N r qv S 𝒪 (HQ N r qv p πΔ)) (hdc : DiaComm N r qv S 𝒪 (HQ N r qv p πΔ))
  [hR : Fact (OpComm N r qv S 𝒪 (HR N r qv))]

abbrev DQ : CohCarrier.HeckeData 𝒪 (Carrier N r qv 𝒪 (HQ N r qv p πΔ)) (ResidueField 𝒪) :=
  heckeData N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ

abbrev DR : CohCarrier.HeckeData 𝒪 (Carrier N r qv 𝒪 (HR N r qv)) (ResidueField 𝒪) :=
  heckeData N r qv S 𝒪 (HR N r qv) θ α hR.out

scoped instance instModuleQR : Module (DQ p S N r qv πΔ θ α hcQ).FreeAlg (Carrier N r qv 𝒪 (HR N r qv)) :=
  (DR S N r qv θ α).moduleFreeAlg

scoped instance instTowerQR :
    IsScalarTower 𝒪 (DQ p S N r qv πΔ θ α hcQ).FreeAlg (Carrier N r qv 𝒪 (HR N r qv)) :=
  (DR S N r qv θ α).V_isScalarTower

theorem X_smul_Q (g : Gen (level N r qv) S t) (v : Carrier N r qv 𝒪 (HQ N r qv p πΔ)) :
    (MvPolynomial.X g : (DQ p S N r qv πΔ θ α hcQ).FreeAlg) • v = op N r qv S 𝒪 (HQ N r qv p πΔ) g v := by
  show (DQ p S N r qv πΔ θ α hcQ).opAlgHom (MvPolynomial.X g) v = _
  rw [CohCarrier.HeckeData.opAlgHom_X]
  rfl

theorem X_smul_R (g : Gen (level N r qv) S t) (w : Carrier N r qv 𝒪 (HR N r qv)) :
    (MvPolynomial.X g : (DQ p S N r qv πΔ θ α hcQ).FreeAlg) • w = op N r qv S 𝒪 (HR N r qv) g w := by
  show (DR S N r qv θ α).opAlgHom (MvPolynomial.X g) w = _
  rw [CohCarrier.HeckeData.opAlgHom_X]
  rfl

def coresF : Carrier N r qv 𝒪 (HQ N r qv p πΔ) →ₗ[(DQ p S N r qv πΔ θ α hcQ).FreeAlg]
    Carrier N r qv 𝒪 (HR N r qv) :=
  linearMapOfX (coresO p N r qv πΔ) fun g v => by
    rw [X_smul_Q, X_smul_R, coresO_op]

@[scoped simp] theorem coresF_apply (v : Carrier N r qv 𝒪 (HQ N r qv p πΔ)) :
    coresF p S N r qv πΔ θ α hcQ v = coresO p N r qv πΔ v := rfl

abbrev Sm : Submonoid (DQ p S N r qv πΔ θ α hcQ).FreeAlg := (DQ p S N r qv πΔ θ α hcQ).mTheta.primeCompl

abbrev MLR' : Type := LocalizedModule (Sm p S N r qv πΔ θ α hcQ) (Carrier N r qv 𝒪 (HR N r qv))

def lamL : ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ →ₗ[Localization (Sm p S N r qv πΔ θ α hcQ)]
    MLR' p S N r qv πΔ θ α hcQ :=
  LocalizedModule.map (Sm p S N r qv πΔ θ α hcQ) (coresF p S N r qv πΔ θ α hcQ)

def lam₀ : ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ →ₗ[𝒪] ML N r qv S 𝒪 (HR N r qv) θ α hR.out :=
  (lamL p S N r qv πΔ θ α hcQ).restrictScalars 𝒪

theorem lam₀_mk (v : Carrier N r qv 𝒪 (HQ N r qv p πΔ)) (s : Sm p S N r qv πΔ θ α hcQ) :
    lam₀ p S N r qv πΔ θ α hcQ (LocalizedModule.mk v s) = LocalizedModule.mk (coresO p N r qv πΔ v) s := by
  show LocalizedModule.map _ (coresF p S N r qv πΔ θ α hcQ) (LocalizedModule.mk v s) = _
  rw [LocalizedModule.map_mk]
  rfl

theorem lam₀_surjective (hr4 : 4 ≤ r) : Function.Surjective (lam₀ p S N r qv πΔ θ α hcQ) := by
  intro y
  obtain ⟨x, hx⟩ := LocalizedModule.map_surjective (Sm p S N r qv πΔ θ α hcQ)
    (coresF p S N r qv πΔ θ α hcQ) (coresO_surjective p N r qv πΔ hr4) y
  exact ⟨x, hx⟩

theorem lam₀_X_smul (g : Gen (level N r qv) S t) (x : ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ) :
    lam₀ p S N r qv πΔ θ α hcQ
        ((MvPolynomial.X g : (heckeData N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ).FreeAlg) • x) =
      (MvPolynomial.X g : (heckeData N r qv S 𝒪 (HR N r qv) θ α hR.out).FreeAlg) •
        lam₀ p S N r qv πΔ θ α hcQ x := by
  show lamL p S N r qv πΔ θ α hcQ ((MvPolynomial.X g : (DQ p S N r qv πΔ θ α hcQ).FreeAlg) • x) =
    (MvPolynomial.X g : (DQ p S N r qv πΔ θ α hcQ).FreeAlg) • lamL p S N r qv πΔ θ α hcQ x
  exact LinearMap.map_smul_of_tower _ _ _

theorem diaML_mk (u : (ZMod (level N r qv))ˣ) (v : Carrier N r qv 𝒪 (HQ N r qv p πΔ))
    (s : Sm p S N r qv πΔ θ α hcQ) :
    diaML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc u (LocalizedModule.mk v s) =
      LocalizedModule.mk (CohCarrier.diamondL (level N r qv) (HQ N r qv p πΔ) 𝒪 u v) s := by
  show LocalizedModule.map _ (diamondLin N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc u)
    (LocalizedModule.mk v s) = _
  rw [LocalizedModule.map_mk]
  rfl

theorem lam₀_diaML (u : (ZMod (level N r qv))ˣ) (hu : u ∈ HR N r qv)
    (x : ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ) :
    lam₀ p S N r qv πΔ θ α hcQ (diaML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc u x) =
      lam₀ p S N r qv πΔ θ α hcQ x := by
  induction x using LocalizedModule.induction_on with
  | h v s => rw [diaML_mk, lam₀_mk, lam₀_mk, coresO_diamondL p N r qv πΔ u hu]

abbrev augSet : Set (ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ) :=
  {y | ∃ u ∈ HR N r qv, ∃ z : ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ,
    y = diaML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc u z - z}

theorem diaML_smul_loc (u : (ZMod (level N r qv))ˣ) (c : Localization (Sm p S N r qv πΔ θ α hcQ))
    (z : ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ) :
    diaML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc u (c • z) =
      c • diaML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc u z := by
  show LocalizedModule.map _ (diamondLin N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc u) (c • z) =
    c • LocalizedModule.map _ (diamondLin N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc u) z
  exact LinearMap.map_smul _ c z

theorem smul_mem_augSet (c : Localization (Sm p S N r qv πΔ θ α hcQ))
    {y : ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ} (hy : y ∈ augSet p S N r qv πΔ θ α hcQ hdc) :
    c • y ∈ augSet p S N r qv πΔ θ α hcQ hdc := by
  obtain ⟨u, hu, z, rfl⟩ := hy
  exact ⟨u, hu, c • z, by rw [smul_sub, diaML_smul_loc]⟩

theorem loc_smul_comm (a : 𝒪) (c : Localization (Sm p S N r qv πΔ θ α hcQ))
    (m : ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ) : c • (a • m) = a • (c • m) := by
  rw [← algebraMap_smul (Localization (Sm p S N r qv πΔ θ α hcQ)) a m, smul_smul,
    ← algebraMap_smul (Localization (Sm p S N r qv πΔ θ α hcQ)) a (c • m), smul_smul, mul_comm]

theorem smul_mem_span_augSet (c : Localization (Sm p S N r qv πΔ θ α hcQ))
    {m : ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ}
    (hm : m ∈ Submodule.span 𝒪 (augSet p S N r qv πΔ θ α hcQ hdc)) :
    c • m ∈ Submodule.span 𝒪 (augSet p S N r qv πΔ θ α hcQ hdc) := by
  induction hm using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span (smul_mem_augSet p S N r qv πΔ θ α hcQ hdc c hy)
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [loc_smul_comm]; exact Submodule.smul_mem _ a hx

theorem toML_diamondRaw_sub_mem (σ : Gamma0 (level N r qv))
    (hσ : (σ : SL(2, ℤ)) ∈ CohCarrier.GammaH (level N r qv) (HR N r qv))
    (x : Carrier N r qv 𝒪 (HQ N r qv p πΔ)) :
    (DQ p S N r qv πΔ θ α hcQ).toML (CohCarrier.diamondRaw (level N r qv) (HQ N r qv p πΔ) 𝒪 σ x - x) ∈
      augSet p S N r qv πΔ θ α hcQ hdc := by
  obtain ⟨hA, hu⟩ := CohCarrier.mem_GammaH_iff.mp hσ
  rw [Subtype.coe_eta] at hu
  refine ⟨CohCarrier.gamma0Units (level N r qv) σ, hu, (DQ p S N r qv πΔ θ α hcQ).toML x, ?_⟩
  rw [map_sub, ← CohCarrier.diamondL_eq_diamondRaw (level N r qv) (HQ N r qv p πΔ) 𝒪 _ σ rfl,
    ← diaML_toML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc]

theorem toML_apply (v : Carrier N r qv 𝒪 (HQ N r qv p πΔ)) :
    (DQ p S N r qv πΔ θ α hcQ).toML v = LocalizedModule.mk v 1 := rfl

theorem lam₀_eq_zero_iff (hr4 : 4 ≤ r) (x : ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ) :
    lam₀ p S N r qv πΔ θ α hcQ x = 0 ↔ x ∈ Submodule.span 𝒪 (augSet p S N r qv πΔ θ α hcQ hdc) := by
  constructor
  · intro hx
    induction x using LocalizedModule.induction_on with
    | h v s =>
      rw [lam₀_mk] at hx

      obtain ⟨w, hw⟩ : ∃ w : Sm p S N r qv πΔ θ α hcQ,
          ((w : (DQ p S N r qv πΔ θ α hcQ).FreeAlg)) • coresO p N r qv πΔ v = 0 := by
        have h0 := (LocalizedModule.mk_eq (S := Sm p S N r qv πΔ θ α hcQ)).mp
          (hx.trans (LocalizedModule.zero_mk s).symm)
        obtain ⟨u, hu⟩ := h0
        refine ⟨u * s, ?_⟩
        simp only [smul_zero, Submonoid.smul_def, smul_smul] at hu
        simpa [Submonoid.coe_mul] using hu

      have h2 : coresO p N r qv πΔ ((w : (DQ p S N r qv πΔ θ α hcQ).FreeAlg) • v) = 0 := by
        have := (coresF p S N r qv πΔ θ α hcQ).map_smul (w : (DQ p S N r qv πΔ θ α hcQ).FreeAlg) v
        simp only [coresF_apply] at this
        rw [this, hw]

      have h3 := ((CohCarrier.surjective_jDeg_one_and_jDeg_eq_zero_iff_of_four_le (level N r qv) 𝒪
        (HQ N r qv p πΔ) (HR N r qv) (levelLE_HR_HQ N r qv p πΔ) r (dvd_level_r N r qv) hr4
        (castHom_eq_one_of_mem_HR N r qv)).2 _).mp h2

      have h4 : (DQ p S N r qv πΔ θ α hcQ).toML ((w : (DQ p S N r qv πΔ θ α hcQ).FreeAlg) • v) ∈
          Submodule.span 𝒪 (augSet p S N r qv πΔ θ α hcQ hdc) := by
        refine AddSubgroup.closure_induction
          (p := fun y _ => (DQ p S N r qv πΔ θ α hcQ).toML y ∈
            Submodule.span 𝒪 (augSet p S N r qv πΔ θ α hcQ hdc)) ?_ ?_ ?_ ?_ h3
        · rintro y ⟨σ, hσ, x, rfl⟩
          exact Submodule.subset_span (toML_diamondRaw_sub_mem p S N r qv πΔ θ α hcQ hdc σ hσ x)
        · show (DQ p S N r qv πΔ θ α hcQ).toML 0 ∈ _
          rw [map_zero]; exact Submodule.zero_mem _
        · intro x y _ _ hx hy
          show (DQ p S N r qv πΔ θ α hcQ).toML (x + y) ∈ _
          rw [map_add]; exact Submodule.add_mem _ hx hy
        · intro x _ hx
          show (DQ p S N r qv πΔ θ α hcQ).toML (-x) ∈ _
          rw [map_neg]; exact Submodule.neg_mem _ hx

      have h5 : (LocalizedModule.mk v s : ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ) =
          (Localization.mk 1 (w * s) : Localization (Sm p S N r qv πΔ θ α hcQ)) •
            (DQ p S N r qv πΔ θ α hcQ).toML ((w : (DQ p S N r qv πΔ θ α hcQ).FreeAlg) • v) := by
        rw [toML_apply, LocalizedModule.mk_smul_mk, one_smul, mul_one, ← Submonoid.smul_def,
          LocalizedModule.mk_cancel_common_left]
      rw [h5]
      exact smul_mem_span_augSet p S N r qv πΔ θ α hcQ hdc _ h4
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨u, hu, z, rfl⟩ := hy
      rw [map_sub, lam₀_diaML p S N r qv πΔ θ α hcQ hdc u hu, sub_self]
    | zero => exact map_zero _
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul a x _ hx => rw [map_smul, hx, smul_zero]

theorem main (hr4 : 4 ≤ r) :
    ∃ lam₀ : ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ →ₗ[𝒪] ML N r qv S 𝒪 (HR N r qv) θ α hR.out,
      Function.Surjective lam₀ ∧
      (∀ (g : Gen (level N r qv) S t) (x : ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ),
        lam₀ ((MvPolynomial.X g : (heckeData N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ).FreeAlg) • x) =
          (MvPolynomial.X g : (heckeData N r qv S 𝒪 (HR N r qv) θ α hR.out).FreeAlg) • lam₀ x) ∧
      (∀ u ∈ HR N r qv, ∀ x : ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ,
        lam₀ (diaML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc u x) = lam₀ x) ∧
      (∀ x : ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ,
        lam₀ x = 0 ↔ x ∈ Submodule.span 𝒪
          {y : ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ |
            ∃ u ∈ HR N r qv, ∃ z : ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ,
              y = diaML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc u z - z}) :=
  ⟨lam₀ p S N r qv πΔ θ α hcQ, lam₀_surjective p S N r qv πΔ θ α hcQ hr4,
    lam₀_X_smul p S N r qv πΔ θ α hcQ, fun u hu x => lam₀_diaML p S N r qv πΔ θ α hcQ hdc u hu x,
    lam₀_eq_zero_iff p S N r qv πΔ θ α hcQ hdc hr4⟩

end Main

end TWTraceSol
p2m_reactivate "P2MW.S_CuspForm_TWLevel_exists_linearMap_ML_HQ_HR_surjective_and_ker_eq_span.TWTraceSol"

end
p2m_reactivate "P2MW.S_CuspForm_TWLevel_exists_linearMap_ML_HQ_HR_surjective_and_ker_eq_span.TWTraceSol"

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
    (p : ℕ) (S : Set ℕ) (N : ℕ) [NeZero N] (r : ℕ) [NeZero r] (hr4 : 4 ≤ r)
    (θ : CuspForm.heckeAlgebra N 2 S →+* ResidueField 𝒪)
    {t : ℕ} (qv : Fin t → ℕ) [∀ i, NeZero (qv i)]
    (α : Fin t → ResidueField 𝒪)
    (πΔ : ∀ i, (ZMod (qv i))ˣ →* Multiplicative (ZMod (p ^ padicValNat p (qv i - 1))))

    (hcQ : OpComm N r qv S 𝒪 (HQ N r qv p πΔ)) (hdc : DiaComm N r qv S 𝒪 (HQ N r qv p πΔ))
    (hcR : OpComm N r qv S 𝒪 (HR N r qv)) :
    ∃ lam₀ : ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ →ₗ[𝒪] ML N r qv S 𝒪 (HR N r qv) θ α hcR,

      Function.Surjective lam₀ ∧

      (∀ (g : Gen (level N r qv) S t) (x : ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ),
        lam₀ ((MvPolynomial.X g : (heckeData N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ).FreeAlg) • x) =
          (MvPolynomial.X g : (heckeData N r qv S 𝒪 (HR N r qv) θ α hcR).FreeAlg) • lam₀ x) ∧

      (∀ u ∈ HR N r qv, ∀ x : ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ,
        lam₀ (diaML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc u x) = lam₀ x) ∧

      (∀ x : ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ,
        lam₀ x = 0 ↔ x ∈ Submodule.span 𝒪
          {y : ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ |
            ∃ u ∈ HR N r qv, ∃ z : ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ,
              y = diaML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc u z - z}) := by
  haveI : Fact (OpComm N r qv S 𝒪 (HR N r qv)) := ⟨hcR⟩
  exact TWTraceSol.main p S N r qv πΔ θ α hcQ hdc hr4

end S_CuspForm_TWLevel_exists_linearMap_ML_HQ_HR_surjective_and_ker_eq_span
end P2MW
export P2MW.S_CuspForm_TWLevel_exists_linearMap_ML_HQ_HR_surjective_and_ker_eq_span (solution)
