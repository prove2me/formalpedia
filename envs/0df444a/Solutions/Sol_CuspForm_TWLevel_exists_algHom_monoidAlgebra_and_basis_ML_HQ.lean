-- Prove2me | solution 1 for CuspForm.TWLevel.exists_algHom_monoidAlgebra_and_basis_ML_HQ
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/9f04e94a-0691-584d-bbe2-6603724fcd5c

import Definitions.Def_CuspForm_TWLevelHeckeModule
import Definitions.Def_CohCarrier_SubfamilyHeckeData
import Definitions.Def_IharaLemma_IdempotentSplitting
import Theorems.Thm_CohCarrier_exists_basis_cornerSubmodule_H1_monoidAlgebra_of_not_isEisenstein_subfamily
import Theorems.Thm_CuspForm_TWLevel_exists_linearMap_ML_HQ_HR_surjective_and_ker_eq_span
import Theorems.Thm_CohCarrier_HeckeData_nonempty_idempotentSplitting_opSubalgebra
import Theorems.Thm_IharaLemma_IdempotentSplitting_isLocalizedModule_toCorner_maximalIdeal
import Theorems.Thm_CohCarrier_HeckeData_finite_ML_and_free_ML
import Theorems.Thm_CohCarrier_H1_moduleFinite
import Theorems.Thm_MonoidAlgebra_isLocalRing_of_isPGroup
import Theorems.Thm_CohCarrier_diamondL_mul_and_diamondL_one_and_diamondL_eq_one_of_mem
import Theorems.Thm_CuspForm_TWLevel_exists_mem_HR_piQ_eq_and_card_Delta_and_relIndex_HQ_HR
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_TWLevel_exists_algHom_monoidAlgebra_and_basis_ML_HQ

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open IsLocalRing CuspForm.TWLevel

noncomputable section

namespace TWFreeSol

open CongruenceSubgroup
open scoped MatrixGroups IsMulCommutative

p2m_attr_erase "instance" "SetLike.GradeZero.instSemiring SetLike.GradeZero.instCommSemiring SetLike.GradeZero.instRing SetLike.GradeZero.instCommRing SetLike.GradeZero.instAlgebra"

scoped instance (priority := high) commRingOpSubalgebra {R : Type} [CommRing R] {W : Type} [AddCommGroup W]
    [Module R W] {k : Type} [Field k] [Algebra R k] (D : CohCarrier.HeckeData R W k) :
    CommRing ↥D.opSubalgebra :=
  IsMulCommutative.instCommRing

section Diamond

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (𝒪 : Type) [CommRing 𝒪]

theorem diamondL_mul_end (u v : (ZMod M)ˣ) :
    CohCarrier.diamondL M H 𝒪 (u * v) = CohCarrier.diamondL M H 𝒪 u * CohCarrier.diamondL M H 𝒪 v :=
  (CohCarrier.diamondL_mul_and_diamondL_one_and_diamondL_eq_one_of_mem M H 𝒪).1 u v

theorem diamondL_one_end : CohCarrier.diamondL M H 𝒪 1 = 1 :=
  (CohCarrier.diamondL_mul_and_diamondL_one_and_diamondL_eq_one_of_mem M H 𝒪).2.1

theorem diamondL_end_eq_one_of_mem (u : (ZMod M)ˣ) (hu : u ∈ H) : CohCarrier.diamondL M H 𝒪 u = 1 :=
  (CohCarrier.diamondL_mul_and_diamondL_one_and_diamondL_eq_one_of_mem M H 𝒪).2.2 u hu

theorem diamondL_mul (u v : (ZMod M)ˣ) (φ : CohCarrier.H1 M H 𝒪) :
    CohCarrier.diamondL M H 𝒪 (u * v) φ =
      CohCarrier.diamondL M H 𝒪 u (CohCarrier.diamondL M H 𝒪 v φ) :=
  LinearMap.congr_fun (diamondL_mul_end M H 𝒪 u v) φ

theorem diamondL_one (φ : CohCarrier.H1 M H 𝒪) : CohCarrier.diamondL M H 𝒪 1 φ = φ :=
  LinearMap.congr_fun (diamondL_one_end M H 𝒪) φ

theorem diamondL_eq_self_of_mem (u : (ZMod M)ˣ) (hu : u ∈ H) (φ : CohCarrier.H1 M H 𝒪) :
    CohCarrier.diamondL M H 𝒪 u φ = φ :=
  LinearMap.congr_fun (diamondL_end_eq_one_of_mem M H 𝒪 u hu) φ

def diaHom : (ZMod M)ˣ →* Module.End 𝒪 (CohCarrier.H1 M H 𝒪) where
  toFun := CohCarrier.diamondL M H 𝒪
  map_one' := diamondL_one_end M H 𝒪
  map_mul' := diamondL_mul_end M H 𝒪

theorem diamondL_pow (u : (ZMod M)ˣ) (n : ℕ) :
    CohCarrier.diamondL M H 𝒪 (u ^ n) = CohCarrier.diamondL M H 𝒪 u ^ n :=
  map_pow (diaHom M H 𝒪) u n

theorem diamondL_comm (u v : (ZMod M)ˣ) :
    CohCarrier.diamondL M H 𝒪 u * CohCarrier.diamondL M H 𝒪 v =
      CohCarrier.diamondL M H 𝒪 v * CohCarrier.diamondL M H 𝒪 u := by
  rw [← diamondL_mul_end, ← diamondL_mul_end, mul_comm]

end Diamond

section DiaML

variable {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
  (p : ℕ) (S : Set ℕ) (N : ℕ) [NeZero N] (r : ℕ) [NeZero r]
  {t : ℕ} (qv : Fin t → ℕ) [∀ i, NeZero (qv i)]
  (πΔ : ∀ i, (ZMod (qv i))ˣ →* Multiplicative (ZMod (p ^ padicValNat p (qv i - 1))))
  (θ : CuspForm.heckeAlgebra N 2 S →+* ResidueField 𝒪)
  (α : Fin t → ResidueField 𝒪)
  (hcQ : OpComm N r qv S 𝒪 (HQ N r qv p πΔ)) (hdc : DiaComm N r qv S 𝒪 (HQ N r qv p πΔ))

theorem diaML_mk (u : (ZMod (level N r qv))ˣ) (v : Carrier N r qv 𝒪 (HQ N r qv p πΔ))
    (s : (heckeData N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ).mTheta.primeCompl) :
    diaML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc u (LocalizedModule.mk v s) =
      LocalizedModule.mk (CohCarrier.diamondL (level N r qv) (HQ N r qv p πΔ) 𝒪 u v) s := by
  show LocalizedModule.map _ (diamondLin N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc u)
    (LocalizedModule.mk v s) = _
  rw [LocalizedModule.map_mk]
  rfl

theorem diaML_mul (u v : (ZMod (level N r qv))ˣ) :
    diaML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc (u * v) =
      diaML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc u *
        diaML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc v := by
  apply LinearMap.ext
  intro x
  induction x using LocalizedModule.induction_on with
  | h w s =>
    rw [Module.End.mul_apply, diaML_mk, diaML_mk, diaML_mk, diamondL_mul]

theorem diaML_one : diaML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc 1 = 1 := by
  apply LinearMap.ext
  intro x
  induction x using LocalizedModule.induction_on with
  | h w s => rw [diaML_mk, diamondL_one]; rfl

theorem diaML_eq_one_of_mem (u : (ZMod (level N r qv))ˣ) (hu : u ∈ HQ N r qv p πΔ) :
    diaML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc u = 1 := by
  apply LinearMap.ext
  intro x
  induction x using LocalizedModule.induction_on with
  | h w s => rw [diaML_mk, diamondL_eq_self_of_mem _ _ _ u hu]; rfl

def dML : ↥(HR N r qv) →* Module.End 𝒪 (ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ) where
  toFun u := diaML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc u
  map_one' := diaML_one p S N r qv πΔ θ α hcQ hdc
  map_mul' u v := diaML_mul p S N r qv πΔ θ α hcQ hdc u v

@[scoped simp] theorem dML_apply (u : ↥(HR N r qv)) :
    dML p S N r qv πΔ θ α hcQ hdc u = diaML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc u := rfl

end DiaML

section CRT

variable (N r : ℕ) {t : ℕ} (qv : Fin t → ℕ) (p : ℕ)
  (πΔ : ∀ i, (ZMod (qv i))ˣ →* Multiplicative (ZMod (p ^ padicValNat p (qv i - 1))))
  [NeZero N] [NeZero r] [∀ i, NeZero (qv i)]
  (hq : ∀ i, (qv i).Prime) (hqinj : Function.Injective qv) (hqr : ∀ i, qv i ≠ r) (hr : r.Prime)
  (hqN : ∀ i, ¬ qv i ∣ N)

include hq hqinj hqr hr hqN in

theorem exists_mem_HR_piQ_eq [Fact p.Prime] (hπΔ : ∀ i, Function.Surjective (πΔ i))
    (δ : Delta qv p) : ∃ u ∈ HR N r qv, piQ N r qv p πΔ u = δ :=
  (CuspForm.TWLevel.exists_mem_HR_piQ_eq_and_card_Delta_and_relIndex_HQ_HR N r hr qv hqinj hq hqN
    hqr p πΔ hπΔ).1 δ

theorem piQ_eq_one_iff (u : (ZMod (level N r qv))ˣ) (hu : u ∈ HR N r qv) :
    piQ N r qv p πΔ u = 1 ↔ u ∈ HQ N r qv p πΔ :=
  ⟨fun h => ⟨hu, h⟩, fun h => h.2⟩

theorem natCard_delta [Fact p.Prime] :
    Nat.card (Delta qv p) = p ^ ∑ i, padicValNat p (qv i - 1) := by
  classical
  rw [Nat.card_pi, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  haveI : NeZero (p ^ padicValNat p (qv i - 1)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

include hq hqinj hqr hr hqN in

theorem relIndex_HQ_HR [Fact p.Prime] (hπΔ : ∀ i, Function.Surjective (πΔ i)) :
    ∃ n : ℕ, (HQ N r qv p πΔ).relIndex (HR N r qv) = p ^ n :=
  ⟨_, (CuspForm.TWLevel.exists_mem_HR_piQ_eq_and_card_Delta_and_relIndex_HQ_HR N r hr qv hqinj hq
    hqN hqr p πΔ hπΔ).2.2⟩

end CRT

section Dstructure

variable {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
  (p : ℕ) (S : Set ℕ) (N : ℕ) [NeZero N] (r : ℕ) [NeZero r]
  {t : ℕ} (qv : Fin t → ℕ) [∀ i, NeZero (qv i)]
  (πΔ : ∀ i, (ZMod (qv i))ˣ →* Multiplicative (ZMod (p ^ padicValNat p (qv i - 1))))
  (θ : CuspForm.heckeAlgebra N 2 S →+* ResidueField 𝒪)
  (α : Fin t → ResidueField 𝒪)
  (hcQ : OpComm N r qv S 𝒪 (HQ N r qv p πΔ)) (hdc : DiaComm N r qv S 𝒪 (HQ N r qv p πΔ))
  (hsurj : ∀ δ : Delta qv p, ∃ u ∈ HR N r qv, piQ N r qv p πΔ u = δ)

def πR : ↥(HR N r qv) →* Delta qv p := (piQ N r qv p πΔ).comp (HR N r qv).subtype

include hsurj in
theorem πR_surjective : Function.Surjective (πR p N r qv πΔ) := fun δ => by
  obtain ⟨u, hu, rfl⟩ := hsurj δ
  exact ⟨⟨u, hu⟩, rfl⟩

theorem ker_πR_le : (πR p N r qv πΔ).ker ≤ (dML p S N r qv πΔ θ α hcQ hdc).ker := by
  intro u hu
  rw [MonoidHom.mem_ker] at hu ⊢
  rw [dML_apply]
  exact diaML_eq_one_of_mem p S N r qv πΔ θ α hcQ hdc u ⟨u.2, hu⟩

def dΔ : Delta qv p →* Module.End 𝒪 (ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ) :=
  (QuotientGroup.lift (πR p N r qv πΔ).ker (dML p S N r qv πΔ θ α hcQ hdc)
      (ker_πR_le p S N r qv πΔ θ α hcQ hdc)).comp
    (QuotientGroup.quotientKerEquivOfSurjective (πR p N r qv πΔ)
      (πR_surjective p N r qv πΔ hsurj)).symm.toMonoidHom

theorem dΔ_apply (u : ↥(HR N r qv)) :
    dΔ p S N r qv πΔ θ α hcQ hdc hsurj (piQ N r qv p πΔ u) =
      diaML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc u := by
  set e := QuotientGroup.quotientKerEquivOfSurjective (πR p N r qv πΔ)
    (πR_surjective p N r qv πΔ hsurj) with he
  have hmk : e (QuotientGroup.mk u) = piQ N r qv p πΔ u :=
    QuotientGroup.kerLift_mk (πR p N r qv πΔ) u
  have hsymm : e.symm (piQ N r qv p πΔ u) = QuotientGroup.mk u := by
    rw [MulEquiv.symm_apply_eq]
    exact hmk.symm
  show QuotientGroup.lift (πR p N r qv πΔ).ker (dML p S N r qv πΔ θ α hcQ hdc)
      (ker_πR_le p S N r qv πΔ θ α hcQ hdc) (e.symm (piQ N r qv p πΔ u)) = _
  rw [hsymm, QuotientGroup.lift_mk]
  rfl

def D : MonoidAlgebra 𝒪 (Delta qv p) →ₐ[𝒪]
    Module.End 𝒪 (ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ) :=
  MonoidAlgebra.lift 𝒪 _ (Delta qv p) (dΔ p S N r qv πΔ θ α hcQ hdc hsurj)

theorem D_of (u : (ZMod (level N r qv))ˣ) (hu : u ∈ HR N r qv) :
    D p S N r qv πΔ θ α hcQ hdc hsurj (MonoidAlgebra.of 𝒪 (Delta qv p) (piQ N r qv p πΔ u)) =
      diaML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc u := by
  rw [D, MonoidAlgebra.lift_of]
  exact dΔ_apply p S N r qv πΔ θ α hcQ hdc hsurj ⟨u, hu⟩

end Dstructure

section Finite

variable {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
  [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
  (S : Set ℕ) (N : ℕ) [NeZero N] (r : ℕ) [NeZero r]
  {t : ℕ} (qv : Fin t → ℕ) [∀ i, NeZero (qv i)]
  (θ : CuspForm.heckeAlgebra N 2 S →+* ResidueField 𝒪)
  (α : Fin t → ResidueField 𝒪)

theorem finite_ML (H : Subgroup (ZMod (level N r qv))ˣ) (hc : OpComm N r qv S 𝒪 H) :
    Module.Finite 𝒪 (ML N r qv S 𝒪 H θ α hc) := by
  haveI : Module.Finite 𝒪 (Carrier N r qv 𝒪 H) := CohCarrier.H1_moduleFinite (level N r qv) H 𝒪 𝒪
  exact (CohCarrier.HeckeData.finite_ML_and_free_ML (IsLocalRing.residue_surjective)
    (heckeData N r qv S 𝒪 H θ α hc)).1

end Finite

section Family

variable {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
  (S : Set ℕ) (N : ℕ) [NeZero N] (r : ℕ) [NeZero r]
  {t : ℕ} (qv : Fin t → ℕ) [∀ i, NeZero (qv i)] (hqp : ∀ i, (qv i).Prime)
  (θ : CuspForm.heckeAlgebra N 2 S →+* ResidueField 𝒪)
  (α : Fin t → ResidueField 𝒪)

abbrev GG : Type := Gen (level N r qv) S t ⊕ ↥(HR N r qv)

def famG : GG S N r qv → CohCarrier.Gen (level N r qv) S
  | Sum.inl (Gen.T ℓ hℓ hℓS hℓL) => CohCarrier.Gen.T ℓ hℓ hℓS hℓL
  | Sum.inl (Gen.U i) => CohCarrier.Gen.U (qv i) (hqp i) (dvd_level_q N r qv i)
  | Sum.inr u => CohCarrier.Gen.dia (u : (ZMod (level N r qv))ˣ)

def θG : GG S N r qv → ResidueField 𝒪 :=
  Sum.elim (thetaQ N r qv S (ResidueField 𝒪) θ α) (fun _ => 1)

@[scoped simp] theorem θG_inl (g : Gen (level N r qv) S t) :
    θG S N r qv θ α (Sum.inl g) = thetaQ N r qv S (ResidueField 𝒪) θ α g := rfl

@[scoped simp] theorem θG_inr (u : ↥(HR N r qv)) : θG S N r qv θ α (Sum.inr u) = 1 := rfl

variable (H : Subgroup (ZMod (level N r qv))ˣ)

theorem opFamily_famG_inl (g : Gen (level N r qv) S t) :
    CohCarrier.opFamily (level N r qv) H S 𝒪 (famG S N r qv hqp (Sum.inl g)) = op N r qv S 𝒪 H g := by
  cases g <;> rfl

theorem opFamily_famG_inr (u : ↥(HR N r qv)) :
    CohCarrier.opFamily (level N r qv) H S 𝒪 (famG S N r qv hqp (Sum.inr u)) =
      CohCarrier.diamondL (level N r qv) H 𝒪 u := rfl

def CommG : Prop :=
  ∀ g g' : GG S N r qv,
    CohCarrier.opFamily (level N r qv) H S 𝒪 (famG S N r qv hqp g) *
        CohCarrier.opFamily (level N r qv) H S 𝒪 (famG S N r qv hqp g') =
      CohCarrier.opFamily (level N r qv) H S 𝒪 (famG S N r qv hqp g') *
        CohCarrier.opFamily (level N r qv) H S 𝒪 (famG S N r qv hqp g)

theorem commG_of (hc : OpComm N r qv S 𝒪 H)
    (hdcH : ∀ u ∈ HR N r qv, ∀ g : Gen (level N r qv) S t,
      CohCarrier.diamondL (level N r qv) H 𝒪 u * op N r qv S 𝒪 H g =
        op N r qv S 𝒪 H g * CohCarrier.diamondL (level N r qv) H 𝒪 u) :
    CommG S N r qv hqp H (𝒪 := 𝒪) := by
  rintro (g | u) (g' | u')
  · rw [opFamily_famG_inl, opFamily_famG_inl]; exact hc g g'
  · rw [opFamily_famG_inl, opFamily_famG_inr]; exact (hdcH u' u'.2 g).symm
  · rw [opFamily_famG_inl, opFamily_famG_inr]; exact hdcH u u.2 g'
  · rw [opFamily_famG_inr, opFamily_famG_inr]; exact diamondL_comm _ _ _ _ _

abbrev DG (hcG : CommG S N r qv hqp H (𝒪 := 𝒪)) :
    CohCarrier.HeckeData 𝒪 (CohCarrier.H1 (level N r qv) H 𝒪) (ResidueField 𝒪) :=
  CohCarrier.hdataSub (level N r qv) H S 𝒪 (ResidueField 𝒪) (famG S N r qv hqp) hcG (θG S N r qv θ α)

end Family

section Bridge

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (p : ℕ) (S : Set ℕ) (N : ℕ) [NeZero N] (r : ℕ) [NeZero r]
  {t : ℕ} (qv : Fin t → ℕ) [∀ i, NeZero (qv i)] (hqp : ∀ i, (qv i).Prime)
  (θ : CuspForm.heckeAlgebra N 2 S →+* ResidueField 𝒪)
  (α : Fin t → ResidueField 𝒪)
  (H : Subgroup (ZMod (level N r qv))ˣ) (hc : OpComm N r qv S 𝒪 H)
  (hcG : CommG S N r qv hqp H (𝒪 := 𝒪))

local notation3 "VV" => CohCarrier.H1 (level N r qv) H 𝒪
local notation3 "DT" => heckeData N r qv S 𝒪 H θ α hc
local notation3 "FF" => (heckeData N r qv S 𝒪 H θ α hc).FreeAlg
local notation3 "𝔪" => (heckeData N r qv S 𝒪 H θ α hc).mTheta
local notation3 "𝕋" => (DG S N r qv hqp θ α H hcG).opSubalgebra

def gG (g : GG S N r qv) : ↥𝕋 :=
  ⟨(DG S N r qv hqp θ α H hcG).op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩

theorem gG_inl_val (g : Gen (level N r qv) S t) :
    ((gG S N r qv hqp θ α H hcG (Sum.inl g) : ↥𝕋) : Module.End 𝒪 VV) = op N r qv S 𝒪 H g :=
  opFamily_famG_inl S N r qv hqp H g

theorem gG_inr_val (u : ↥(HR N r qv)) :
    ((gG S N r qv hqp θ α H hcG (Sum.inr u) : ↥𝕋) : Module.End 𝒪 VV) =
      CohCarrier.diamondL (level N r qv) H 𝒪 u := rfl

def ψ : FF →ₐ[𝒪] ↥𝕋 := MvPolynomial.aeval fun g => gG S N r qv hqp θ α H hcG (Sum.inl g)

theorem ψ_X (g : Gen (level N r qv) S t) :
    ψ S N r qv hqp θ α H hc hcG (MvPolynomial.X g) = gG S N r qv hqp θ α H hcG (Sum.inl g) :=
  MvPolynomial.aeval_X _ g

theorem val_ψ (f : FF) :
    ((ψ S N r qv hqp θ α H hc hcG f : ↥𝕋) : Module.End 𝒪 VV) = (DT).opAlgHom f := by
  have h : (Subalgebra.val 𝕋).comp (ψ S N r qv hqp θ α H hc hcG) = (DT).opAlgHom := by
    apply MvPolynomial.algHom_ext
    intro g
    rw [AlgHom.comp_apply, ψ_X, Subalgebra.coe_val, gG_inl_val, CohCarrier.HeckeData.opAlgHom_X]
    rfl
  exact congrArg (fun χ : FF →ₐ[𝒪] Module.End 𝒪 VV => χ f) h

theorem smul_eq_ψ_smul (f : FF) (v : VV) : f • v = (ψ S N r qv hqp θ α H hc hcG f) • v := by
  show (DT).opAlgHom f v = ((ψ S N r qv hqp θ α H hc hcG f : ↥𝕋) : Module.End 𝒪 VV) v
  rw [val_ψ]

theorem H1_isTorsionFree : Module.IsTorsionFree 𝒪 VV := by
  refine Module.IsTorsionFree.of_smul_eq_zero fun c φ hcφ => ?_
  by_cases hc0 : c = 0
  · exact Or.inl hc0
  · right
    refine AddMonoidHom.ext fun a => ?_
    have := DFunLike.congr_fun hcφ a
    rw [AddMonoidHom.smul_apply, AddMonoidHom.zero_apply, smul_eq_mul] at this
    exact (mul_eq_zero.mp this).resolve_left hc0

theorem T_moduleFinite : Module.Finite 𝒪 ↥𝕋 := by
  haveI : Module.Finite 𝒪 VV := CohCarrier.H1_moduleFinite (level N r qv) H 𝒪 𝒪
  haveI := H1_isTorsionFree N r qv H (𝒪 := 𝒪)
  haveI : Module.Free 𝒪 VV := Module.free_of_finite_type_torsion_free'
  haveI : Module.Finite 𝒪 (Module.End 𝒪 VV) := Module.Finite.linearMap _ _ _ _
  exact Module.Finite.of_injective (Subalgebra.val 𝕋).toLinearMap Subtype.val_injective

variable (hpow : ∃ n : ℕ, ∀ u ∈ HR N r qv, u ^ p ^ n ∈ H)

include hpow in
theorem gG_inr_pow_eq_one :
    ∃ n : ℕ, ∀ u : ↥(HR N r qv), gG S N r qv hqp θ α H hcG (Sum.inr u) ^ p ^ n = 1 := by
  obtain ⟨n, hn⟩ := hpow
  refine ⟨n, fun u => Subtype.ext ?_⟩
  rw [SubmonoidClass.coe_pow, gG_inr_val, ← diamondL_pow, OneMemClass.coe_one]
  exact diamondL_end_eq_one_of_mem (level N r qv) H 𝒪 _ (hn u u.2)

theorem natCast_p_mem (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪) (I : Ideal ↥𝕋) [I.IsMaximal] :
    ((p : ℕ) : ↥𝕋) ∈ I := by
  haveI := T_moduleFinite S N r qv hqp θ α H hcG
  haveI : Algebra.IsIntegral 𝒪 ↥𝕋 := Algebra.IsIntegral.of_finite 𝒪 ↥𝕋
  have hmax : (I.comap (algebraMap 𝒪 ↥𝕋)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := 𝒪) (S := ↥𝕋) I
  have heq : I.comap (algebraMap 𝒪 ↥𝕋) = maximalIdeal 𝒪 := IsLocalRing.eq_maximalIdeal hmax
  have : (p : 𝒪) ∈ I.comap (algebraMap 𝒪 ↥𝕋) := heq ▸ hp𝒪
  rw [Ideal.mem_comap, map_natCast] at this
  exact this

theorem sub_one_mem_of_pow_prime_pow_eq_one {A : Type} [CommRing A] [hp : Fact p.Prime]
    (I : Ideal A) [hI : I.IsMaximal] (hpI : (p : A) ∈ I) {x : A} {n : ℕ} (hx : x ^ p ^ n = 1) :
    x - 1 ∈ I := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  set a : A ⧸ I := Ideal.Quotient.mk I x with ha
  have hp0 : ((p : ℕ) : A ⧸ I) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]
    exact hpI
  haveI : CharP (A ⧸ I) p := (CharP.charP_iff_prime_eq_zero hp.out).mpr hp0
  have hapow : a ^ p ^ n = 1 := by rw [ha, ← map_pow, hx, map_one]
  have h1 : (a - 1) ^ p ^ n = a ^ p ^ n - 1 ^ p ^ n := sub_pow_char_pow a 1 n
  have h2 : (a - 1) ^ p ^ n = 0 := by rw [h1, hapow, one_pow, sub_self]
  have h3 : a - 1 = 0 := (pow_eq_zero_iff (pow_ne_zero n hp.out.ne_zero)).mp h2
  rw [map_sub, map_one]
  exact h3

include hpow in

theorem gG_inr_sub_one_mem [Fact p.Prime] (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
    (I : Ideal ↥𝕋) [hI : I.IsMaximal] (u : ↥(HR N r qv)) :
    gG S N r qv hqp θ α H hcG (Sum.inr u) - 1 ∈ I := by
  obtain ⟨n, hn⟩ := gG_inr_pow_eq_one p S N r qv hqp θ α H hcG hpow
  exact sub_one_mem_of_pow_prime_pow_eq_one p I (natCast_p_mem p S N r qv hqp θ α H hcG hp𝒪 I) (hn u)

def Jdia : Ideal ↥𝕋 :=
  Ideal.span (Set.range fun u : ↥(HR N r qv) => gG S N r qv hqp θ α H hcG (Sum.inr u) - 1)

include hpow in
theorem Jdia_le [Fact p.Prime] (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪) (I : Ideal ↥𝕋) [I.IsMaximal] :
    Jdia S N r qv hqp θ α H hcG ≤ I :=
  Ideal.span_le.mpr (by
    rintro _ ⟨u, rfl⟩
    exact gG_inr_sub_one_mem p S N r qv hqp θ α H hcG hpow hp𝒪 I u)

theorem exists_sub_ψ_mem_Jdia (x : ↥𝕋) :
    ∃ a : FF, x - ψ S N r qv hqp θ α H hc hcG a ∈ Jdia S N r qv hqp θ α H hcG := by
  have htop : Algebra.adjoin 𝒪
      (Subtype.val ⁻¹' Set.range (DG S N r qv hqp θ α H hcG).op : Set ↥𝕋) = ⊤ :=
    Algebra.adjoin_adjoin_coe_preimage
  have hx : x ∈ Algebra.adjoin 𝒪
      (Subtype.val ⁻¹' Set.range (DG S N r qv hqp θ α H hcG).op : Set ↥𝕋) := by
    rw [htop]
    exact Algebra.mem_top
  refine Algebra.adjoin_induction
    (p := fun y _ => ∃ a : FF, y - ψ S N r qv hqp θ α H hc hcG a ∈ Jdia S N r qv hqp θ α H hcG)
    ?_ ?_ ?_ ?_ hx
  · rintro y ⟨g, hg⟩
    rcases g with g | u
    · refine ⟨MvPolynomial.X g, ?_⟩
      have : y - ψ S N r qv hqp θ α H hc hcG (MvPolynomial.X g) = 0 := by
        rw [ψ_X, sub_eq_zero]
        exact Subtype.ext hg.symm
      rw [this]
      exact zero_mem _
    · refine ⟨1, ?_⟩
      have : y - ψ S N r qv hqp θ α H hc hcG 1 = gG S N r qv hqp θ α H hcG (Sum.inr u) - 1 := by
        rw [map_one, sub_left_inj]
        exact Subtype.ext hg.symm
      rw [this]
      exact Ideal.subset_span ⟨u, rfl⟩
  · intro c
    exact ⟨algebraMap 𝒪 FF c, by rw [AlgHom.commutes, sub_self]; exact zero_mem _⟩
  · rintro x y - - ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    have : x + y - ψ S N r qv hqp θ α H hc hcG (a + b) =
        (x - ψ S N r qv hqp θ α H hc hcG a) + (y - ψ S N r qv hqp θ α H hc hcG b) := by
      rw [map_add]; abel
    rw [this]
    exact add_mem ha hb
  · rintro x y - - ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a * b, ?_⟩
    have : x * y - ψ S N r qv hqp θ α H hc hcG (a * b) =
        x * (y - ψ S N r qv hqp θ α H hc hcG b) +
          (x - ψ S N r qv hqp θ α H hc hcG a) * ψ S N r qv hqp θ α H hc hcG b := by
      rw [map_mul]; ring
    rw [this]
    exact add_mem (Ideal.mul_mem_left _ _ hb) (Ideal.mul_mem_right _ _ ha)

include hpow in

theorem eq_of_comap_ψ_le [Fact p.Prime] (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
    (I J : Ideal ↥𝕋) [hI : I.IsMaximal] [hJ : J.IsMaximal]
    (h : I.comap (ψ S N r qv hqp θ α H hc hcG).toRingHom ≤
      J.comap (ψ S N r qv hqp θ α H hc hcG).toRingHom) : I = J := by
  refine hI.eq_of_le hJ.ne_top fun x hx => ?_
  obtain ⟨a, ha⟩ := exists_sub_ψ_mem_Jdia S N r qv hqp θ α H hc hcG x
  have haI : ψ S N r qv hqp θ α H hc hcG a ∈ I := by
    have := I.sub_mem hx (Jdia_le p S N r qv hqp θ α H hcG hpow hp𝒪 I ha)
    rwa [sub_sub_cancel] at this
  have haJ : ψ S N r qv hqp θ α H hc hcG a ∈ J := h haI
  have := J.add_mem (Jdia_le p S N r qv hqp θ α H hcG hpow hp𝒪 J ha) haJ
  rwa [sub_add_cancel] at this

theorem thetaTilde_surjective : Function.Surjective (DT).thetaTilde := fun y => by
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
  exact ⟨algebraMap 𝒪 FF a, (DT).thetaTilde.commutes a⟩

theorem mTheta_isMaximal : (𝔪).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (thetaTilde_surjective S N r qv θ α H hc)

theorem ker_ψ_le_of_nontrivial [Nontrivial (ML N r qv S 𝒪 H θ α hc)] :
    RingHom.ker (ψ S N r qv hqp θ α H hc hcG).toRingHom ≤ 𝔪 := by
  intro f hf
  by_contra hfm
  have hunit := IsLocalizedModule.map_units (S := (𝔪).primeCompl)
    (LocalizedModule.mkLinearMap (𝔪).primeCompl VV) ⟨f, hfm⟩
  obtain ⟨x, hx⟩ := exists_ne (0 : ML N r qv S 𝒪 H θ α hc)
  apply hx
  apply ((Module.End.isUnit_iff _).mp hunit).injective
  show f • x = f • (0 : ML N r qv S 𝒪 H θ α hc)
  rw [smul_zero]
  have hf' : ψ S N r qv hqp θ α H hc hcG f = 0 := hf
  induction x using LocalizedModule.induction_on with
  | h v s =>
    rw [LocalizedModule.smul'_mk, smul_eq_ψ_smul S N r qv hqp θ α H hc hcG, hf', zero_smul,
      LocalizedModule.zero_mk]

include hpow in

theorem exists_kPoint [Fact p.Prime] (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
    (hker : RingHom.ker (ψ S N r qv hqp θ α H hc hcG).toRingHom ≤ 𝔪)
    (Sp : IharaLemma.IdempotentSplitting ↥𝕋) :
    ∃ (i₀ : Fin Sp.n) (πk : Sp.CornerRing i₀ →ₐ[𝒪] ResidueField 𝒪),
      ∀ g : GG S N r qv,
        πk (Sp.toCornerRing i₀ (gG S N r qv hqp θ α H hcG g)) = θG S N r qv θ α g := by
  haveI := T_moduleFinite S N r qv hqp θ α H hcG
  haveI : Algebra.IsIntegral 𝒪 ↥𝕋 := Algebra.IsIntegral.of_finite 𝒪 ↥𝕋
  letI : Algebra FF ↥𝕋 := (ψ S N r qv hqp θ α H hc hcG).toRingHom.toAlgebra
  haveI : IsScalarTower 𝒪 FF ↥𝕋 :=
    IsScalarTower.of_algebraMap_eq fun c => ((ψ S N r qv hqp θ α H hc hcG).commutes c).symm
  haveI : Algebra.IsIntegral FF ↥𝕋 := Algebra.IsIntegral.tower_top (R := 𝒪)
  haveI := mTheta_isMaximal S N r qv θ α H hc
  obtain ⟨𝔫, h𝔫max, h𝔫⟩ :=
    Ideal.exists_ideal_over_maximal_of_isIntegral (S := ↥𝕋) (𝔪) hker
  haveI := h𝔫max
  obtain ⟨i₀, hi₀⟩ := Sp.exists_eq 𝔫 h𝔫max

  have hψmem : ∀ a : FF, a ∈ 𝔪 → ψ S N r qv hqp θ α H hc hcG a ∈ 𝔫 := fun a ha => by
    rw [← h𝔫] at ha
    exact ha

  have hconst : ∀ x : ↥𝕋, ∃ c : 𝒪, x - algebraMap 𝒪 ↥𝕋 c ∈ 𝔫 := fun x => by
    obtain ⟨a, ha⟩ := exists_sub_ψ_mem_Jdia S N r qv hqp θ α H hc hcG x
    obtain ⟨c, hc'⟩ := IsLocalRing.residue_surjective ((DT).thetaTilde a)
    refine ⟨c, ?_⟩
    have h1 : a - algebraMap 𝒪 FF c ∈ 𝔪 := by
      show (DT).thetaTilde.toRingHom (a - algebraMap 𝒪 FF c) = 0
      rw [map_sub, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes, ← hc']
      exact sub_self _
    have h2 := hψmem _ h1
    rw [map_sub, AlgHom.commutes] at h2
    have := 𝔫.add_mem (Jdia_le p S N r qv hqp θ α H hcG hpow hp𝒪 𝔫 ha) h2
    rwa [sub_add_sub_cancel] at this

  letI := Ideal.Quotient.field 𝔫
  have hsurj : Function.Surjective (Algebra.ofId 𝒪 (↥𝕋 ⧸ 𝔫)) := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨c, hc'⟩ := hconst x
    refine ⟨c, ?_⟩
    rw [Algebra.ofId_apply, IsScalarTower.algebraMap_apply 𝒪 ↥𝕋 (↥𝕋 ⧸ 𝔫),
      Ideal.Quotient.algebraMap_eq]
    exact (Ideal.Quotient.eq.mpr hc').symm
  let e : (𝒪 ⧸ RingHom.ker (Algebra.ofId 𝒪 (↥𝕋 ⧸ 𝔫))) ≃ₐ[𝒪] ↥𝕋 ⧸ 𝔫 :=
    Ideal.quotientKerAlgEquivOfSurjective hsurj
  have hkerO : RingHom.ker (Algebra.ofId 𝒪 (↥𝕋 ⧸ 𝔫)) = maximalIdeal 𝒪 :=
    IsLocalRing.eq_maximalIdeal
      (RingHom.ker_isMaximal_of_surjective (Algebra.ofId 𝒪 (↥𝕋 ⧸ 𝔫)) hsurj)
  let e₀ : ResidueField 𝒪 ≃ₐ[𝒪] ↥𝕋 ⧸ 𝔫 :=
    (Ideal.quotientEquivAlgOfEq 𝒪 hkerO.symm).trans e
  let χ₀ : ↥𝕋 →ₐ[𝒪] ResidueField 𝒪 := e₀.symm.toAlgHom.comp (Ideal.Quotient.mkₐ 𝒪 𝔫)
  have hχ₀ : ∀ (x : ↥𝕋) (c : 𝒪), x - algebraMap 𝒪 ↥𝕋 c ∈ 𝔫 →
      χ₀ x = IsLocalRing.residue 𝒪 c := by
    intro x c hxc
    have hmk : Ideal.Quotient.mk 𝔫 x = algebraMap 𝒪 (↥𝕋 ⧸ 𝔫) c := by
      rw [IsScalarTower.algebraMap_apply 𝒪 ↥𝕋 (↥𝕋 ⧸ 𝔫), Ideal.Quotient.algebraMap_eq]
      exact Ideal.Quotient.eq.mpr hxc
    show e₀.symm (Ideal.Quotient.mk 𝔫 x) = _
    rw [hmk, AlgEquiv.commutes]
    rfl
  have hχ₀ker : ∀ x : ↥𝕋, χ₀ x = 0 → x ∈ 𝔫 := by
    intro x hx
    have : Ideal.Quotient.mk 𝔫 x = 0 := by
      have h := congrArg e₀ hx
      rw [map_zero] at h
      rw [← h]
      exact (e₀.apply_symm_apply _).symm
    exact Ideal.Quotient.eq_zero_iff_mem.mp this

  have hunits : ∀ y : (Sp.𝔪 i₀).primeCompl, IsUnit (χ₀.toRingHom y) := by
    intro y
    apply Ne.isUnit
    intro hy
    exact y.2 (hi₀ ▸ hχ₀ker y hy)
  let πk₀ := IsLocalization.lift (S := Sp.CornerRing i₀) (M := (Sp.𝔪 i₀).primeCompl) hunits
  have hπk₀ : ∀ x : ↥𝕋, πk₀ (Sp.toCornerRing i₀ x) = χ₀ x := fun x =>
    IsLocalization.lift_eq hunits x
  let πk : Sp.CornerRing i₀ →ₐ[𝒪] ResidueField 𝒪 :=
    { πk₀ with
      commutes' := fun c => by
        show πk₀ (Sp.toCornerRing i₀ (algebraMap 𝒪 ↥𝕋 c)) = algebraMap 𝒪 (ResidueField 𝒪) c
        rw [hπk₀, AlgHom.commutes] }
  refine ⟨i₀, πk, fun g => ?_⟩
  show πk₀ (Sp.toCornerRing i₀ (gG S N r qv hqp θ α H hcG g)) = θG S N r qv θ α g
  rw [hπk₀]
  rcases g with g | u
  · obtain ⟨c, hc'⟩ := IsLocalRing.residue_surjective (thetaQ N r qv S (ResidueField 𝒪) θ α g)
    rw [θG_inl, ← hc']
    apply hχ₀
    have h1 : (MvPolynomial.X g : FF) - algebraMap 𝒪 FF c ∈ 𝔪 := by
      show (DT).thetaTilde.toRingHom ((MvPolynomial.X g : FF) - algebraMap 𝒪 FF c) = 0
      rw [map_sub, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes, sub_eq_zero]
      show MvPolynomial.aeval (DT).θbar (MvPolynomial.X g) = _
      rw [MvPolynomial.aeval_X]
      exact hc'.symm
    have h2 := hψmem _ h1
    rwa [map_sub, ψ_X, AlgHom.commutes] at h2
  · rw [θG_inr, ← (IsLocalRing.residue 𝒪).map_one]
    apply hχ₀
    rw [map_one]
    exact gG_inr_sub_one_mem p S N r qv hqp θ α H hcG hpow hp𝒪 𝔫 u

theorem mem_𝔪_iff_of_point {B : Type} [CommRing B] [Algebra 𝒪 B]
    (Sp : IharaLemma.IdempotentSplitting B) (i : Fin Sp.n)
    (πk : Sp.CornerRing i →ₐ[𝒪] ResidueField 𝒪) (b : B) :
    πk (Sp.toCornerRing i b) = 0 ↔ b ∈ Sp.𝔪 i := by
  let ic : B →ₐ[𝒪] Sp.CornerRing i := { Sp.toCornerRing i with commutes' := fun _ => rfl }
  let χ : B →ₐ[𝒪] ResidueField 𝒪 := πk.comp ic
  have hχsurj : Function.Surjective χ := fun y => by
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
    exact ⟨algebraMap 𝒪 B a, χ.commutes a⟩
  have hmax : (RingHom.ker χ.toRingHom).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective χ.toRingHom hχsurj
  obtain ⟨j, hj⟩ := Sp.exists_eq _ hmax
  have hji : j = i := by
    by_contra hne
    have hmem : Sp.e i ∈ Sp.𝔪 j := Sp.mem_of_ne fun h => hne h.symm
    rw [hj, RingHom.mem_ker] at hmem
    have h1 : Sp.toCornerRing i (Sp.e i) = 1 := by
      apply Subtype.ext
      show Sp.e i * Sp.e i * Sp.e i = Sp.e i
      rw [(Sp.idem i).eq, (Sp.idem i).eq]
    have : χ (Sp.e i) = 1 := by
      show πk (Sp.toCornerRing i (Sp.e i)) = 1
      rw [h1, map_one]
    rw [show χ.toRingHom (Sp.e i) = χ (Sp.e i) from rfl, this] at hmem
    exact one_ne_zero hmem
  subst hji
  rw [hj, RingHom.mem_ker]
  rfl

variable (Sp : IharaLemma.IdempotentSplitting
    ↥(DG S N r qv hqp θ α H hcG).opSubalgebra) (i₀ : Fin Sp.n)
  (πk : Sp.CornerRing i₀ →ₐ[𝒪] ResidueField 𝒪)
  (hπk : ∀ g : Gen (level N r qv) S t,
    πk (Sp.toCornerRing i₀ (gG S N r qv hqp θ α H hcG (Sum.inl g))) =
      thetaQ N r qv S (ResidueField 𝒪) θ α g)

include hπk in
theorem πk_toCornerRing_ψ (f : FF) :
    πk (Sp.toCornerRing i₀ (ψ S N r qv hqp θ α H hc hcG f)) = (DT).thetaTilde f := by
  let ic : ↥𝕋 →ₐ[𝒪] Sp.CornerRing i₀ := { Sp.toCornerRing i₀ with commutes' := fun _ => rfl }
  have heq : πk.comp (ic.comp (ψ S N r qv hqp θ α H hc hcG)) = (DT).thetaTilde := by
    apply MvPolynomial.algHom_ext
    intro g
    rw [AlgHom.comp_apply, AlgHom.comp_apply, ψ_X]
    show πk (Sp.toCornerRing i₀ _) = MvPolynomial.aeval (DT).θbar (MvPolynomial.X g)
    rw [hπk, MvPolynomial.aeval_X]
    rfl
  exact congrArg (fun χ : FF →ₐ[𝒪] ResidueField 𝒪 => χ f) heq

include hπk in

theorem mem_mTheta_iff (f : FF) :
    f ∈ 𝔪 ↔ ψ S N r qv hqp θ α H hc hcG f ∈ Sp.𝔪 i₀ := by
  rw [← mem_𝔪_iff_of_point Sp i₀ πk, πk_toCornerRing_ψ S N r qv hqp θ α H hc hcG Sp i₀ πk hπk]
  exact RingHom.mem_ker

include hπk in
theorem comap_𝔪_i₀ : (Sp.𝔪 i₀).comap (ψ S N r qv hqp θ α H hc hcG).toRingHom = 𝔪 :=
  Ideal.ext fun f => (mem_mTheta_iff S N r qv hqp θ α H hc hcG Sp i₀ πk hπk f).symm

include hπk hpow in
theorem exists_notMem_ψ_mul_e_eq_zero [Fact p.Prime] (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
    {j : Fin Sp.n} (hj : j ≠ i₀) :
    ∃ tt : FF, tt ∉ 𝔪 ∧ ψ S N r qv hqp θ α H hc hcG tt * Sp.e j = 0 := by
  by_contra hcon
  push Not at hcon
  haveI := T_moduleFinite S N r qv hqp θ α H hcG
  haveI : Algebra.IsIntegral 𝒪 ↥𝕋 := Algebra.IsIntegral.of_finite 𝒪 ↥𝕋
  letI : Algebra FF ↥𝕋 := (ψ S N r qv hqp θ α H hc hcG).toRingHom.toAlgebra
  haveI : IsScalarTower 𝒪 FF ↥𝕋 :=
    IsScalarTower.of_algebraMap_eq fun c => ((ψ S N r qv hqp θ α H hc hcG).commutes c).symm
  haveI : Algebra.IsIntegral FF ↥𝕋 := Algebra.IsIntegral.tower_top (R := 𝒪)
  haveI := mTheta_isMaximal S N r qv θ α H hc

  have hIP : (Ideal.span {1 - Sp.e j}).comap (algebraMap FF ↥𝕋) ≤ 𝔪 := by
    intro tt htt
    by_contra hm
    apply hcon tt hm
    rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at htt
    obtain ⟨a, ha⟩ := htt
    show (algebraMap FF ↥𝕋 tt) * Sp.e j = 0
    rw [← ha, mul_assoc, sub_mul, one_mul, (Sp.idem j).eq, sub_self, mul_zero]

  obtain ⟨Q, hQI, hQprime, hQ⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (𝔪) (Ideal.span {1 - Sp.e j}) hIP
  haveI := hQprime
  have hQmax : Q.IsMaximal :=
    Ideal.IsIntegral.isMaximal_of_isMaximal_comap (R := FF) Q (by rw [hQ]; infer_instance)
  obtain ⟨j', hj'⟩ := Sp.exists_eq Q hQmax
  have hjj' : j' = j := by
    by_contra hne
    have h1e : (1 : ↥𝕋) - Sp.e j ∈ Q := hQI (Ideal.subset_span rfl)
    have he : Sp.e j ∈ Q := hj' ▸ Sp.mem_of_ne (fun h => hne h.symm)
    apply hQprime.ne_top
    rw [Ideal.eq_top_iff_one]
    have := Q.add_mem he h1e
    rwa [add_sub_cancel] at this
  subst hjj'
  have h2 : (Sp.𝔪 j').comap (ψ S N r qv hqp θ α H hc hcG).toRingHom = 𝔪 := by
    rw [hj']
    exact hQ
  have h3 := comap_𝔪_i₀ S N r qv hqp θ α H hc hcG Sp i₀ πk hπk
  have : Sp.𝔪 j' = Sp.𝔪 i₀ :=
    eq_of_comap_ψ_le p S N r qv hqp θ α H hc hcG hpow hp𝒪 (Sp.𝔪 j') (Sp.𝔪 i₀) (by rw [h2, h3])
  exact hj (Sp.𝔪_injective this)

include hπk hpow in

theorem exists_notMem_ψ_mul_one_sub_e [Fact p.Prime] (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪) :
    ∃ tt : FF, tt ∉ 𝔪 ∧ ψ S N r qv hqp θ α H hc hcG tt * (1 - Sp.e i₀) = 0 := by
  classical
  haveI := mTheta_isMaximal S N r qv θ α H hc
  have hall : ∀ j : Fin Sp.n, ∃ tt : FF, tt ∉ 𝔪 ∧
      (j ≠ i₀ → ψ S N r qv hqp θ α H hc hcG tt * Sp.e j = 0) := by
    intro j
    by_cases hj : j = i₀
    · exact ⟨1, fun h => Ideal.IsPrime.one_notMem inferInstance h, fun h => absurd hj h⟩
    · obtain ⟨tt, htt, h0⟩ :=
        exists_notMem_ψ_mul_e_eq_zero p S N r qv hqp θ α H hc hcG hpow Sp i₀ πk hπk hp𝒪 hj
      exact ⟨tt, htt, fun _ => h0⟩
  choose tf htf₁ htf₂ using hall
  refine ⟨∏ j ∈ Finset.univ.erase i₀, tf j, ?_, ?_⟩
  · exact prod_mem (S := (𝔪).primeCompl) fun j _ => htf₁ j
  · have hsum : (1 : ↥𝕋) - Sp.e i₀ = ∑ j ∈ Finset.univ.erase i₀, Sp.e j := by
      rw [← Sp.coi.complete, ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀), add_sub_cancel_left]
    rw [hsum, Finset.mul_sum]
    refine Finset.sum_eq_zero fun j hj => ?_
    have hj' : j ≠ i₀ := (Finset.mem_erase.mp hj).1
    rw [map_prod, ← Finset.mul_prod_erase _ _ hj, mul_comm (ψ S N r qv hqp θ α H hc hcG (tf j)),
      mul_assoc, htf₂ j hj', mul_zero]

local notation3 "PP" =>
  ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 (level N r qv) H 𝒪) (Sp.e i₀))

@[reducible] def modP : Module FF PP :=
  Module.compHom _ (ψ S N r qv hqp θ α H hc hcG).toRingHom

attribute [local instance] modP

theorem freeAlg_smul_P (f : FF) (y : PP) : f • y = (ψ S N r qv hqp θ α H hc hcG f) • y := rfl

scoped instance towerP : IsScalarTower 𝒪 FF PP :=
  ⟨fun a f y => Subtype.ext (by
    change ((ψ S N r qv hqp θ α H hc hcG (a • f) : ↥𝕋) : Module.End 𝒪 VV) (y : VV) =
      a • ((ψ S N r qv hqp θ α H hc hcG f : ↥𝕋) : Module.End 𝒪 VV) (y : VV)
    rw [map_smul, Subalgebra.coe_smul, LinearMap.smul_apply])⟩

def fL : VV →ₗ[FF] PP where
  toFun := IharaLemma.toCorner (M := VV) (Sp.e i₀)
  map_add' v w := map_add _ v w
  map_smul' f v := by
    apply Subtype.ext
    rw [RingHom.id_apply, freeAlg_smul_P, Submodule.coe_smul, IharaLemma.toCorner_apply,
      IharaLemma.toCorner_apply, smul_eq_ψ_smul S N r qv hqp θ α H hc hcG, smul_smul, smul_smul,
      mul_comm]

theorem fL_apply (v : VV) :
    fL S N r qv hqp θ α H hc hcG Sp i₀ v = IharaLemma.toCorner (M := VV) (Sp.e i₀) v := rfl

include hπk hpow in

theorem isLocalizedModule_fL [Fact p.Prime] (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪) :
    IsLocalizedModule (𝔪).primeCompl (fL S N r qv hqp θ α H hc hcG Sp i₀) := by
  have h₂ := Sp.isLocalizedModule_toCorner_maximalIdeal i₀ (M := VV)
  have hmem := mem_mTheta_iff S N r qv hqp θ α H hc hcG Sp i₀ πk hπk
  obtain ⟨tt, htt, h0⟩ :=
    exists_notMem_ψ_mul_one_sub_e p S N r qv hqp θ α H hc hcG hpow Sp i₀ πk hπk hp𝒪
  rw [mul_sub, mul_one, sub_eq_zero] at h0
  refine ⟨fun s => ?_, fun y => ?_, fun {x₁ x₂} h => ?_⟩
  · have hs : ψ S N r qv hqp θ α H hc hcG (s : FF) ∉ Sp.𝔪 i₀ := fun h => s.2 ((hmem _).mpr h)
    have hb := (Module.End.isUnit_iff _).mp (h₂.map_units ⟨_, hs⟩)
    exact (Module.End.isUnit_iff _).mpr hb
  · refine ⟨((y : VV), 1), ?_⟩
    show ((1 : (𝔪).primeCompl) : FF) • y = fL S N r qv hqp θ α H hc hcG Sp i₀ (y : VV)
    rw [OneMemClass.coe_one, one_smul]
    exact (Subtype.ext (Sp.e_smul_coe i₀ y)).symm
  · refine ⟨⟨tt, htt⟩, ?_⟩
    have h' : Sp.e i₀ • x₁ = Sp.e i₀ • x₂ := congrArg Subtype.val h
    have key : ∀ x : VV, tt • x = ψ S N r qv hqp θ α H hc hcG tt • (Sp.e i₀ • x) := fun x => by
      rw [smul_eq_ψ_smul S N r qv hqp θ α H hc hcG, smul_smul, ← h0]
    show tt • x₁ = tt • x₂
    rw [key, key, h']

def Φ [Fact p.Prime] (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪) : ML N r qv S 𝒪 H θ α hc ≃ₗ[FF] PP :=
  haveI := isLocalizedModule_fL p S N r qv hqp θ α H hc hcG hpow Sp i₀ πk hπk hp𝒪
  IsLocalizedModule.iso (𝔪).primeCompl (fL S N r qv hqp θ α H hc hcG Sp i₀)

theorem Φ_toML [Fact p.Prime] (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪) (v : VV) :
    Φ p S N r qv hqp θ α H hc hcG hpow Sp i₀ πk hπk hp𝒪 ((DT).toML v) =
      fL S N r qv hqp θ α H hc hcG Sp i₀ v := by
  haveI := isLocalizedModule_fL p S N r qv hqp θ α H hc hcG hpow Sp i₀ πk hπk hp𝒪
  have h := IsLocalizedModule.iso_symm_comp (𝔪).primeCompl (fL S N r qv hqp θ α H hc hcG Sp i₀)
  have h' : (Φ p S N r qv hqp θ α H hc hcG hpow Sp i₀ πk hπk hp𝒪).symm
      (fL S N r qv hqp θ α H hc hcG Sp i₀ v) = (DT).toML v := LinearMap.congr_fun h v
  rw [← h', LinearEquiv.apply_symm_apply]

def cornerSmulF (z : Sp.CornerRing i₀) : PP →ₗ[FF] PP where
  toFun y := z • y
  map_add' := smul_add z
  map_smul' f y := by
    apply Subtype.ext
    rw [RingHom.id_apply, IharaLemma.IdempotentSplitting.coe_cornerSmul, freeAlg_smul_P,
      freeAlg_smul_P, Submodule.coe_smul, Submodule.coe_smul,
      IharaLemma.IdempotentSplitting.coe_cornerSmul, smul_smul, smul_smul, mul_comm]

theorem Φ_diaML [Fact p.Prime] (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪) (hdc : DiaComm N r qv S 𝒪 H)
    (u : ↥(HR N r qv)) (x : ML N r qv S 𝒪 H θ α hc) :
    Φ p S N r qv hqp θ α H hc hcG hpow Sp i₀ πk hπk hp𝒪 (diaML N r qv S 𝒪 H θ α hc hdc u x) =
      (Sp.toCornerRing i₀ (gG S N r qv hqp θ α H hcG (Sum.inr u))) •
        Φ p S N r qv hqp θ α H hc hcG hpow Sp i₀ πk hπk hp𝒪 x := by
  haveI := isLocalizedModule_fL p S N r qv hqp θ α H hc hcG hpow Sp i₀ πk hπk hp𝒪
  let dF : ML N r qv S 𝒪 H θ α hc →ₗ[FF] ML N r qv S 𝒪 H θ α hc :=
    (LocalizedModule.map (𝔪).primeCompl (diamondLin N r qv S 𝒪 H θ α hc hdc u)).restrictScalars FF
  have h := IsLocalizedModule.linearMap_ext (S := (𝔪).primeCompl)
    (f := LocalizedModule.mkLinearMap (𝔪).primeCompl VV)
    (f' := fL S N r qv hqp θ α H hc hcG Sp i₀)
    (g := (Φ p S N r qv hqp θ α H hc hcG hpow Sp i₀ πk hπk hp𝒪).toLinearMap ∘ₗ dF)
    (g' := cornerSmulF S N r qv hqp θ α H hc hcG Sp i₀
        (Sp.toCornerRing i₀ (gG S N r qv hqp θ α H hcG (Sum.inr u))) ∘ₗ
      (Φ p S N r qv hqp θ α H hc hcG hpow Sp i₀ πk hπk hp𝒪).toLinearMap) ?_
  · exact LinearMap.congr_fun h x
  · apply LinearMap.ext
    intro v
    show Φ p S N r qv hqp θ α H hc hcG hpow Sp i₀ πk hπk hp𝒪
        (diaML N r qv S 𝒪 H θ α hc hdc u ((DT).toML v)) =
      (Sp.toCornerRing i₀ (gG S N r qv hqp θ α H hcG (Sum.inr u))) •
        Φ p S N r qv hqp θ α H hc hcG hpow Sp i₀ πk hπk hp𝒪 ((DT).toML v)
    rw [diaML_toML, Φ_toML, Φ_toML]
    apply Subtype.ext
    rw [IharaLemma.IdempotentSplitting.coe_cornerSmul, IharaLemma.IdempotentSplitting.coe_toCornerRing,
      fL_apply, fL_apply, IharaLemma.toCorner_apply, IharaLemma.toCorner_apply, smul_smul,
      mul_assoc, (Sp.idem i₀).eq, mul_comm (Sp.e i₀ * _) (Sp.e i₀), ← mul_assoc, (Sp.idem i₀).eq,
      mul_smul]
    rfl

def Φₒ [Fact p.Prime] (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪) : ML N r qv S 𝒪 H θ α hc ≃ₗ[𝒪] PP :=
  (Φ p S N r qv hqp θ α H hc hcG hpow Sp i₀ πk hπk hp𝒪).restrictScalars 𝒪

theorem Φₒ_apply [Fact p.Prime] (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪) (x : ML N r qv S 𝒪 H θ α hc) :
    Φₒ p S N r qv hqp θ α H hc hcG hpow Sp i₀ πk hπk hp𝒪 x =
      Φ p S N r qv hqp θ α H hc hcG hpow Sp i₀ πk hπk hp𝒪 x := rfl

def dT : ↥(HR N r qv) →* ↥𝕋 where
  toFun u := gG S N r qv hqp θ α H hcG (Sum.inr u)
  map_one' := Subtype.ext (by
    rw [gG_inr_val, OneMemClass.coe_one, OneMemClass.coe_one, diamondL_one_end])
  map_mul' u v := Subtype.ext (by
    rw [Subalgebra.coe_mul, gG_inr_val, gG_inr_val, gG_inr_val, Subgroup.coe_mul, diamondL_mul_end])

@[scoped simp] theorem dT_apply (u : ↥(HR N r qv)) :
    dT S N r qv hqp θ α H hcG u = gG S N r qv hqp θ α H hcG (Sum.inr u) := rfl

variable {Δ : Type} [CommGroup Δ] (π : (ZMod (level N r qv))ˣ →* Δ)
  (hπ : ∀ δ : Δ, ∃ u ∈ HR N r qv, π u = δ) (hπH : ∀ u ∈ HR N r qv, (π u = 1 ↔ u ∈ H))

def πR' : ↥(HR N r qv) →* Δ := π.comp (HR N r qv).subtype

include hπ in
theorem πR'_surjective : Function.Surjective (πR' N r qv π) := fun δ => by
  obtain ⟨u, hu, rfl⟩ := hπ δ
  exact ⟨⟨u, hu⟩, rfl⟩

include hπH in
theorem ker_πR'_le : (πR' N r qv π).ker ≤ (dT S N r qv hqp θ α H hcG).ker := by
  intro u hu
  rw [MonoidHom.mem_ker] at hu ⊢
  have huH : (u : (ZMod (level N r qv))ˣ) ∈ H := (hπH u u.2).mp hu
  apply Subtype.ext
  rw [dT_apply, gG_inr_val, OneMemClass.coe_one]
  exact diamondL_end_eq_one_of_mem _ _ _ _ huH

def lamT : MonoidAlgebra 𝒪 Δ →ₐ[𝒪] ↥𝕋 :=
  MonoidAlgebra.lift 𝒪 _ Δ
    ((QuotientGroup.lift (πR' N r qv π).ker (dT S N r qv hqp θ α H hcG)
        (ker_πR'_le S N r qv hqp θ α H hcG π hπH)).comp
      (QuotientGroup.quotientKerEquivOfSurjective (πR' N r qv π)
        (πR'_surjective N r qv π hπ)).symm.toMonoidHom)

theorem lamT_of (u : ↥(HR N r qv)) :
    lamT S N r qv hqp θ α H hcG π hπ hπH (MonoidAlgebra.of 𝒪 Δ (π u)) =
      gG S N r qv hqp θ α H hcG (Sum.inr u) := by
  set e := QuotientGroup.quotientKerEquivOfSurjective (πR' N r qv π) (πR'_surjective N r qv π hπ)
    with he
  have hmk : e (QuotientGroup.mk u) = π u := QuotientGroup.kerLift_mk (πR' N r qv π) u
  have hsymm : e.symm (π u) = QuotientGroup.mk u := by
    rw [MulEquiv.symm_apply_eq]
    exact hmk.symm
  rw [lamT, MonoidAlgebra.lift_of]
  show QuotientGroup.lift (πR' N r qv π).ker (dT S N r qv hqp θ α H hcG)
      (ker_πR'_le S N r qv hqp θ α H hcG π hπH) (e.symm (π u)) = _
  rw [hsymm, QuotientGroup.lift_mk]
  rfl

def toCornerAlgHom : ↥𝕋 →ₐ[𝒪] Sp.CornerRing i₀ :=
  { Sp.toCornerRing i₀ with commutes' := fun _ => rfl }

def ιT : MonoidAlgebra 𝒪 Δ →ₐ[𝒪] Sp.CornerRing i₀ :=
  (toCornerAlgHom S N r qv hqp θ α H hcG Sp i₀).comp (lamT S N r qv hqp θ α H hcG π hπ hπH)

theorem ιT_apply (c : MonoidAlgebra 𝒪 Δ) :
    ιT S N r qv hqp θ α H hcG Sp i₀ π hπ hπH c =
      Sp.toCornerRing i₀ (lamT S N r qv hqp θ α H hcG π hπ hπH c) := rfl

theorem ιT_of (u : ↥(HR N r qv)) :
    ιT S N r qv hqp θ α H hcG Sp i₀ π hπ hπH (MonoidAlgebra.of 𝒪 Δ (π u)) =
      Sp.toCornerRing i₀ (gG S N r qv hqp θ α H hcG (Sum.inr u)) := by
  rw [ιT_apply, lamT_of]

theorem coe_toCornerRing_smul (b : ↥𝕋) (y : PP) :
    ((Sp.toCornerRing i₀ b • y : PP) : VV) = b • (y : VV) := by
  rw [IharaLemma.IdempotentSplitting.coe_cornerSmul, IharaLemma.IdempotentSplitting.coe_toCornerRing,
    mul_smul, Sp.e_smul_coe i₀ y, mul_comm, mul_smul, Sp.e_smul_coe i₀ y]

theorem coe_ιT_smul (c : MonoidAlgebra 𝒪 Δ) (y : PP) :
    ((ιT S N r qv hqp θ α H hcG Sp i₀ π hπ hπH c • y : PP) : VV) =
      lamT S N r qv hqp θ α H hcG π hπ hπH c • (y : VV) := by
  rw [ιT_apply, coe_toCornerRing_smul]

include hπk hpow in
set_option maxHeartbeats 16000000 in

theorem coe_Φₒ_D [Fact p.Prime] (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪) (hdc : DiaComm N r qv S 𝒪 H)
    (Dm : MonoidAlgebra 𝒪 Δ →ₐ[𝒪] Module.End 𝒪 (ML N r qv S 𝒪 H θ α hc))
    (hDm : ∀ u ∈ HR N r qv, Dm (MonoidAlgebra.of 𝒪 Δ (π u)) = diaML N r qv S 𝒪 H θ α hc hdc u)
    (c : MonoidAlgebra 𝒪 Δ) (x : ML N r qv S 𝒪 H θ α hc) :
    ((Φₒ p S N r qv hqp θ α H hc hcG hpow Sp i₀ πk hπk hp𝒪 (Dm c x) : PP) : VV) =
      lamT S N r qv hqp θ α H hcG π hπ hπH c •
        ((Φₒ p S N r qv hqp θ α H hc hcG hpow Sp i₀ πk hπk hp𝒪 x : PP) : VV) := by
  induction c using MonoidAlgebra.induction_on with
  | of δ =>
    obtain ⟨u, hu, rfl⟩ := hπ δ
    rw [hDm u hu, lamT_of S N r qv hqp θ α H hcG π hπ hπH ⟨u, hu⟩, Φₒ_apply, Φₒ_apply,
      Φ_diaML p S N r qv hqp θ α H hc hcG hpow Sp i₀ πk hπk hp𝒪 hdc ⟨u, hu⟩ x, coe_toCornerRing_smul]
  | add a b ha hb =>
    rw [map_add, LinearMap.add_apply, map_add, Submodule.coe_add, ha, hb, map_add, add_smul]
  | smul c a ha =>
    rw [map_smul, LinearMap.smul_apply, map_smul, Submodule.coe_smul_of_tower, ha, map_smul,
      smul_assoc]

include hπk hpow in

theorem Φₒ_D_eq_ιT_smul [Fact p.Prime] (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪) (hdc : DiaComm N r qv S 𝒪 H)
    (Dm : MonoidAlgebra 𝒪 Δ →ₐ[𝒪] Module.End 𝒪 (ML N r qv S 𝒪 H θ α hc))
    (hDm : ∀ u ∈ HR N r qv, Dm (MonoidAlgebra.of 𝒪 Δ (π u)) = diaML N r qv S 𝒪 H θ α hc hdc u)
    (c : MonoidAlgebra 𝒪 Δ) (x : ML N r qv S 𝒪 H θ α hc) :
    Φₒ p S N r qv hqp θ α H hc hcG hpow Sp i₀ πk hπk hp𝒪 (Dm c x) =
      ιT S N r qv hqp θ α H hcG Sp i₀ π hπ hπH c • Φₒ p S N r qv hqp θ α H hc hcG hpow Sp i₀ πk hπk hp𝒪 x :=
  Subtype.ext (by
    rw [coe_Φₒ_D p S N r qv hqp θ α H hc hcG hpow Sp i₀ πk hπk π hπ hπH hp𝒪 hdc Dm hDm, coe_ιT_smul])

attribute [irreducible] Φₒ

end Bridge

section Special

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (p : ℕ) (S : Set ℕ) (N : ℕ) [NeZero N] (r : ℕ) [NeZero r]
  {t : ℕ} (qv : Fin t → ℕ) [∀ i, NeZero (qv i)]
  (θ : CuspForm.heckeAlgebra N 2 S →+* ResidueField 𝒪)
  (α : Fin t → ResidueField 𝒪)
  (πΔ : ∀ i, (ZMod (qv i))ˣ →* Multiplicative (ZMod (p ^ padicValNat p (qv i - 1))))

theorem hdcH_R : ∀ u ∈ HR N r qv, ∀ g : Gen (level N r qv) S t,
    CohCarrier.diamondL (level N r qv) (HR N r qv) 𝒪 u * op N r qv S 𝒪 (HR N r qv) g =
      op N r qv S 𝒪 (HR N r qv) g * CohCarrier.diamondL (level N r qv) (HR N r qv) 𝒪 u := by
  intro u hu g
  rw [diamondL_end_eq_one_of_mem _ _ _ u hu, one_mul, mul_one]

theorem hpow_R : ∃ n : ℕ, ∀ u ∈ HR N r qv, u ^ p ^ n ∈ HR N r qv :=
  ⟨0, fun u hu => by rwa [pow_zero, pow_one]⟩

theorem hpow_Q [Fact p.Prime] (hq : ∀ i, (qv i).Prime) (hqinj : Function.Injective qv)
    (hqr : ∀ i, qv i ≠ r) (hr : r.Prime) (hqN : ∀ i, ¬ qv i ∣ N)
    (hπΔ : ∀ i, Function.Surjective (πΔ i)) :
    ∃ n : ℕ, ∀ u ∈ HR N r qv, u ^ p ^ n ∈ HQ N r qv p πΔ := by
  obtain ⟨n, hn⟩ := relIndex_HQ_HR N r qv p πΔ hq hqinj hqr hr hqN hπΔ
  refine ⟨n, fun u hu => ?_⟩
  rw [← hn]
  exact Subgroup.pow_relIndex_mem (HQ N r qv p πΔ) hu

variable (hr4 : 4 ≤ r)
  (hcQ : OpComm N r qv S 𝒪 (HQ N r qv p πΔ)) (hdc : DiaComm N r qv S 𝒪 (HQ N r qv p πΔ))
  (hcR : OpComm N r qv S 𝒪 (HR N r qv))

include hr4 hdc in

theorem subsingleton_R_of_Q [Subsingleton (ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ)] :
    Subsingleton (ML N r qv S 𝒪 (HR N r qv) θ α hcR) := by
  obtain ⟨lam₀, hsurj, -, -, -⟩ :=
    CuspForm.TWLevel.exists_linearMap_ML_HQ_HR_surjective_and_ker_eq_span p S N r hr4 θ qv α πΔ
      hcQ hdc hcR
  refine ⟨fun x y => ?_⟩
  obtain ⟨x', rfl⟩ := hsurj x
  obtain ⟨y', rfl⟩ := hsurj y
  rw [Subsingleton.elim x' y']

include hr4 hdc in

theorem subsingleton_Q_of_R [Fact p.Prime] [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
    (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
    (hsurjΔ : ∀ δ : Delta qv p, ∃ u ∈ HR N r qv, piQ N r qv p πΔ u = δ)
    [Subsingleton (ML N r qv S 𝒪 (HR N r qv) θ α hcR)] :
    Subsingleton (ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ) := by
  obtain ⟨lam₀, -, -, -, hker⟩ :=
    CuspForm.TWLevel.exists_linearMap_ML_HQ_HR_surjective_and_ker_eq_span p S N r hr4 θ qv α πΔ
      hcQ hdc hcR
  set Dm := D p S N r qv πΔ θ α hcQ hdc hsurjΔ with hDm
  haveI : ∀ i, NeZero (p ^ padicValNat p (qv i - 1)) :=
    fun i => ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  haveI : Finite (Delta qv p) := inferInstance
  haveI : IsLocalRing (MonoidAlgebra 𝒪 (Delta qv p)) :=
    MonoidAlgebra.isLocalRing_of_isPGroup hp𝒪 (IsPGroup.of_card (natCard_delta qv p))
  letI : Module (MonoidAlgebra 𝒪 (Delta qv p)) (ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ) :=
    Module.compHom _ Dm.toRingHom
  have hsm : ∀ (a : MonoidAlgebra 𝒪 (Delta qv p)) (x : ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ),
      a • x = Dm a x := fun _ _ => rfl
  haveI : IsScalarTower 𝒪 (MonoidAlgebra 𝒪 (Delta qv p)) (ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ) :=
    ⟨fun c a x => by rw [hsm, hsm, map_smul, LinearMap.smul_apply]⟩
  haveI : Module.Finite 𝒪 (ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ) := finite_ML S N r qv θ α _ hcQ
  haveI : Module.Finite (MonoidAlgebra 𝒪 (Delta qv p)) (ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ) :=
    Module.Finite.of_restrictScalars_finite 𝒪 _ _

  have hmem : ∀ δ : Delta qv p,
      MonoidAlgebra.of 𝒪 (Delta qv p) δ - 1 ∈ maximalIdeal (MonoidAlgebra 𝒪 (Delta qv p)) := by
    intro δ
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h := hu.map (MonoidAlgebra.lift 𝒪 𝒪 (Delta qv p) (1 : Delta qv p →* 𝒪))
    rw [map_sub, MonoidAlgebra.lift_of, MonoidHom.one_apply,
      map_one (MonoidAlgebra.lift 𝒪 𝒪 (Delta qv p) (1 : Delta qv p →* 𝒪)), sub_self] at h
    exact not_isUnit_zero h
  have htop : (⊤ : Submodule (MonoidAlgebra 𝒪 (Delta qv p)) (ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ)) ≤
      maximalIdeal (MonoidAlgebra 𝒪 (Delta qv p)) • ⊤ := by
    intro x _
    have hx : lam₀ x = 0 := Subsingleton.elim _ _
    have hx' := (hker x).mp hx
    refine Submodule.span_induction
      (p := fun y _ => y ∈ (maximalIdeal (MonoidAlgebra 𝒪 (Delta qv p)) • ⊤ :
        Submodule (MonoidAlgebra 𝒪 (Delta qv p)) (ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ)))
      ?_ ?_ ?_ ?_ hx'
    · rintro y ⟨u, hu, z, rfl⟩
      have : diaML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc u z - z =
          (MonoidAlgebra.of 𝒪 (Delta qv p) (piQ N r qv p πΔ u) - 1) • z := by
        rw [hsm, map_sub, map_one, LinearMap.sub_apply, Module.End.one_apply, hDm,
          D_of p S N r qv πΔ θ α hcQ hdc hsurjΔ u hu]
      rw [this]
      exact Submodule.smul_mem_smul (hmem _) Submodule.mem_top
    · exact zero_mem _
    · intro y z _ _ hy hz
      exact add_mem hy hz
    · intro c y _ hy
      rw [← algebraMap_smul (MonoidAlgebra 𝒪 (Delta qv p)) c y]
      exact Submodule.smul_mem _ _ hy
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
    (maximalIdeal (MonoidAlgebra 𝒪 (Delta qv p))) ⊤ Module.Finite.fg_top htop
    (by rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top])
  refine subsingleton_of_forall_eq 0 fun x => ?_
  have hx : x ∈ (⊤ : Submodule (MonoidAlgebra 𝒪 (Delta qv p))
    (ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ)) := Submodule.mem_top
  rw [hbot] at hx
  exact (Submodule.mem_bot _).mp hx

end Special

section Main

set_option maxHeartbeats 16000000 in
theorem main
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [CharZero 𝒪]
    (p : ℕ) [Fact p.Prime] (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
    (S : Set ℕ) (N : ℕ) [NeZero N] (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    (r : ℕ) [NeZero r] (hr : r.Prime) (hr4 : 4 ≤ r)
    (θ : CuspForm.heckeAlgebra N 2 S →+* ResidueField 𝒪)
    {t : ℕ} (qv : Fin t → ℕ) [∀ i, NeZero (qv i)] (hqinj : Function.Injective qv)
    (hq : ∀ i, (qv i).Prime ∧ qv i ∉ S) (hqr : ∀ i, qv i ≠ r)
    (α : Fin t → ResidueField 𝒪)
    (πΔ : ∀ i, (ZMod (qv i))ˣ →* Multiplicative (ZMod (p ^ padicValNat p (qv i - 1))))
    (hπΔ : ∀ i, Function.Surjective (πΔ i))
    (hEis : ∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ level N r qv),
      ℓ ≡ 1 [MOD level N r qv] ∧
      θ (CuspForm.heckeAlgebra.T hℓ (not_dvd_of_not_dvd_level N r qv hℓL) hℓS) ≠
        (ℓ : ResidueField 𝒪) + 1)
    (hcQ : OpComm N r qv S 𝒪 (HQ N r qv p πΔ)) (hdc : DiaComm N r qv S 𝒪 (HQ N r qv p πΔ))
    (hcR : OpComm N r qv S 𝒪 (HR N r qv)) :
    ∃ D : MonoidAlgebra 𝒪 (Delta qv p) →ₐ[𝒪]
        Module.End 𝒪 (ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ),
      (∀ u ∈ HR N r qv, D (MonoidAlgebra.of 𝒪 (Delta qv p) (piQ N r qv p πΔ u)) =
        diaML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc u) ∧
      (∀ δ : Delta qv p, ∃ u ∈ HR N r qv, piQ N r qv p πΔ u = δ) ∧
      Module.Finite 𝒪 (ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ) ∧
      ∃ b : Fin (Module.finrank 𝒪 (ML N r qv S 𝒪 (HR N r qv) θ α hcR)) →
          ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ,
        (∀ x : ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ,
          ∃ c : Fin (Module.finrank 𝒪 (ML N r qv S 𝒪 (HR N r qv) θ α hcR)) →
              MonoidAlgebra 𝒪 (Delta qv p),
            x = ∑ i, D (c i) (b i)) ∧
        (∀ c : Fin (Module.finrank 𝒪 (ML N r qv S 𝒪 (HR N r qv) θ α hcR)) →
            MonoidAlgebra 𝒪 (Delta qv p),
          ∑ i, D (c i) (b i) = 0 ↔ ∀ i, c i = 0) := by
  classical
  have hqp : ∀ i, (qv i).Prime := fun i => (hq i).1
  have hqN : ∀ i, ¬ qv i ∣ N := fun i h => (hq i).2 (hNS _ (hq i).1 h)
  have hsurjΔ := exists_mem_HR_piQ_eq N r qv p πΔ hqp hqinj hqr hr hqN hπΔ
  have hidx := relIndex_HQ_HR N r qv p πΔ hqp hqinj hqr hr hqN hπΔ
  set Dm := D p S N r qv πΔ θ α hcQ hdc hsurjΔ with hDm
  have hD_of : ∀ u ∈ HR N r qv, Dm (MonoidAlgebra.of 𝒪 (Delta qv p) (piQ N r qv p πΔ u)) =
      diaML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc u :=
    fun u hu => D_of p S N r qv πΔ θ α hcQ hdc hsurjΔ u hu
  haveI hfinQ : Module.Finite 𝒪 (ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ) :=
    finite_ML S N r qv θ α _ hcQ
  haveI hfinR : Module.Finite 𝒪 (ML N r qv S 𝒪 (HR N r qv) θ α hcR) := finite_ML S N r qv θ α _ hcR
  refine ⟨Dm, hD_of, hsurjΔ, hfinQ, ?_⟩

  by_cases hR : Subsingleton (ML N r qv S 𝒪 (HR N r qv) θ α hcR)
  · haveI := hR
    haveI : Subsingleton (ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ) :=
      subsingleton_Q_of_R p S N r qv θ α πΔ hr4 hcQ hdc hcR hp𝒪 hsurjΔ
    have hd : Module.finrank 𝒪 (ML N r qv S 𝒪 (HR N r qv) θ α hcR) = 0 :=
      Module.finrank_zero_of_subsingleton
    refine ⟨fun _ => 0, fun x => ⟨fun _ => 0, Subsingleton.elim _ _⟩,
      fun c => ⟨fun _ i => ?_, fun _ => Subsingleton.elim _ _⟩⟩
    exact absurd (i.2.trans_eq hd) (Nat.not_lt_zero _)

  haveI hRnt : Nontrivial (ML N r qv S 𝒪 (HR N r qv) θ α hcR) := not_subsingleton_iff_nontrivial.mp hR
  haveI hQnt : Nontrivial (ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hR (subsingleton_R_of_Q p S N r qv θ α πΔ hr4 hcQ hdc hcR)

  have hcGQ : CommG S N r qv hqp (HQ N r qv p πΔ) (𝒪 := 𝒪) :=
    commG_of S N r qv hqp (HQ N r qv p πΔ) hcQ (fun u _ g => hdc u g)
  have hcGR : CommG S N r qv hqp (HR N r qv) (𝒪 := 𝒪) :=
    commG_of S N r qv hqp (HR N r qv) hcR (hdcH_R S N r qv)
  have hpowQ := hpow_Q p N r qv πΔ hqp hqinj hqr hr hqN hπΔ
  have hpowR := hpow_R p N r qv

  haveI : Module.Finite 𝒪 (CohCarrier.H1 (level N r qv) (HQ N r qv p πΔ) 𝒪) :=
    CohCarrier.H1_moduleFinite _ _ 𝒪 𝒪
  haveI : Module.Finite 𝒪 (CohCarrier.H1 (level N r qv) (HR N r qv) 𝒪) :=
    CohCarrier.H1_moduleFinite _ _ 𝒪 𝒪
  obtain ⟨Sp⟩ := CohCarrier.HeckeData.nonempty_idempotentSplitting_opSubalgebra
    (DG S N r qv hqp θ α (HQ N r qv p πΔ) hcGQ)
  obtain ⟨Sp'⟩ := CohCarrier.HeckeData.nonempty_idempotentSplitting_opSubalgebra
    (DG S N r qv hqp θ α (HR N r qv) hcGR)

  obtain ⟨i₀, πk, hπk⟩ := exists_kPoint p S N r qv hqp θ α (HQ N r qv p πΔ) hcQ hcGQ hpowQ hp𝒪
    (ker_ψ_le_of_nontrivial S N r qv hqp θ α (HQ N r qv p πΔ) hcQ hcGQ) Sp
  obtain ⟨i₀', πk', hπk'⟩ := exists_kPoint p S N r qv hqp θ α (HR N r qv) hcR hcGR hpowR hp𝒪
    (ker_ψ_le_of_nontrivial S N r qv hqp θ α (HR N r qv) hcR hcGR) Sp'
  have hπk_inl : ∀ g : Gen (level N r qv) S t,
      πk (Sp.toCornerRing i₀ (gG S N r qv hqp θ α (HQ N r qv p πΔ) hcGQ (Sum.inl g))) =
        thetaQ N r qv S (ResidueField 𝒪) θ α g := fun g => hπk (Sum.inl g)
  have hπk'_inl : ∀ g : Gen (level N r qv) S t,
      πk' (Sp'.toCornerRing i₀' (gG S N r qv hqp θ α (HR N r qv) hcGR (Sum.inl g))) =
        thetaQ N r qv S (ResidueField 𝒪) θ α g := fun g => hπk' (Sum.inl g)

  have hπH : ∀ u ∈ HR N r qv, (piQ N r qv p πΔ u = 1 ↔ u ∈ HQ N r qv p πΔ) :=
    fun u hu => piQ_eq_one_iff N r qv p πΔ u hu
  let ι := ιT S N r qv hqp θ α (HQ N r qv p πΔ) hcGQ Sp i₀ (piQ N r qv p πΔ) hsurjΔ hπH
  have hι : ∀ u : ↥(HR N r qv), ι (MonoidAlgebra.of 𝒪 (Delta qv p) (piQ N r qv p πΔ u)) =
      Sp.toCornerRing i₀ (gG S N r qv hqp θ α (HQ N r qv p πΔ) hcGQ (Sum.inr u)) :=
    fun u => ιT_of S N r qv hqp θ α (HQ N r qv p πΔ) hcGQ Sp i₀ (piQ N r qv p πΔ) hsurjΔ hπH u

  haveI : CharP (ResidueField 𝒪) p := by
    refine (CharP.charP_iff_prime_eq_zero Fact.out).mpr ?_
    rw [← map_natCast (IsLocalRing.residue 𝒪), IsLocalRing.residue_eq_zero_iff]
    exact hp𝒪
  have hH' : ∀ u ∈ HR N r qv,
      ZMod.castHom (dvd_level_r N r qv) (ZMod r) (u : ZMod (level N r qv)) = 1 := by
    intro u hu
    have h := congrArg Units.val ((mem_HR_iff N r qv u).mp hu)
    rwa [ZMod.unitsMap_def, Units.coe_map, Units.val_one] at h
  have hEis' : ∃ (g : GG S N r qv) (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ level N r qv),
      famG S N r qv hqp g = CohCarrier.Gen.T ℓ hℓ hℓS hℓL ∧ ℓ ≡ 1 [MOD level N r qv] ∧
        θG S N r qv θ α g ≠ (ℓ : ResidueField 𝒪) + 1 := by
    obtain ⟨ℓ, hℓ, hℓS, hℓL, hmod, hne⟩ := hEis
    exact ⟨Sum.inl (Gen.T ℓ hℓ hℓS hℓL), ℓ, hℓ, hℓS, hℓL, rfl, hmod, hne⟩
  obtain ⟨b', hspan', hind'⟩ :=
    CohCarrier.exists_basis_cornerSubmodule_H1_monoidAlgebra_of_not_isEisenstein_subfamily
      (level N r qv) S 𝒪 p (HQ N r qv p πΔ) (HR N r qv) (HQ_le_HR N r qv p πΔ) hidx r
      (dvd_level_r N r qv) hr4 hH' (famG S N r qv hqp) Sum.inr (fun u => rfl) hcGQ hcGR
      (θG S N r qv θ α) Sp i₀ πk hπk Sp' i₀' πk' hπk' hEis' (piQ N r qv p πΔ) hsurjΔ hπH ι hι

  let ΦQₒ := Φₒ p S N r qv hqp θ α (HQ N r qv p πΔ) hcQ hcGQ hpowQ Sp i₀ πk hπk_inl hp𝒪
  let ΦRₒ := Φₒ p S N r qv hqp θ α (HR N r qv) hcR hcGR hpowR Sp' i₀' πk' hπk'_inl hp𝒪
  have hd : Module.finrank 𝒪 (ML N r qv S 𝒪 (HR N r qv) θ α hcR) =
      Module.finrank 𝒪 ↥(IharaLemma.cornerSubmodule
        (M := CohCarrier.H1 (level N r qv) (HR N r qv) 𝒪) (Sp'.e i₀')) := ΦRₒ.finrank_eq

  have hcompat : ∀ (c : MonoidAlgebra 𝒪 (Delta qv p)) (x : ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ),
      ΦQₒ (Dm c x) = ι c • ΦQₒ x := fun c x =>
    Φₒ_D_eq_ιT_smul p S N r qv hqp θ α (HQ N r qv p πΔ) hcQ hcGQ hpowQ Sp i₀ πk hπk_inl
      (piQ N r qv p πΔ) hsurjΔ hπH hp𝒪 hdc Dm hD_of c x

  let e := finCongr hd
  refine ⟨fun i => ΦQₒ.symm (b' (e i)), fun x => ?_, fun c => ⟨fun hsum i => ?_, fun hc0 => ?_⟩⟩
  · obtain ⟨c', hc'⟩ := hspan' (ΦQₒ x)
    refine ⟨fun i => c' (e i), ?_⟩
    apply ΦQₒ.injective
    rw [hc', map_sum, ← Equiv.sum_comp e]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcompat, LinearEquiv.apply_symm_apply]
  · have h0 : ∑ i, ι (c i) • b' (e i) = 0 := by
      have h := congrArg ΦQₒ hsum
      rw [map_sum, map_zero] at h
      rw [← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcompat, LinearEquiv.apply_symm_apply]
    have h0' : ∑ i', ι (c (e.symm i')) • b' i' = 0 := by
      rw [← Equiv.sum_comp e]
      simpa only [Equiv.symm_apply_apply] using h0
    have h := (hind' (fun i' => c (e.symm i'))).mp h0' (e i)
    simpa only [Equiv.symm_apply_apply] using h
  · simp only [hc0, map_zero, LinearMap.zero_apply, Finset.sum_const_zero]

end Main

end TWFreeSol
p2m_reactivate "P2MW.S_CuspForm_TWLevel_exists_algHom_monoidAlgebra_and_basis_ML_HQ.TWFreeSol"

end
p2m_reactivate "P2MW.S_CuspForm_TWLevel_exists_algHom_monoidAlgebra_and_basis_ML_HQ.TWFreeSol"

open TWFreeSol in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [CharZero 𝒪]
    (p : ℕ) [Fact p.Prime] (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)

    (S : Set ℕ) (N : ℕ) [NeZero N] (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)

    (r : ℕ) [NeZero r] (hr : r.Prime) (hr4 : 4 ≤ r)

    (θ : CuspForm.heckeAlgebra N 2 S →+* ResidueField 𝒪)

    {t : ℕ} (qv : Fin t → ℕ) [∀ i, NeZero (qv i)] (hqinj : Function.Injective qv)
    (hq : ∀ i, (qv i).Prime ∧ qv i ∉ S) (hqr : ∀ i, qv i ≠ r)
    (α : Fin t → ResidueField 𝒪)

    (πΔ : ∀ i, (ZMod (qv i))ˣ →* Multiplicative (ZMod (p ^ padicValNat p (qv i - 1))))
    (hπΔ : ∀ i, Function.Surjective (πΔ i))

    (hEis : ∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ level N r qv),
      ℓ ≡ 1 [MOD level N r qv] ∧
      θ (CuspForm.heckeAlgebra.T hℓ (not_dvd_of_not_dvd_level N r qv hℓL) hℓS) ≠
        (ℓ : ResidueField 𝒪) + 1)

    (hcQ : OpComm N r qv S 𝒪 (HQ N r qv p πΔ)) (hdc : DiaComm N r qv S 𝒪 (HQ N r qv p πΔ))
    (hcR : OpComm N r qv S 𝒪 (HR N r qv)) :
    ∃ D : MonoidAlgebra 𝒪 (Delta qv p) →ₐ[𝒪]
        Module.End 𝒪 (ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ),

      (∀ u ∈ HR N r qv, D (MonoidAlgebra.of 𝒪 (Delta qv p) (piQ N r qv p πΔ u)) =
        diaML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc u) ∧

      (∀ δ : Delta qv p, ∃ u ∈ HR N r qv, piQ N r qv p πΔ u = δ) ∧

      Module.Finite 𝒪 (ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ) ∧

      ∃ b : Fin (Module.finrank 𝒪 (ML N r qv S 𝒪 (HR N r qv) θ α hcR)) →
          ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ,
        (∀ x : ML N r qv S 𝒪 (HQ N r qv p πΔ) θ α hcQ,
          ∃ c : Fin (Module.finrank 𝒪 (ML N r qv S 𝒪 (HR N r qv) θ α hcR)) →
              MonoidAlgebra 𝒪 (Delta qv p),
            x = ∑ i, D (c i) (b i)) ∧
        (∀ c : Fin (Module.finrank 𝒪 (ML N r qv S 𝒪 (HR N r qv) θ α hcR)) →
            MonoidAlgebra 𝒪 (Delta qv p),
          ∑ i, D (c i) (b i) = 0 ↔ ∀ i, c i = 0) :=
  main p hp𝒪 S N hNS r hr hr4 θ qv hqinj hq hqr α πΔ hπΔ hEis hcQ hdc hcR

end S_CuspForm_TWLevel_exists_algHom_monoidAlgebra_and_basis_ML_HQ
end P2MW
export P2MW.S_CuspForm_TWLevel_exists_algHom_monoidAlgebra_and_basis_ML_HQ (solution)
