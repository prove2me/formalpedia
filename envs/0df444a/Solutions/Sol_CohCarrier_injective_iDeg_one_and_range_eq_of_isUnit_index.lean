-- Prove2me | solution 1 for CohCarrier.injective_iDeg_one_and_range_eq_of_isUnit_index
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/4c184c9d-269c-5c45-8ad2-49decadcd5f1

import Mathlib.GroupTheory.Transfer
import Mathlib.GroupTheory.Index
import Definitions.Def_CohCarrier_Level
import Definitions.Def_CohCarrier_Inst
import Theorems.Thm_CohCarrier_coresAdd_comp_subtype
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_injective_iDeg_one_and_range_eq_of_isUnit_index

set_option autoImplicit false

open CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups

namespace K3ppU4

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ)

theorem conjLowerMat_one (A : SL(2, ℤ)) (h : ((1 : ℕ) : ℤ) ∣ A 1 0) :
    CohCarrier.conjLowerMat 1 A h = A := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [CohCarrier.conjLowerMat]

variable (h : CohCarrier.LevelLE M M ⊤ H 1)

theorem coe_iotaDeg_one (γ : ↥(CohCarrier.GammaH M H)) :
    ((CohCarrier.iotaDeg M M ⊤ H 1 h γ : ↥(CohCarrier.GammaH M ⊤)) : SL(2, ℤ)) = γ :=
  conjLowerMat_one (γ : SL(2, ℤ)) (h.dvd_entry γ)

noncomputable def unitsTop : ↥(CohCarrier.GammaH M ⊤) →* (ZMod M)ˣ :=
  (CohCarrier.gamma0Units M).comp (Subgroup.inclusion (CohCarrier.GammaH_le_Gamma0 (M := M) ⊤))

theorem unitsTop_surjective [NeZero M] : Function.Surjective (unitsTop M) := by
  intro u
  obtain ⟨σ, hσ⟩ := CohCarrier.gamma0Units_surjective M u
  have hσ' : (σ : SL(2, ℤ)) ∈ CohCarrier.GammaH M ⊤ := by
    rw [CohCarrier.GammaH_top]; exact σ.2
  refine ⟨⟨(σ : SL(2, ℤ)), hσ'⟩, ?_⟩
  rw [← hσ]
  rfl

theorem range_iotaDeg_one_eq_comap :
    (CohCarrier.iotaDeg M M ⊤ H 1 h).range = H.comap (unitsTop M) := by
  ext x
  constructor
  · rintro ⟨γ, rfl⟩
    obtain ⟨hγ0, hγH⟩ := CohCarrier.mem_GammaH_iff.mp γ.2
    rw [Subgroup.mem_comap]
    have hx : (CohCarrier.iotaDeg M M ⊤ H 1 h γ : SL(2, ℤ)) = γ := coe_iotaDeg_one M H h γ
    have : unitsTop M (CohCarrier.iotaDeg M M ⊤ H 1 h γ) = CohCarrier.gamma0Units M ⟨γ, hγ0⟩ := by
      show CohCarrier.gamma0Units M ⟨(CohCarrier.iotaDeg M M ⊤ H 1 h γ : SL(2, ℤ)), _⟩ = _
      congr 1
      exact Subtype.ext hx
    rw [this]
    exact hγH
  · intro hx
    rw [Subgroup.mem_comap] at hx
    have hx0 : (x : SL(2, ℤ)) ∈ Gamma0 M := CohCarrier.GammaH_le_Gamma0 ⊤ x.2
    have hxH : (x : SL(2, ℤ)) ∈ CohCarrier.GammaH M H :=
      CohCarrier.mem_GammaH_iff.mpr ⟨hx0, hx⟩
    refine ⟨⟨x, hxH⟩, Subtype.ext ?_⟩
    exact coe_iotaDeg_one M H h ⟨x, hxH⟩

theorem index_range_iotaDeg_one [NeZero M] :
    (CohCarrier.iotaDeg M M ⊤ H 1 h).range.index = H.index := by
  rw [range_iotaDeg_one_eq_comap, Subgroup.index_comap_of_surjective _ (unitsTop_surjective M)]

theorem range_iotaDeg_one_normal : ((CohCarrier.iotaDeg M M ⊤ H 1 h).range).Normal := by
  rw [range_iotaDeg_one_eq_comap]
  infer_instance

variable (A : Type) [AddCommGroup A]

theorem pushChar_apply (φ : CohCarrier.H1 M H A)
    (x : ↥((CohCarrier.iotaDeg M M ⊤ H 1 h).range)) (γ' : ↥(CohCarrier.GammaH M H))
    (hx : (x : ↥(CohCarrier.GammaH M ⊤)) = CohCarrier.iotaDeg M M ⊤ H 1 h γ') :
    CohCarrier.pushChar M M ⊤ H 1 A h φ (Additive.ofMul x) = φ (Additive.ofMul γ') := by
  have hinj := CohCarrier.iotaDeg_injective M M ⊤ H 1 h
  have hsymm : (MonoidHom.ofInjective hinj).symm x = γ' := by
    apply (MonoidHom.ofInjective hinj).injective
    rw [MulEquiv.apply_symm_apply]
    exact Subtype.ext hx
  show φ (Additive.ofMul ((MonoidHom.ofInjective hinj).symm.toMonoidHom x)) = _
  rw [MulEquiv.coe_toMonoidHom, hsymm]

theorem jDeg_iDeg_one [NeZero M] (φ : CohCarrier.H1 M ⊤ A) :
    CohCarrier.jDeg M M ⊤ H 1 A h (CohCarrier.iDeg' M M ⊤ H 1 A h φ) =
      (CohCarrier.iotaDeg M M ⊤ H 1 h).range.index • φ := by
  have hpush : CohCarrier.pushChar M M ⊤ H 1 A h (CohCarrier.iDeg' M M ⊤ H 1 A h φ) =
      φ.comp (Subgroup.subtype (CohCarrier.iotaDeg M M ⊤ H 1 h).range).toAdditive := by
    refine AddMonoidHom.ext fun x => ?_
    obtain ⟨γ', hγ'⟩ := (Additive.toMul x).2
    have hx : ((Additive.toMul x : ↥((CohCarrier.iotaDeg M M ⊤ H 1 h).range)) : ↥(CohCarrier.GammaH M ⊤)) =
        CohCarrier.iotaDeg M M ⊤ H 1 h γ' := hγ'.symm
    have := pushChar_apply M H h A (CohCarrier.iDeg' M M ⊤ H 1 A h φ) (Additive.toMul x) γ' hx
    rw [ofMul_toMul] at this
    rw [this]
    show φ (Additive.ofMul (CohCarrier.iotaDeg M M ⊤ H 1 h γ')) =
      φ (Additive.ofMul ((Additive.toMul x : ↥((CohCarrier.iotaDeg M M ⊤ H 1 h).range)) : ↥(CohCarrier.GammaH M ⊤)))
    rw [hx]
  show CohCarrier.coresAdd _ (CohCarrier.pushChar M M ⊤ H 1 A h (CohCarrier.iDeg' M M ⊤ H 1 A h φ)) = _
  rw [hpush, CohCarrier.coresAdd_comp_subtype]

end K3ppU4

namespace K3ppU4

theorem transfer_apply_of_normal {G : Type} [Group G] (K : Subgroup G) [K.FiniteIndex]
    [hK : K.Normal] {C : Type} [CommGroup C] (ψ : K →* C)
    (hψ : ∀ (g : G) (k : K) (hm : g⁻¹ * k * g ∈ K), ψ ⟨g⁻¹ * k * g, hm⟩ = ψ k) (k : K) :
    MonoidHom.transfer ψ k = ψ k ^ K.index := by
  classical
  letI := K.fintypeQuotientOfFiniteIndex
  set T : K.LeftTransversal := default with hT
  rw [MonoidHom.transfer_def ψ T k]
  simp only [Subgroup.leftTransversals.diff]
  rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card, ← Finset.card_univ, ← Finset.prod_const]
  refine Finset.prod_congr rfl fun q _ => ?_
  set α : G ⧸ K → G := fun q => (T.2.leftQuotientEquiv q : G) with hα
  have hq : (k : G)⁻¹ • q = q := by
    induction q using QuotientGroup.induction_on with
    | H g =>
      rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, smul_eq_mul]
      have : ((k : G)⁻¹ * g)⁻¹ * g = g⁻¹ * k * g := by group
      rw [this]
      exact hK.conj_mem' _ k.2 g
  have hβ : (((k : G) • T).2.leftQuotientEquiv q : G) = k * α q := by
    rw [Subgroup.smul_apply_eq_smul_apply_inv_smul, hq]
    rfl
  have key : ∀ (x : K), (x : G) = (α q)⁻¹ * (k * α q) → ψ x = ψ k := fun x hx => by
    have hm : (α q)⁻¹ * k * (α q) ∈ K := by
      have := x.2
      rw [hx, ← mul_assoc] at this
      exact this
    have : x = ⟨(α q)⁻¹ * k * (α q), hm⟩ := Subtype.ext (by
      show (x : G) = (α q)⁻¹ * k * (α q)
      rw [hx, mul_assoc])
    rw [this]
    exact hψ (α q) k hm
  apply key
  show (α q)⁻¹ * (((k : G) • T).2.leftQuotientEquiv q : G) = _
  rw [hβ]

end K3ppU4

namespace K3ppU4

section Descent

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (h : CohCarrier.LevelLE M M ⊤ H 1)
variable (A : Type) [AddCommGroup A]

def ofGamma0 (σ : Gamma0 M) : ↥(CohCarrier.GammaH M ⊤) :=
  ⟨σ, by rw [CohCarrier.GammaH_top]; exact σ.2⟩

@[scoped simp] theorem coe_ofGamma0 (σ : Gamma0 M) : ((ofGamma0 M σ : ↥(CohCarrier.GammaH M ⊤)) : SL(2, ℤ)) = σ :=
  rfl

def toGamma0 (g : ↥(CohCarrier.GammaH M ⊤)) : Gamma0 M := ⟨g, CohCarrier.GammaH_le_Gamma0 ⊤ g.2⟩

@[scoped simp] theorem coe_toGamma0 (g : ↥(CohCarrier.GammaH M ⊤)) : ((toGamma0 M g : Gamma0 M) : SL(2, ℤ)) = g :=
  rfl

theorem iotaDeg_conjHom (σ : Gamma0 M) (γ : ↥(CohCarrier.GammaH M H)) :
    CohCarrier.iotaDeg M M ⊤ H 1 h (CohCarrier.conjHom M H σ γ) =
      ofGamma0 M σ * CohCarrier.iotaDeg M M ⊤ H 1 h γ * (ofGamma0 M σ)⁻¹ := by
  apply Subtype.ext
  rw [coe_iotaDeg_one]
  simp only [Subgroup.coe_mul, InvMemClass.coe_inv, coe_ofGamma0, coe_iotaDeg_one]
  rfl

theorem iotaDeg_conjHom_inv (g : ↥(CohCarrier.GammaH M ⊤)) (γ : ↥(CohCarrier.GammaH M H)) :
    CohCarrier.iotaDeg M M ⊤ H 1 h (CohCarrier.conjHom M H (toGamma0 M g)⁻¹ γ) =
      g⁻¹ * CohCarrier.iotaDeg M M ⊤ H 1 h γ * g := by
  apply Subtype.ext
  rw [coe_iotaDeg_one]
  simp only [Subgroup.coe_mul, InvMemClass.coe_inv, coe_iotaDeg_one]
  show ((toGamma0 M g)⁻¹ : Gamma0 M) * (γ : SL(2, ℤ)) * (((toGamma0 M g)⁻¹ : Gamma0 M) : SL(2, ℤ))⁻¹ = _
  simp only [InvMemClass.coe_inv, coe_toGamma0, inv_inv]

theorem apply_conjHom_of_invariant (φ : CohCarrier.H1 M H A)
    (hinv : ∀ σ : Gamma0 M, CohCarrier.diamondRaw M H A σ φ = φ) (σ : Gamma0 M)
    (γ : ↥(CohCarrier.GammaH M H)) :
    φ (Additive.ofMul (CohCarrier.conjHom M H σ γ)) = φ (Additive.ofMul γ) :=
  DFunLike.congr_fun (hinv σ) (Additive.ofMul γ)

theorem iDeg_jDeg_one_of_invariant [NeZero M] (φ : CohCarrier.H1 M H A)
    (hinv : ∀ σ : Gamma0 M, CohCarrier.diamondRaw M H A σ φ = φ) :
    CohCarrier.iDeg' M M ⊤ H 1 A h (CohCarrier.jDeg M M ⊤ H 1 A h φ) =
      (CohCarrier.iotaDeg M M ⊤ H 1 h).range.index • φ := by
  haveI := range_iotaDeg_one_normal M H h
  set K := (CohCarrier.iotaDeg M M ⊤ H 1 h).range with hK
  set ψa := CohCarrier.pushChar M M ⊤ H 1 A h φ with hψa

  have hψ : ∀ (g : ↥(CohCarrier.GammaH M ⊤)) (x : K) (hm : g⁻¹ * x * g ∈ K),
      AddMonoidHom.toMultiplicativeRight ψa ⟨g⁻¹ * x * g, hm⟩ =
        AddMonoidHom.toMultiplicativeRight ψa x := by
    intro g x hm
    obtain ⟨γ', hγ'⟩ := x.2
    have hx : (((⟨g⁻¹ * x * g, hm⟩ : K) : ↥(CohCarrier.GammaH M ⊤))) =
        CohCarrier.iotaDeg M M ⊤ H 1 h (CohCarrier.conjHom M H (toGamma0 M g)⁻¹ γ') := by
      rw [iotaDeg_conjHom_inv, hγ']
    simp only [AddMonoidHom.toMultiplicativeRight_apply_apply]
    rw [pushChar_apply M H h A φ _ _ hx, pushChar_apply M H h A φ x γ' hγ'.symm,
      apply_conjHom_of_invariant M H A φ hinv]
  refine AddMonoidHom.ext fun a => ?_
  set γ := Additive.toMul a with hγ
  have ha : a = Additive.ofMul γ := (ofMul_toMul a).symm
  set k : K := ⟨CohCarrier.iotaDeg M M ⊤ H 1 h γ, γ, rfl⟩ with hk

  have hL : CohCarrier.iDeg' M M ⊤ H 1 A h (CohCarrier.jDeg M M ⊤ H 1 A h φ) a =
      Additive.toMul.symm ((MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight ψa)) (k : ↥(CohCarrier.GammaH M ⊤))) := by
    rfl
  rw [hL, transfer_apply_of_normal K (AddMonoidHom.toMultiplicativeRight ψa) hψ k]
  simp only [AddMonoidHom.toMultiplicativeRight_apply_apply, ← ofAdd_nsmul]
  rw [pushChar_apply M H h A φ k γ rfl, ha, AddMonoidHom.nsmul_apply]
  rfl

theorem diamondRaw_iDeg_one (φ : CohCarrier.H1 M ⊤ A) (σ : Gamma0 M) :
    CohCarrier.diamondRaw M H A σ (CohCarrier.iDeg' M M ⊤ H 1 A h φ) =
      CohCarrier.iDeg' M M ⊤ H 1 A h φ := by
  refine AddMonoidHom.ext fun a => ?_
  show φ (Additive.ofMul (CohCarrier.iotaDeg M M ⊤ H 1 h (CohCarrier.conjHom M H σ (Additive.toMul a)))) =
    φ (Additive.ofMul (CohCarrier.iotaDeg M M ⊤ H 1 h (Additive.toMul a)))
  rw [iotaDeg_conjHom, ofMul_mul, ofMul_mul, ofMul_inv, map_add, map_add, map_neg]
  abel

end Descent

theorem main (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (R : Type) [CommRing R] (A : Type) [AddCommGroup A] [Module R A]
    (h : CohCarrier.LevelLE M M ⊤ H 1)
    (hunit : IsUnit ((H.index : ℕ) : R)) :
    (CohCarrier.iotaDeg M M ⊤ H 1 h).range.index = H.index ∧
    Function.Injective (CohCarrier.iDeg' M M ⊤ H 1 A h) ∧
    Set.range (CohCarrier.iDeg' M M ⊤ H 1 A h) =
      {φ | ∀ σ : Gamma0 M, CohCarrier.diamondRaw M H A σ φ = φ} ∧
    ∀ φ : CohCarrier.H1 M H A, (∀ σ : Gamma0 M, CohCarrier.diamondRaw M H A σ φ = φ) →
      CohCarrier.iDeg' M M ⊤ H 1 A h (CohCarrier.jDeg M M ⊤ H 1 A h φ) = H.index • φ := by
  have hidx := index_range_iotaDeg_one M H h
  have hformula : ∀ φ : CohCarrier.H1 M H A, (∀ σ : Gamma0 M, CohCarrier.diamondRaw M H A σ φ = φ) →
      CohCarrier.iDeg' M M ⊤ H 1 A h (CohCarrier.jDeg M M ⊤ H 1 A h φ) = H.index • φ := by
    intro φ hφ
    rw [← hidx]
    exact iDeg_jDeg_one_of_invariant M H h A φ hφ
  have hlin : ∀ (c : R) (ψ : CohCarrier.H1 M ⊤ A),
      CohCarrier.iDeg' M M ⊤ H 1 A h (c • ψ) = c • CohCarrier.iDeg' M M ⊤ H 1 A h ψ := fun c ψ =>
    (CohCarrier.iDegL M M ⊤ H 1 A R h).map_smul c ψ
  refine ⟨hidx, ?_, ?_, hformula⟩
  · intro φ₁ φ₂ heq
    have := congrArg (CohCarrier.jDeg M M ⊤ H 1 A h) heq
    rw [jDeg_iDeg_one, jDeg_iDeg_one, hidx, ← Nat.cast_smul_eq_nsmul R,
      ← Nat.cast_smul_eq_nsmul R] at this
    exact (hunit.smul_left_cancel).mp this
  · ext φ
    constructor
    · rintro ⟨φ₀, rfl⟩ σ
      exact diamondRaw_iDeg_one M H h A φ₀ σ
    · intro hφ
      obtain ⟨u, hu⟩ := hunit
      refine ⟨((u⁻¹ : Rˣ) : R) • CohCarrier.jDeg M M ⊤ H 1 A h φ, ?_⟩
      rw [hlin, hformula φ hφ, ← Nat.cast_smul_eq_nsmul R, ← hu, smul_smul, Units.inv_mul,
        one_smul]

end K3ppU4
p2m_reactivate "P2MW.S_CohCarrier_injective_iDeg_one_and_range_eq_of_isUnit_index.K3ppU4"

open CongruenceSubgroup in
theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (R : Type) [CommRing R] (A : Type) [AddCommGroup A] [Module R A]
    (h : CohCarrier.LevelLE M M ⊤ H 1)
    (hunit : IsUnit ((H.index : ℕ) : R)) :
    (CohCarrier.iotaDeg M M ⊤ H 1 h).range.index = H.index ∧
    Function.Injective (CohCarrier.iDeg' M M ⊤ H 1 A h) ∧
    Set.range (CohCarrier.iDeg' M M ⊤ H 1 A h) =
      {φ | ∀ σ : Gamma0 M, CohCarrier.diamondRaw M H A σ φ = φ} ∧
    ∀ φ : CohCarrier.H1 M H A, (∀ σ : Gamma0 M, CohCarrier.diamondRaw M H A σ φ = φ) →
      CohCarrier.iDeg' M M ⊤ H 1 A h (CohCarrier.jDeg M M ⊤ H 1 A h φ) = H.index • φ :=
  K3ppU4.main M H R A h hunit

end S_CohCarrier_injective_iDeg_one_and_range_eq_of_isUnit_index
end P2MW
export P2MW.S_CohCarrier_injective_iDeg_one_and_range_eq_of_isUnit_index (solution)
