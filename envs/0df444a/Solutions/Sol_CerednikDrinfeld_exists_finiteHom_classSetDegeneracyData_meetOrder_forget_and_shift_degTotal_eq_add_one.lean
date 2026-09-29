-- Prove2me | solution 1 for CerednikDrinfeld.exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/a3e15f08-7920-5ba2-a84c-efa4d9146561

import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_AlgebraicCurve_TotallyDegenerateCovering_Hom
import Theorems.Thm_Submodule_finiteAdeleBox_conjByFiniteIdele
import Theorems.Thm_Submodule_conjByFiniteIdele_mul_eq_of_mem_finiteIdeleStabilizer
import Theorems.Thm_QuaternionAlgebra_IsOrder_finiteAdeleBox_inf_conjByFiniteIdele_eq_and_finiteIdeleStabilizer_le
import Theorems.Thm_QuaternionAlgebra_IsOrder_conjByFiniteIdele
import Theorems.Thm_QuaternionAlgebra_IsOrder_finite_isUnitOf_and_nrd_eq_one
import Theorems.Thm_QuaternionAlgebra_IsOrder_isUnitOf_conjByFiniteIdele_iff
import Theorems.Thm_Subgroup_sum_fibre_doubleCoset_relIndex_inf_map_conj_eq_relIndex
import Theorems.Thm_Subgroup_sum_fibre_doubleCoset_relIndex_inf_map_conj_eq_relIndex_of_le_inf
import Theorems.Thm_CerednikDrinfeld_relIndex_finiteIdeleStabilizer_meetOrder_eq_succ_of_mem_primeHeckeSet
import Theorems.Thm_QuaternionAlgebra_mem_primeHeckeSet_iff_finiteIdeleDiagonal_mul_inv_mem
import Theorems.Thm_QuaternionAlgebra_primeHeckeSet_eq_doubleCoset_finiteIdeleStabilizer
import Theorems.Thm_Submodule_mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox
import Theorems.Thm_Submodule_localBox_inf
import Theorems.Thm_Submodule_mem_localBox_conjByFiniteIdele_iff
import Theorems.Thm_QuaternionAlgebra_IsOrder_mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits
import Theorems.Thm_Submodule_exists_units_finiteAdeleEvalAt_eq
import Theorems.Thm_CerednikDrinfeld_exists_mul_self_eq_finiteIdeleDiagonal_mul_and_mem_finiteIdeleStabilizer_meetOrder_of_conjByFiniteIdele_mul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val"

set_option autoImplicit false

namespace DoubleCosetFibre

open scoped Pointwise
open MulAction

variable {G : Type*} [Group G]

def stabH (H K : Subgroup G) (g : G) : Subgroup G := H ⊓ K.map (MulAut.conj g).toMonoidHom

theorem mem_stabH {H K : Subgroup G} {g h : G} : h ∈ stabH H K g ↔ h ∈ H ∧ g⁻¹ * h * g ∈ K := by
  unfold stabH
  rw [Subgroup.mem_inf, Subgroup.mem_map]
  constructor
  · rintro ⟨hH, k, hk, rfl⟩
    refine ⟨hH, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
    exact hk
  · rintro ⟨hH, hk⟩
    refine ⟨hH, g⁻¹ * h * g, hk, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem stabH_mono {H K K' : Subgroup G} (hK : K' ≤ K) (g : G) : stabH H K' g ≤ stabH H K g := by
  intro h hh
  rw [mem_stabH] at hh ⊢
  exact ⟨hh.1, hK hh.2⟩

theorem stabH_mul (H K : Subgroup G) (g h k : G) (hh : h ∈ H) (hk : k ∈ K) :
    stabH H K (h * g * k) = (stabH H K g).map (MulAut.conj h).toMonoidHom := by
  ext y
  rw [mem_stabH, Subgroup.mem_map]
  constructor
  · rintro ⟨hyH, hyK⟩
    refine ⟨h⁻¹ * y * h, ?_, ?_⟩
    · rw [mem_stabH]
      refine ⟨H.mul_mem (H.mul_mem (H.inv_mem hh) hyH) hh, ?_⟩
      have : g⁻¹ * (h⁻¹ * y * h) * g = k * ((h * g * k)⁻¹ * y * (h * g * k)) * k⁻¹ := by group
      rw [this]
      exact K.mul_mem (K.mul_mem hk hyK) (K.inv_mem hk)
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  · rintro ⟨z, hz, rfl⟩
    rw [mem_stabH] at hz
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine ⟨H.mul_mem (H.mul_mem hh hz.1) (H.inv_mem hh), ?_⟩
    have : (h * g * k)⁻¹ * (h * z * h⁻¹) * (h * g * k) = k⁻¹ * (g⁻¹ * z * g) * k := by group
    rw [this]
    exact K.mul_mem (K.mul_mem (K.inv_mem hk) hz.2) hk

theorem stabH_mul_right (H K : Subgroup G) (g k : G) (hk : k ∈ K) : stabH H K (g * k) = stabH H K g := by
  ext y
  rw [mem_stabH, mem_stabH]
  constructor
  · rintro ⟨hyH, hyK⟩
    refine ⟨hyH, ?_⟩
    have : g⁻¹ * y * g = k * ((g * k)⁻¹ * y * (g * k)) * k⁻¹ := by group
    rw [this]
    exact K.mul_mem (K.mul_mem hk hyK) (K.inv_mem hk)
  · rintro ⟨hyH, hyK⟩
    refine ⟨hyH, ?_⟩
    have : (g * k)⁻¹ * y * (g * k) = k⁻¹ * (g⁻¹ * y * g) * k := by group
    rw [this]
    exact K.mul_mem (K.mul_mem (K.inv_mem hk) hyK) hk

theorem relIndex_stabH_mul (H K K' : Subgroup G) (hK : K' ≤ K) (g h k : G) (hh : h ∈ H) (hk : k ∈ K') :
    (stabH H K' (h * g * k)).relIndex (stabH H K (h * g * k)) = (stabH H K' g).relIndex (stabH H K g) := by
  rw [stabH_mul H K' g h k hh hk, stabH_mul H K g h k hh (hK hk)]
  exact Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj h).injective

section PartOne

variable (H K K' : Subgroup G) (hK : K' ≤ K) (x : G)

include hK

omit hK in

abbrev Fibre : Type _ :=
  {c : DoubleCoset.Quotient (H : Set G) (K' : Set G) // DoubleCoset.mk H K c.out = DoubleCoset.mk H K x}

omit hK in

def toK : stabH H K x →* K where
  toFun h := ⟨x⁻¹ * h * x, (mem_stabH.mp h.2).2⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' a b := by apply Subtype.ext; simp only [Subgroup.coe_mul]; group

omit hK in
scoped instance actY : MulAction (stabH H K x) (K ⧸ K'.subgroupOf K) :=
  MulAction.compHom _ (toK H K x)

omit hK in
theorem smul_mk (h : stabH H K x) (k : K) :
    h • (QuotientGroup.mk k : K ⧸ K'.subgroupOf K) = QuotientGroup.mk (toK H K x h * k) := rfl

def psi : K ⧸ K'.subgroupOf K → Fibre H K K' x :=
  Quotient.lift (fun k : K => (⟨DoubleCoset.mk H K' (x * k), by
      obtain ⟨h, k', hh, hk', he⟩ := (DoubleCoset.mk_out_eq_mul H K' (x * k))
      rw [he, DoubleCoset.eq]
      exact ⟨h⁻¹, H.inv_mem hh, ((k : G) * k')⁻¹, K.inv_mem (K.mul_mem k.2 (hK hk')), by group⟩⟩ : Fibre H K K' x))
    (by
      intro k₁ k₂ hrel
      apply Subtype.ext
      simp only
      rw [DoubleCoset.eq]
      have : (k₁⁻¹ * k₂ : K) ∈ K'.subgroupOf K := QuotientGroup.leftRel_apply.mp hrel
      rw [Subgroup.mem_subgroupOf] at this
      exact ⟨1, H.one_mem, k₁⁻¹ * k₂, this, by simp [mul_assoc]⟩)

theorem psi_mk (k : K) : (psi H K K' hK x (QuotientGroup.mk k) : Fibre H K K' x).1 = DoubleCoset.mk H K' (x * k) := rfl

theorem psi_surjective : Function.Surjective (psi H K K' hK x) := by
  rintro ⟨c, hc⟩
  have hout := DoubleCoset.out_eq' H K' c

  obtain ⟨h, hh, k, hk, he⟩ := (DoubleCoset.eq H K _ _).mp hc.symm

  refine ⟨QuotientGroup.mk ⟨k, hk⟩, ?_⟩
  apply Subtype.ext
  simp only [psi_mk]
  rw [← hout, DoubleCoset.eq]
  exact ⟨h, hh, 1, K'.one_mem, by rw [he]; group⟩

theorem psi_eq_psi_iff (k₁ k₂ : K) :
    psi H K K' hK x (QuotientGroup.mk k₁) = psi H K K' hK x (QuotientGroup.mk k₂) ↔
      ∃ h : stabH H K x, h • (QuotientGroup.mk k₁ : K ⧸ K'.subgroupOf K) = QuotientGroup.mk k₂ := by
  constructor
  · intro he
    have he' := congrArg Subtype.val he
    simp only [psi_mk] at he'
    rw [DoubleCoset.eq] at he'
    obtain ⟨h, hh, k', hk', he'⟩ := he'

    have hhx : h ∈ stabH H K x := by
      rw [mem_stabH]
      refine ⟨hh, ?_⟩
      have e3 : k' = (h * (x * k₁))⁻¹ * (x * k₂) := by rw [he']; group
      have : x⁻¹ * h * x = (k₂ : G) * k'⁻¹ * (k₁ : G)⁻¹ := by rw [e3]; group
      rw [this]
      exact K.mul_mem (K.mul_mem k₂.2 (K.inv_mem (hK hk'))) (K.inv_mem k₁.2)
    refine ⟨⟨h, hhx⟩, ?_⟩
    rw [smul_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    show ((x⁻¹ * h * x * k₁ : G))⁻¹ * k₂ ∈ K'
    have e3 : k' = (h * (x * k₁))⁻¹ * (x * k₂) := by rw [he']; group
    have : ((x⁻¹ * h * x * k₁ : G))⁻¹ * k₂ = k' := by rw [e3]; group
    rw [this]; exact hk'
  · rintro ⟨h, hh⟩
    rw [← hh, smul_mk]
    apply Subtype.ext
    simp only [psi_mk]
    rw [DoubleCoset.eq]
    refine ⟨h, (mem_stabH.mp h.2).1, 1, K'.one_mem, ?_⟩
    show (x * (x⁻¹ * (h : G) * x * k₁) : G) = h * (x * k₁) * 1
    group

theorem psi_smul (h : stabH H K x) (y : K ⧸ K'.subgroupOf K) :
    psi H K K' hK x (h • y) = psi H K K' hK x y := by
  induction y using QuotientGroup.induction_on with
  | H k => exact ((psi_eq_psi_iff H K K' hK x k (toK H K x h * k)).mpr ⟨h, rfl⟩).symm

noncomputable def orbitEquiv : orbitRel.Quotient (stabH H K x) (K ⧸ K'.subgroupOf K) ≃ Fibre H K K' x :=
  Equiv.ofBijective
    (Quotient.lift (fun y => psi H K K' hK x y) (by
      intro y₁ y₂ hrel
      obtain ⟨h, rfl⟩ := hrel
      exact psi_smul H K K' hK x h y₂))
    ⟨by
      intro O₁ O₂ he
      induction O₁ using Quotient.inductionOn with
      | h y₁ =>
      induction O₂ using Quotient.inductionOn with
      | h y₂ =>
      induction y₁ using QuotientGroup.induction_on with
      | H k₁ =>
      induction y₂ using QuotientGroup.induction_on with
      | H k₂ =>
      obtain ⟨h, hh⟩ := (psi_eq_psi_iff H K K' hK x k₁ k₂).mp he
      exact Quotient.sound ⟨h⁻¹, by rw [← hh]; exact inv_smul_smul h _⟩,
     by
      intro c
      obtain ⟨y, rfl⟩ := psi_surjective H K K' hK x c
      exact ⟨Quotient.mk _ y, rfl⟩⟩

theorem stabilizer_eq (k : K) :
    (stabilizer (stabH H K x) (QuotientGroup.mk k : K ⧸ K'.subgroupOf K)).map (stabH H K x).subtype =
      stabH H K' (x * k) := by
  ext g
  rw [Subgroup.mem_map, mem_stabH]
  constructor
  · rintro ⟨h, hh, rfl⟩
    rw [mem_stabilizer_iff, smul_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hh
    have hh' := hh
    refine ⟨(mem_stabH.mp h.2).1, ?_⟩
    show (x * (k : G))⁻¹ * (h : G) * (x * k) ∈ K'

    have : (x * k : G)⁻¹ * h * (x * k) = (((toK H K x h * k : K) : G)⁻¹ * k)⁻¹ := by
      show (x * k : G)⁻¹ * h * (x * k) = ((x⁻¹ * h * x * k : G)⁻¹ * k)⁻¹
      group
    rw [this]
    exact K'.inv_mem hh'
  · rintro ⟨hgH, hgK'⟩
    have hgx : g ∈ stabH H K x := by
      rw [mem_stabH]
      refine ⟨hgH, ?_⟩
      have : x⁻¹ * g * x = (k : G) * ((x * k)⁻¹ * g * (x * k)) * (k : G)⁻¹ := by group
      rw [this]
      exact K.mul_mem (K.mul_mem k.2 (hK hgK')) (K.inv_mem k.2)
    refine ⟨⟨g, hgx⟩, ?_, rfl⟩
    rw [mem_stabilizer_iff, smul_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    show ((x⁻¹ * g * x * k : G))⁻¹ * k ∈ K'
    have : ((x⁻¹ * g * x * k : G))⁻¹ * k = ((x * k)⁻¹ * g * (x * k))⁻¹ := by group
    rw [this]
    exact K'.inv_mem hgK'

theorem relIndex_eq_card_orbit (k : K) [Finite (K ⧸ K'.subgroupOf K)] :
    (stabH H K' (x * k)).relIndex (stabH H K x) =
      Nat.card (orbit (stabH H K x) (QuotientGroup.mk k : K ⧸ K'.subgroupOf K)) := by
  rw [Subgroup.relIndex, ← stabilizer_eq H K K' hK x k, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _), index_stabilizer,
    ← Nat.card_coe_set_eq]

omit hK in

theorem card_eq_sum_card_orbits [Fintype (K ⧸ K'.subgroupOf K)]
    [Fintype (orbitRel.Quotient (stabH H K x) (K ⧸ K'.subgroupOf K))] :
    Fintype.card (K ⧸ K'.subgroupOf K) =
      ∑ O : orbitRel.Quotient (stabH H K x) (K ⧸ K'.subgroupOf K), Nat.card (orbit (stabH H K x) O.out) := by
  classical
  rw [Fintype.card_congr (selfEquivSigmaOrbits (stabH H K x) (K ⧸ K'.subgroupOf K)), Fintype.card_sigma]
  refine Finset.sum_congr rfl fun O _ => ?_
  rw [Nat.card_eq_fintype_card]

theorem sum_fibre_relIndex_stabH_eq_relIndex [K'.IsFiniteRelIndex K]
    [Fintype (Fibre H K K' x)] :
    ∑ c : Fibre H K K' x, (stabH H K' c.1.out).relIndex (stabH H K c.1.out) = K'.relIndex K := by
  classical
  haveI : Finite (K ⧸ K'.subgroupOf K) := Subgroup.finite_quotient_of_finiteIndex
  haveI : Fintype (K ⧸ K'.subgroupOf K) := Fintype.ofFinite _
  haveI : Fintype (orbitRel.Quotient (stabH H K x) (K ⧸ K'.subgroupOf K)) :=
    Fintype.ofEquiv _ (orbitEquiv H K K' hK x).symm

  rw [← Fintype.sum_equiv (orbitEquiv H K K' hK x)
    (fun O => Nat.card (orbit (stabH H K x) O.out))
    (fun c => (stabH H K' c.1.out).relIndex (stabH H K c.1.out)) ?_]
  · rw [← card_eq_sum_card_orbits H K K' x, Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]
  · intro O
    induction O using Quotient.inductionOn with
    | h y =>
    induction y using QuotientGroup.induction_on with
    | H k =>
    show Nat.card (orbit (stabH H K x)
        (Quotient.mk (orbitRel (stabH H K x) (K ⧸ K'.subgroupOf K)) (QuotientGroup.mk k : K ⧸ K'.subgroupOf K)).out) =
      (stabH H K' (DoubleCoset.mk H K' (x * (k : G))).out).relIndex (stabH H K (DoubleCoset.mk H K' (x * (k : G))).out)
    obtain ⟨h₀, hh₀⟩ : ∃ h₀ : stabH H K x, h₀ • (QuotientGroup.mk k : K ⧸ K'.subgroupOf K) =
        (Quotient.mk (orbitRel (stabH H K x) (K ⧸ K'.subgroupOf K)) (QuotientGroup.mk k : K ⧸ K'.subgroupOf K)).out :=
      orbitRel_apply.mp (Quotient.mk_out (s := orbitRel (stabH H K x) (K ⧸ K'.subgroupOf K))
        (QuotientGroup.mk k : K ⧸ K'.subgroupOf K))
    rw [← hh₀, orbit_smul, ← relIndex_eq_card_orbit H K K' hK x k]
    obtain ⟨h, k', hh, hk', he⟩ := DoubleCoset.mk_out_eq_mul H K' (x * k)
    rw [he, relIndex_stabH_mul H K K' hK (x * k) h k' hh hk', stabH_mul_right H K x k k.2]

end PartOne

theorem sum_filter_card_orbit_eq_card {M α : Type*} [Group M] [MulAction M α] [Fintype α]
    [Fintype (orbitRel.Quotient M α)] (A : Set α) [DecidablePred (· ∈ A)]
    (P : orbitRel.Quotient M α → Prop) [DecidablePred P]
    (hP : ∀ a : α, P (Quotient.mk (orbitRel M α) a) ↔ a ∈ A) :
    ∑ O ∈ Finset.univ.filter P, Nat.card (orbit M O.out) = Fintype.card A := by
  classical
  have hmaps : ∀ a ∈ Finset.univ.filter (fun a : α => a ∈ A),
      Quotient.mk (orbitRel M α) a ∈ Finset.univ.filter P := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact (hP a).mpr ha
  rw [← Set.toFinset_card, show A.toFinset = Finset.univ.filter (fun a : α => a ∈ A) by ext a; simp,
    Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl fun O hO => ?_
  have hPO : P O := (Finset.mem_filter.mp hO).2

  have hfib : (Finset.univ.filter (fun a : α => a ∈ A)).filter (fun a => Quotient.mk (orbitRel M α) a = O) =
      (orbit M O.out).toFinset := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset]
    constructor
    · rintro ⟨-, ha⟩
      have : Quotient.mk (orbitRel M α) a = Quotient.mk (orbitRel M α) O.out := by rw [ha, Quotient.out_eq]
      exact orbitRel_apply.mp (Quotient.exact this)
    · intro ha
      have hq : Quotient.mk (orbitRel M α) a = O := by
        rw [← Quotient.out_eq O]
        exact Quotient.sound (orbitRel_apply.mpr ha)
      refine ⟨?_, hq⟩
      exact (hP a).mp (hq ▸ hPO)
  rw [hfib, Set.toFinset_card, Nat.card_eq_fintype_card]

section Harmonic

variable (H K K₁ K₂ K₁₂ : Subgroup G) (hK₁ : K₁ ≤ K) (hK₂ : K₂ ≤ K)
  (h₁ : K₁₂ ≤ K₁) (h₂ : K₁₂ ≤ K₂) (hinf : K₁ ⊓ K₂ ≤ K₁₂)
  (hsurj : ∀ k : K, ∃ k₁ : K₁, ((k₁ : G)⁻¹ * k) ∈ K₂) (z : G)

def theta : K₁ ⧸ K₁₂.subgroupOf K₁ → K ⧸ K₂.subgroupOf K :=
  Quotient.map' (fun k₁ : K₁ => (⟨(k₁ : G), hK₁ k₁.2⟩ : K)) (by
    intro a b hab
    rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at hab ⊢
    exact h₂ hab)

theorem theta_mk (k₁ : K₁) :
    theta K K₁ K₂ K₁₂ hK₁ h₂ (QuotientGroup.mk k₁) = QuotientGroup.mk (⟨(k₁ : G), hK₁ k₁.2⟩ : K) := rfl

include hsurj hinf in
theorem theta_bijective : Function.Bijective (theta K K₁ K₂ K₁₂ hK₁ h₂) := by
  constructor
  · intro a b hab
    induction a using QuotientGroup.induction_on with
    | H a =>
    induction b using QuotientGroup.induction_on with
    | H b =>
    rw [theta_mk, theta_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hab
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    exact hinf (Subgroup.mem_inf.mpr ⟨K₁.mul_mem (K₁.inv_mem a.2) b.2, hab⟩)
  · intro c
    induction c using QuotientGroup.induction_on with
    | H k =>
    obtain ⟨k₁, hk₁⟩ := hsurj k
    refine ⟨QuotientGroup.mk k₁, ?_⟩
    rw [theta_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    exact hk₁

theorem theta_smul (h : stabH H K₁ z) (a : K₁ ⧸ K₁₂.subgroupOf K₁) :
    theta K K₁ K₂ K₁₂ hK₁ h₂ (h • a) = (Subgroup.inclusion (stabH_mono (H := H) hK₁ z) h) • theta K K₁ K₂ K₁₂ hK₁ h₂ a := by
  induction a using QuotientGroup.induction_on with
  | H k₁ =>
  rw [smul_mk, theta_mk, theta_mk, smul_mk]
  rfl

variable (y : G) (hyz : DoubleCoset.mk H K z = DoubleCoset.mk H K y)

abbrev Fibre₂ : Type _ :=
  {c : DoubleCoset.Quotient (H : Set G) (K₁₂ : Set G) //
    DoubleCoset.mk H K₂ c.out = DoubleCoset.mk H K₂ y ∧ DoubleCoset.mk H K₁ c.out = DoubleCoset.mk H K₁ z}

include hK₁ hK₂ h₁ h₂ hinf hyz hsurj in

theorem sum_fibre₂_relIndex_stabH_eq [K₂.IsFiniteRelIndex K] [K₁₂.IsFiniteRelIndex K₁]
    [Fintype (Fibre₂ H K₁ K₂ K₁₂ z y)] :
    ∑ c : Fibre₂ H K₁ K₂ K₁₂ z y, (stabH H K₁₂ c.1.out).relIndex (stabH H K₁ c.1.out) =
      (stabH H K₂ y).relIndex (stabH H K y) := by
  classical

  have hK₁₂le : K₁₂ ≤ K₁ := h₁
  haveI : Finite (K ⧸ K₂.subgroupOf K) := Subgroup.finite_quotient_of_finiteIndex
  haveI : Fintype (K ⧸ K₂.subgroupOf K) := Fintype.ofFinite _
  haveI : Finite (K₁ ⧸ K₁₂.subgroupOf K₁) := Subgroup.finite_quotient_of_finiteIndex
  haveI : Fintype (K₁ ⧸ K₁₂.subgroupOf K₁) := Fintype.ofFinite _

  obtain ⟨h₀, hh₀, k₀, hk₀, hy⟩ := (DoubleCoset.eq H K z y).mp hyz
  set y₀ : K ⧸ K₂.subgroupOf K := QuotientGroup.mk ⟨k₀, hk₀⟩ with hy₀def
  let Ω : Set (K ⧸ K₂.subgroupOf K) := orbit (stabH H K z) y₀
  let A : Set (K₁ ⧸ K₁₂.subgroupOf K₁) := (theta K K₁ K₂ K₁₂ hK₁ h₂) ⁻¹' Ω

  have hcond : ∀ k₁ : K₁, DoubleCoset.mk H K₂ (z * k₁) = DoubleCoset.mk H K₂ y ↔
      theta K K₁ K₂ K₁₂ hK₁ h₂ (QuotientGroup.mk k₁) ∈ Ω := by
    intro k₁
    rw [theta_mk, hy]
    have e1 : DoubleCoset.mk H K₂ (h₀ * z * k₀) = DoubleCoset.mk H K₂ (z * k₀) := by
      rw [DoubleCoset.eq]; exact ⟨h₀⁻¹, H.inv_mem hh₀, 1, K₂.one_mem, by group⟩
    rw [e1]

    have key := psi_eq_psi_iff H K K₂ hK₂ z (⟨(k₁ : G), hK₁ k₁.2⟩ : K) ⟨k₀, hk₀⟩
    have e2 : ∀ k : K, ((psi H K K₂ hK₂ z (QuotientGroup.mk k) : Fibre H K K₂ z).1) = DoubleCoset.mk H K₂ (z * k) :=
      fun k => rfl
    constructor
    · intro hk
      have : psi H K K₂ hK₂ z (QuotientGroup.mk (⟨(k₁ : G), hK₁ k₁.2⟩ : K)) = psi H K K₂ hK₂ z (QuotientGroup.mk ⟨k₀, hk₀⟩) := by
        apply Subtype.ext; rw [e2, e2]; exact hk
      obtain ⟨h, hh⟩ := key.mp this
      exact mem_orbit_iff.mpr ⟨h⁻¹, by rw [hy₀def, ← hh, inv_smul_smul]⟩
    · intro hk
      obtain ⟨h, hh⟩ := mem_orbit_iff.mp hk
      have : psi H K K₂ hK₂ z (QuotientGroup.mk (⟨(k₁ : G), hK₁ k₁.2⟩ : K)) = psi H K K₂ hK₂ z (QuotientGroup.mk ⟨k₀, hk₀⟩) :=
        key.mpr ⟨h⁻¹, by rw [← hh, inv_smul_smul]⟩
      have hv := congrArg Subtype.val this
      rw [e2, e2] at hv
      exact hv

  have hθbij := theta_bijective K K₁ K₂ K₁₂ hK₁ h₂ hinf hsurj
  have hAinv : ∀ (h : stabH H K₁ z) (a : K₁ ⧸ K₁₂.subgroupOf K₁), a ∈ A → h • a ∈ A := by
    intro h a ha
    show theta K K₁ K₂ K₁₂ hK₁ h₂ (h • a) ∈ Ω
    rw [theta_smul]
    exact mem_orbit_of_mem_orbit _ ha
  haveI : Fintype (orbitRel.Quotient (stabH H K₁ z) (K₁ ⧸ K₁₂.subgroupOf K₁)) := Fintype.ofFinite _
  let P : orbitRel.Quotient (stabH H K₁ z) (K₁ ⧸ K₁₂.subgroupOf K₁) → Prop := fun O => theta K K₁ K₂ K₁₂ hK₁ h₂ O.out ∈ Ω
  have hP : ∀ a, P (Quotient.mk (orbitRel (stabH H K₁ z) _) a) ↔ a ∈ A := by
    intro a
    show theta K K₁ K₂ K₁₂ hK₁ h₂ (Quotient.mk (orbitRel (stabH H K₁ z) _) a).out ∈ Ω ↔ theta K K₁ K₂ K₁₂ hK₁ h₂ a ∈ Ω
    obtain ⟨h, hh⟩ : ∃ h : stabH H K₁ z, h • a = (Quotient.mk (orbitRel (stabH H K₁ z) _) a).out :=
      orbitRel_apply.mp (Quotient.mk_out (s := orbitRel (stabH H K₁ z) (K₁ ⧸ K₁₂.subgroupOf K₁)) a)
    rw [← hh]
    constructor
    · intro h1
      have := hAinv h⁻¹ _ h1
      rwa [inv_smul_smul] at this
    · intro h1; exact hAinv h _ h1

  have hiff : ∀ O : orbitRel.Quotient (stabH H K₁ z) (K₁ ⧸ K₁₂.subgroupOf K₁),
      P O ↔ (DoubleCoset.mk H K₂ ((orbitEquiv H K₁ K₁₂ hK₁₂le z O : Fibre H K₁ K₁₂ z).1.out) = DoubleCoset.mk H K₂ y) := by
    intro O
    induction O using Quotient.inductionOn with
    | h a =>
    induction a using QuotientGroup.induction_on with
    | H k₁ =>
    rw [hP]
    show theta K K₁ K₂ K₁₂ hK₁ h₂ (QuotientGroup.mk k₁) ∈ Ω ↔ _
    rw [← hcond k₁]

    have hval : ((orbitEquiv H K₁ K₁₂ hK₁₂le z (Quotient.mk _ (QuotientGroup.mk k₁))) : Fibre H K₁ K₁₂ z).1 =
        DoubleCoset.mk H K₁₂ (z * k₁) := rfl
    rw [hval]
    obtain ⟨h, k', hh, hk', he⟩ := DoubleCoset.mk_out_eq_mul H K₁₂ (z * k₁)
    rw [he]
    have : DoubleCoset.mk H K₂ (h * (z * ↑k₁) * k') = DoubleCoset.mk H K₂ (z * k₁) := by
      rw [DoubleCoset.eq]; exact ⟨h⁻¹, H.inv_mem hh, k'⁻¹, K₂.inv_mem (h₂ hk'), by group⟩
    rw [this]
  let eF : {O : orbitRel.Quotient (stabH H K₁ z) (K₁ ⧸ K₁₂.subgroupOf K₁) // P O} ≃ Fibre₂ H K₁ K₂ K₁₂ z y :=
    (Equiv.subtypeEquiv (orbitEquiv H K₁ K₁₂ hK₁₂le z) hiff).trans
      { toFun := fun c => ⟨c.1.1, c.2, c.1.2⟩
        invFun := fun c => (⟨⟨c.1, c.2.2⟩, c.2.1⟩ :
          {b : Fibre H K₁ K₁₂ z // DoubleCoset.mk H K₂ b.1.out = DoubleCoset.mk H K₂ y})
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [← Fintype.sum_equiv eF (fun O => Nat.card (orbit (stabH H K₁ z) O.1.out))
    (fun c => (stabH H K₁₂ c.1.out).relIndex (stabH H K₁ c.1.out)) ?_]
  swap
  ·
    rintro ⟨O, hO⟩
    induction O using Quotient.inductionOn with
    | h a =>
    induction a using QuotientGroup.induction_on with
    | H k =>
    show Nat.card (orbit (stabH H K₁ z)
        (Quotient.mk (orbitRel (stabH H K₁ z) (K₁ ⧸ K₁₂.subgroupOf K₁)) (QuotientGroup.mk k : K₁ ⧸ K₁₂.subgroupOf K₁)).out) =
      (stabH H K₁₂ (DoubleCoset.mk H K₁₂ (z * (k : G))).out).relIndex (stabH H K₁ (DoubleCoset.mk H K₁₂ (z * (k : G))).out)
    obtain ⟨h₁, hh₁⟩ : ∃ h₁ : stabH H K₁ z, h₁ • (QuotientGroup.mk k : K₁ ⧸ K₁₂.subgroupOf K₁) =
        (Quotient.mk (orbitRel (stabH H K₁ z) (K₁ ⧸ K₁₂.subgroupOf K₁)) (QuotientGroup.mk k : K₁ ⧸ K₁₂.subgroupOf K₁)).out :=
      orbitRel_apply.mp (Quotient.mk_out (s := orbitRel (stabH H K₁ z) (K₁ ⧸ K₁₂.subgroupOf K₁))
        (QuotientGroup.mk k : K₁ ⧸ K₁₂.subgroupOf K₁))
    rw [← hh₁, orbit_smul, ← relIndex_eq_card_orbit H K₁ K₁₂ hK₁₂le z k]
    obtain ⟨h, k', hh, hk', he⟩ := DoubleCoset.mk_out_eq_mul H K₁₂ (z * k)
    rw [he, relIndex_stabH_mul H K₁ K₁₂ hK₁₂le (z * k) h k' hh hk', stabH_mul_right H K₁ z k k.2]

  rw [show (∑ O : {O // P O}, Nat.card (orbit (stabH H K₁ z) O.1.out)) =
      ∑ O ∈ Finset.univ.filter P, Nat.card (orbit (stabH H K₁ z) O.out) from
    (Finset.sum_subtype (Finset.univ.filter P) (fun O => by simp) (fun O => Nat.card (orbit (stabH H K₁ z) O.out))).symm]
  rw [sum_filter_card_orbit_eq_card A P hP]

  have eAΩ : A ≃ Ω := Equiv.subtypeEquiv (Equiv.ofBijective _ hθbij) (fun a => Iff.rfl)
  rw [Fintype.card_congr eAΩ, ← Nat.card_eq_fintype_card]

  show Nat.card (orbit (stabH H K z) (QuotientGroup.mk (⟨k₀, hk₀⟩ : K) : K ⧸ K₂.subgroupOf K)) = _
  rw [← relIndex_eq_card_orbit H K K₂ hK₂ z ⟨k₀, hk₀⟩, hy,
    show h₀ * z * k₀ = h₀ * (z * k₀) * 1 by group,
    relIndex_stabH_mul H K K₂ hK₂ (z * k₀) h₀ 1 hh₀ K₂.one_mem, stabH_mul_right H K z k₀ hk₀]

end Harmonic

end DoubleCosetFibre
p2m_reactivate "P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.DoubleCosetFibre"

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

noncomputable section

namespace CSTower

variable {a b : ℚ}

local notation "𝔸ℍ" => (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)
local notation "𝔾" => (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ
local notation "U" => Submodule.finiteIdeleStabilizer
local notation "conj" => Submodule.conjByFiniteIdele

theorem meetOrder_def (X : Submodule ℤ ℍ[ℚ, a, b]) (g : 𝔾) : meetOrder X g = X ⊓ conj X g := rfl

theorem mem_map_conj_iff (B : AddSubgroup 𝔸ℍ) (h : 𝔾) (x : 𝔸ℍ) :
    x ∈ B.map ((AddMonoidHom.mulRight ((h⁻¹ : 𝔾) : 𝔸ℍ)).comp (AddMonoidHom.mulLeft (h : 𝔸ℍ))) ↔
      ((h⁻¹ : 𝔾) : 𝔸ℍ) * x * (h : 𝔸ℍ) ∈ B := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro hx
    exact ⟨_, hx, by simp [mul_assoc]⟩

theorem units_smul_set_eq_image (g : 𝔾) (X : Set 𝔸ℍ) : g • X = (fun x => (g : 𝔸ℍ) * x) '' X := by
  ext x
  simp [Set.mem_smul_set, Units.smul_def, smul_eq_mul]

theorem mul_mem_box_iff_of_mem_stab {X : Submodule ℤ ℍ[ℚ, a, b]} {w : 𝔾} (hw : w ∈ U X) (y : 𝔸ℍ) :
    (w : 𝔸ℍ) * y ∈ Submodule.finiteAdeleBox X ↔ y ∈ Submodule.finiteAdeleBox X := by
  rw [Submodule.mem_finiteIdeleStabilizer_iff] at hw
  set B : Set 𝔸ℍ := ((Submodule.finiteAdeleBox X : AddSubgroup 𝔸ℍ) : Set 𝔸ℍ) with hB
  constructor
  · intro h
    have h' : (w : 𝔸ℍ) * y ∈ w • B := by rw [hw]; exact h
    rw [units_smul_set_eq_image] at h'
    obtain ⟨z, hz, hzy⟩ := h'
    have : z = y := by
      have := congrArg (fun t => ((w⁻¹ : 𝔾) : 𝔸ℍ) * t) hzy
      simpa using this
    rw [← this]; exact hz
  · intro h
    have : (w : 𝔸ℍ) * y ∈ w • B := by rw [units_smul_set_eq_image]; exact ⟨y, h, rfl⟩
    rw [hw] at this
    exact this

theorem conj_eq_conj_of_inv_mul_mem {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) {n n' : 𝔾}
    (hnn' : n⁻¹ * n' ∈ U R) : conj R n' = conj R n := by
  have h := Submodule.conjByFiniteIdele_mul_eq_of_mem_finiteIdeleStabilizer R hR.one_mem
    (fun x y hx hy => hR.mul_mem hx hy) n (n⁻¹ * n') hnn'
  rwa [mul_inv_cancel_left] at h

theorem meetOrder_eq_meetOrder_of_inv_mul_mem {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) {n n' : 𝔾}
    (hnn' : n⁻¹ * n' ∈ U R) : meetOrder R n' = meetOrder R n := by
  rw [meetOrder_def, meetOrder_def, conj_eq_conj_of_inv_mul_mem hR hnn']

theorem conj_conj {X : Submodule ℤ ℍ[ℚ, a, b]} (hX : IsOrder X) (g g' : 𝔾) :
    conj (conj X g) g' = conj X (g' * g) := by
  ext z
  rw [Submodule.mem_conjByFiniteIdele_iff, Submodule.mem_conjByFiniteIdele_iff,
    Submodule.finiteAdeleBox_conjByFiniteIdele X hX.fg hX.spanTop g, AddSubgroup.map_map]
  have hc : ((AddMonoidHom.mulRight ((g'⁻¹ : 𝔾) : 𝔸ℍ)).comp (AddMonoidHom.mulLeft (g' : 𝔸ℍ))).comp
      ((AddMonoidHom.mulRight ((g⁻¹ : 𝔾) : 𝔸ℍ)).comp (AddMonoidHom.mulLeft (g : 𝔸ℍ))) =
      (AddMonoidHom.mulRight (((g' * g)⁻¹ : 𝔾) : 𝔸ℍ)).comp (AddMonoidHom.mulLeft ((g' * g : 𝔾) : 𝔸ℍ)) := by
    ext x
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulLeft,
      AddMonoidHom.coe_mulRight, mul_inv_rev, Units.val_mul, mul_assoc]
  rw [hc]

theorem conj_meetOrder {X : Submodule ℤ ℍ[ℚ, a, b]} (hX : IsOrder X) (g h : 𝔾) :
    conj (meetOrder X g) h = conj X h ⊓ conj X (h * g) := by
  have hbox := (QuaternionAlgebra.IsOrder.finiteAdeleBox_inf_conjByFiniteIdele_eq_and_finiteIdeleStabilizer_le X hX g).1
  ext z
  rw [Submodule.mem_inf, Submodule.mem_conjByFiniteIdele_iff, Submodule.mem_conjByFiniteIdele_iff,
    Submodule.mem_conjByFiniteIdele_iff, meetOrder_def, hbox, mem_map_conj_iff, mem_map_conj_iff, mem_map_conj_iff,
    AddSubgroup.mem_inf, mem_map_conj_iff]
  simp only [mul_inv_rev, Units.val_mul, mul_assoc]

theorem meetOrder_meetOrder_comm {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) {n s n' : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}
    (hnn' : n⁻¹ * n' ∈ U R) (hsn' : s * n' = n' * s) :
    meetOrder (meetOrder R s) n' = meetOrder (meetOrder R n) s := by
  have h1 : conj R n' = conj R n := conj_eq_conj_of_inv_mul_mem hR hnn'
  have h2 : conj R (n' * s) = conj R (s * n) := by
    rw [← hsn', show s * n' = s * n * (n⁻¹ * n') by rw [mul_assoc, mul_inv_cancel_left]]
    exact Submodule.conjByFiniteIdele_mul_eq_of_mem_finiteIdeleStabilizer R hR.one_mem
      (fun x y hx hy => hR.mul_mem hx hy) (s * n) (n⁻¹ * n') hnn'
  rw [meetOrder_def (meetOrder R s), meetOrder_def (meetOrder R n), conj_meetOrder hR s n', conj_meetOrder hR n s,
    meetOrder_def, meetOrder_def, h1, h2]
  ac_rfl

theorem isOrder_conj {X : Submodule ℤ ℍ[ℚ, a, b]} (hX : IsOrder X) (g : 𝔾) : IsOrder (conj X g) :=
  QuaternionAlgebra.IsOrder.conjByFiniteIdele X hX g

private theorem _root_.CSTower.isOrder_meetOrder {X : Submodule ℤ ℍ[ℚ, a, b]} (hX : IsOrder X) (g : 𝔾) : IsOrder (meetOrder X g) := by
  rw [meetOrder_def]; exact hX.inf (isOrder_conj hX g)

p2m_export "CSTower" "isOrder_meetOrder"

theorem mem_stab_meetOrder_iff {X : Submodule ℤ ℍ[ℚ, a, b]} (hX : IsOrder X) (g u : 𝔾) :
    u ∈ U (meetOrder X g) ↔ u ∈ U X ∧ g⁻¹ * u * g ∈ U X := by
  have h8 := QuaternionAlgebra.IsOrder.finiteAdeleBox_inf_conjByFiniteIdele_eq_and_finiteIdeleStabilizer_le X hX g
  constructor
  · intro hu
    rw [meetOrder_def] at hu
    exact ⟨h8.2.2.1 hu, h8.2.2.2 u hu⟩
  · rintro ⟨hu, hgu⟩
    rw [meetOrder_def, Submodule.mem_finiteIdeleStabilizer_iff, h8.1, AddSubgroup.coe_inf, Set.smul_set_inter]
    have hu' := (Submodule.mem_finiteIdeleStabilizer_iff X u).mp hu
    rw [hu']
    congr 1
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem, Units.smul_def, smul_eq_mul, SetLike.mem_coe, SetLike.mem_coe,
      mem_map_conj_iff, mem_map_conj_iff]
    have key : ((g⁻¹ : 𝔾) : 𝔸ℍ) * (((u⁻¹ : 𝔾) : 𝔸ℍ) * x) * (g : 𝔸ℍ) =
        (((g⁻¹ * u * g)⁻¹ : 𝔾) : 𝔸ℍ) * (((g⁻¹ : 𝔾) : 𝔸ℍ) * x * (g : 𝔸ℍ)) := by
      simp only [mul_inv_rev, inv_inv, Units.val_mul, mul_assoc, Units.mul_inv_cancel_left]
    rw [key, mul_mem_box_iff_of_mem_stab (inv_mem hgu)]

theorem stab_meetOrder_le {X : Submodule ℤ ℍ[ℚ, a, b]} (hX : IsOrder X) (g : 𝔾) : U (meetOrder X g) ≤ U X :=
  fun _ hu => ((mem_stab_meetOrder_iff hX g _).mp hu).1

section Storey

variable {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) {n s n' : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}
include hR

theorem stab_R'_le_R : U (meetOrder R s) ≤ U R := stab_meetOrder_le hR s

theorem stab_S'_le_R' : U (meetOrder (meetOrder R s) n') ≤ U (meetOrder R s) :=
  stab_meetOrder_le (isOrder_meetOrder hR s) n'

theorem inv_mul_mul_mem_stab_R_of_mem_stab_S {u : 𝔾} (hu : u ∈ U (meetOrder R n)) : n⁻¹ * u * n ∈ U R :=
  ((mem_stab_meetOrder_iff hR n u).mp hu).2

theorem inv_mul_mul_mem_stab_R'_of_mem_stab_S' {u : 𝔾} (hu : u ∈ U (meetOrder (meetOrder R s) n')) :
    n'⁻¹ * u * n' ∈ U (meetOrder R s) :=
  ((mem_stab_meetOrder_iff (isOrder_meetOrder hR s) n' u).mp hu).2

theorem inv_mul_mul_mem_stab_R_of_mem_stab_R' {u : 𝔾} (hu : u ∈ U (meetOrder R s)) : s⁻¹ * u * s ∈ U R :=
  ((mem_stab_meetOrder_iff hR s u).mp hu).2

theorem stab_S'_le_S (hnn' : n⁻¹ * n' ∈ U R) (hsn' : s * n' = n' * s) :
    U (meetOrder (meetOrder R s) n') ≤ U (meetOrder R n) := by
  rw [meetOrder_meetOrder_comm hR hnn' hsn']
  exact stab_meetOrder_le (isOrder_meetOrder hR n) s

theorem inv_mul_mul_mem_stab_S_of_mem_stab_S' (hnn' : n⁻¹ * n' ∈ U R) (hsn' : s * n' = n' * s) {u : 𝔾}
    (hu : u ∈ U (meetOrder (meetOrder R s) n')) : s⁻¹ * u * s ∈ U (meetOrder R n) := by
  rw [meetOrder_meetOrder_comm hR hnn' hsn'] at hu
  exact ((mem_stab_meetOrder_iff (isOrder_meetOrder hR n) s u).mp hu).2

end Storey
p2m_reactivate "P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.DoubleCosetFibre"

section ClassSetMaps

variable {V V' : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}

theorem exists_out_eq (V : Subgroup 𝔾) (x : 𝔾) :
    ∃ (δ : (ℍ[ℚ, a, b])ˣ) (u : 𝔾), u ∈ V ∧
      (ClassSet.mk V x).out = Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] δ * x * u := by
  obtain ⟨h, k, hh, hk, hout⟩ := DoubleCoset.mk_out_eq_mul (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]).range V x
  obtain ⟨δ, rfl⟩ := MonoidHom.mem_range.mp hh
  exact ⟨δ, k, hk, hout⟩

theorem classSetForget_mk (h : V ≤ V') (x : 𝔾) : classSetForget V V' (ClassSet.mk V x) = ClassSet.mk V' x := by
  obtain ⟨δ, u, hu, hout⟩ := exists_out_eq V x
  show ClassSet.mk V' (ClassSet.mk V x).out = _
  rw [hout, ClassSet.mk_mul_of_mem _ _ (h hu), ClassSet.mk_diagonal_mul]

theorem classSetForget_eq_map (h : V ≤ V') : classSetForget V V' = ClassSet.map h := by
  funext x
  obtain ⟨y, rfl⟩ := ClassSet.mk_surjective x
  rw [classSetForget_mk h, ClassSet.map_mk]

theorem mk_out_mul (g : 𝔾) (hg : ∀ u ∈ V, g⁻¹ * u * g ∈ V') (x : 𝔾) :
    ClassSet.mk V' ((ClassSet.mk V x).out * g) = ClassSet.mk V' (x * g) := by
  obtain ⟨δ, u, hu, hout⟩ := exists_out_eq V x
  have hre : Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] δ * x * u * g =
      Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] δ * (x * g) * (g⁻¹ * u * g) := by
    simp only [mul_assoc, mul_inv_cancel_left]
  rw [hout, hre, ClassSet.mk_mul_of_mem _ _ (hg u hu), ClassSet.mk_diagonal_mul]

theorem mk_mul_eq_mk_mul (g : 𝔾) (hg : ∀ u ∈ V, g⁻¹ * u * g ∈ V') {x y : 𝔾} (h : ClassSet.mk V x = ClassSet.mk V y) :
    ClassSet.mk V' (x * g) = ClassSet.mk V' (y * g) := by
  rw [← mk_out_mul g hg x, ← mk_out_mul g hg y, h]

end ClassSetMaps
p2m_reactivate "P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.DoubleCosetFibre"

section Squares

variable {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) {n s n' : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}
  (hnn' : n⁻¹ * n' ∈ U R) (hsn' : s * n' = n' * s)
include hR hnn' hsn'

theorem a_forget (e : ClassSet (U (meetOrder (meetOrder R s) n'))) :
    (classSetDegeneracyData R n).a (classSetForget _ (U (meetOrder R n)) e) =
      classSetForget _ (U R) ((classSetDegeneracyData (meetOrder R s) n').a e) := by
  obtain ⟨x, rfl⟩ := ClassSet.mk_surjective e
  show classSetForget _ (U R) (classSetForget _ (U (meetOrder R n)) (ClassSet.mk _ x)) =
    classSetForget _ (U R) (classSetForget _ (U (meetOrder R s)) (ClassSet.mk _ x))
  rw [classSetForget_mk (stab_S'_le_S hR hnn' hsn'), classSetForget_mk (stab_meetOrder_le hR n),
    classSetForget_mk (stab_S'_le_R' hR), classSetForget_mk (stab_R'_le_R hR)]

theorem b_forget (e : ClassSet (U (meetOrder (meetOrder R s) n'))) :
    (classSetDegeneracyData R n).b (classSetForget _ (U (meetOrder R n)) e) =
      classSetForget _ (U R) ((classSetDegeneracyData (meetOrder R s) n').b e) := by
  obtain ⟨x, rfl⟩ := ClassSet.mk_surjective e
  show ClassSet.mk (U R) ((classSetForget _ (U (meetOrder R n)) (ClassSet.mk _ x)).out * n) =
    classSetForget _ (U R) (ClassSet.mk (U (meetOrder R s)) ((ClassSet.mk _ x).out * n'))
  rw [classSetForget_mk (stab_S'_le_S hR hnn' hsn'),
    mk_out_mul n (fun u hu => inv_mul_mul_mem_stab_R_of_mem_stab_S hR hu),
    classSetForget_mk (stab_R'_le_R hR),
    mk_out_mul n' (fun u hu => stab_R'_le_R hR (inv_mul_mul_mem_stab_R'_of_mem_stab_S' hR hu))]
  have hre : x * n' = x * n * (n⁻¹ * n') := by rw [mul_assoc, mul_inv_cancel_left]
  rw [hre, ClassSet.mk_mul_of_mem _ _ hnn']

theorem shift_mk_edge (x : 𝔾) :
    ClassSet.mk (U (meetOrder R n)) ((ClassSet.mk (U (meetOrder (meetOrder R s) n')) x).out * s) =
      ClassSet.mk (U (meetOrder R n)) (x * s) :=
  mk_out_mul s (fun u hu => inv_mul_mul_mem_stab_S_of_mem_stab_S' hR hnn' hsn' hu) x

theorem shift_mk_vertex (x : 𝔾) :
    ClassSet.mk (U R) ((ClassSet.mk (U (meetOrder R s)) x).out * s) = ClassSet.mk (U R) (x * s) :=
  mk_out_mul s (fun u hu => inv_mul_mul_mem_stab_R_of_mem_stab_R' hR hu) x

theorem a_shift (e : ClassSet (U (meetOrder (meetOrder R s) n'))) :
    (classSetDegeneracyData R n).a (ClassSet.mk (U (meetOrder R n)) (e.out * s)) =
      ClassSet.mk (U R) (((classSetDegeneracyData (meetOrder R s) n').a e).out * s) := by
  show classSetForget _ (U R) (ClassSet.mk (U (meetOrder R n)) (e.out * s)) =
    ClassSet.mk (U R) ((ClassSet.mk (U (meetOrder R s)) e.out).out * s)
  rw [classSetForget_mk (stab_meetOrder_le hR n), shift_mk_vertex hR hnn' hsn']

theorem b_shift (e : ClassSet (U (meetOrder (meetOrder R s) n'))) :
    (classSetDegeneracyData R n).b (ClassSet.mk (U (meetOrder R n)) (e.out * s)) =
      ClassSet.mk (U R) (((classSetDegeneracyData (meetOrder R s) n').b e).out * s) := by
  show ClassSet.mk (U R) ((ClassSet.mk (U (meetOrder R n)) (e.out * s)).out * n) =
    ClassSet.mk (U R) ((ClassSet.mk (U (meetOrder R s)) (e.out * n')).out * s)
  rw [mk_out_mul n (fun u hu => inv_mul_mul_mem_stab_R_of_mem_stab_S hR hu), shift_mk_vertex hR hnn' hsn',
    mul_assoc e.out n' s, ← hsn', ← mul_assoc]
  have hre : e.out * s * n' = e.out * s * n * (n⁻¹ * n') := by rw [mul_assoc (e.out * s), mul_inv_cancel_left]
  rw [hre, ClassSet.mk_mul_of_mem _ _ hnn']

end Squares
p2m_reactivate "P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.DoubleCosetFibre"

end CSTower
p2m_reactivate "P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.DoubleCosetFibre"

namespace CSTower

variable {a b : ℚ}

local notation "𝔸ℍ" => (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)
local notation "𝔾" => (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ
local notation "U" => Submodule.finiteIdeleStabilizer
local notation "conj" => Submodule.conjByFiniteIdele

def unitGroup (X : Submodule ℤ ℍ[ℚ, a, b]) : Subgroup (ℍ[ℚ, a, b])ˣ :=
  MulAction.stabilizer (ℍ[ℚ, a, b])ˣ X

theorem mem_unitGroup_iff {X : Submodule ℤ ℍ[ℚ, a, b]} (hX : IsOrder X) (δ : (ℍ[ℚ, a, b])ˣ) :
    δ ∈ unitGroup X ↔ (δ : ℍ[ℚ, a, b]) ∈ X ∧ ((δ⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ∈ X := by
  rw [unitGroup, MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have h1 : δ • (1 : ℍ[ℚ, a, b]) ∈ δ • X := Submodule.smul_mem_pointwise_smul _ _ _ hX.one_mem
      rw [h] at h1
      simpa [Units.smul_def] using h1
    · have h1 : (1 : ℍ[ℚ, a, b]) ∈ δ • X := by rw [h]; exact hX.one_mem
      obtain ⟨y, hy, hy1⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h1
      rw [Units.smul_def, smul_eq_mul] at hy1
      rwa [Units.inv_eq_of_mul_eq_one_right hy1]
  · rintro ⟨hδ, hδi⟩
    apply le_antisymm
    · intro y hy
      obtain ⟨z, hz, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hy
      rw [Units.smul_def, smul_eq_mul]
      exact hX.mul_mem hδ hz
    · intro y hy
      refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨((δ⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * y,
        hX.mul_mem hδi hy, ?_⟩
      rw [Units.smul_def, smul_eq_mul, ← mul_assoc, Units.mul_inv, one_mul]

theorem mem_unitGroup_iff_isUnitOf {X : Submodule ℤ ℍ[ℚ, a, b]} (hX : IsOrder X) (δ : (ℍ[ℚ, a, b])ˣ) :
    δ ∈ unitGroup X ↔ IsUnitOf X (δ : ℍ[ℚ, a, b]) := by
  rw [mem_unitGroup_iff hX]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, _, h2, δ.mul_inv, δ.inv_mul⟩
  · rintro ⟨h1, v, hv, hv1, -⟩
    exact ⟨h1, by rwa [Units.inv_eq_of_mul_eq_one_right hv1]⟩

def unitOfIsUnitOf {X : Submodule ℤ ℍ[ℚ, a, b]} (u : {u : ℍ[ℚ, a, b] // IsUnitOf X u}) : (ℍ[ℚ, a, b])ˣ :=
  ⟨u.1, Classical.choose u.2.2, (Classical.choose_spec u.2.2).2.1, (Classical.choose_spec u.2.2).2.2⟩

@[scoped simp] theorem coe_unitOfIsUnitOf {X : Submodule ℤ ℍ[ℚ, a, b]} (u : {u : ℍ[ℚ, a, b] // IsUnitOf X u}) :
    (unitOfIsUnitOf u : ℍ[ℚ, a, b]) = u.1 := rfl

def isUnitOfEquiv {X : Submodule ℤ ℍ[ℚ, a, b]} (hX : IsOrder X) :
    {u : ℍ[ℚ, a, b] // IsUnitOf X u} ≃ unitGroup X where
  toFun u := ⟨unitOfIsUnitOf u, (mem_unitGroup_iff_isUnitOf hX _).mpr u.2⟩
  invFun δ := ⟨δ.1, (mem_unitGroup_iff_isUnitOf hX δ.1).mp δ.2⟩
  left_inv u := Subtype.ext rfl
  right_inv δ := Subtype.ext (Units.ext rfl)

theorem card_unitGroup_eq {X : Submodule ℤ ℍ[ℚ, a, b]} (hX : IsOrder X) :
    Nat.card (unitGroup X) = Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf X u} :=
  Nat.card_congr (isUnitOfEquiv hX).symm

theorem neg_one_mem_unitGroup {X : Submodule ℤ ℍ[ℚ, a, b]} (hX : IsOrder X) : -1 ∈ unitGroup X := by
  rw [mem_unitGroup_iff hX]
  refine ⟨?_, ?_⟩
  · simpa using X.neg_mem hX.one_mem
  · simpa using X.neg_mem hX.one_mem

theorem unitGroup_mono {X Y : Submodule ℤ ℍ[ℚ, a, b]} (hX : IsOrder X) (hY : IsOrder Y) (h : X ≤ Y) :
    unitGroup X ≤ unitGroup Y := by
  intro δ hδ
  rw [mem_unitGroup_iff hX] at hδ
  rw [mem_unitGroup_iff hY]
  exact ⟨h hδ.1, h hδ.2⟩

theorem finite_unitGroup {q' : ℕ} (hdef : IsDefiniteRamifiedExactlyAt a b q') {X : Submodule ℤ ℍ[ℚ, a, b]}
    (hX : IsOrder X) : Finite (unitGroup X) :=
  have := (QuaternionAlgebra.IsOrder.finite_isUnitOf_and_nrd_eq_one hdef.neg_left hdef.neg_right hX).1
  Finite.of_equiv _ (isUnitOfEquiv hX)

theorem mem_conj_diagonal_mul_iff (X : Submodule ℤ ℍ[ℚ, a, b]) (δ : (ℍ[ℚ, a, b])ˣ) (x : 𝔾) (z : ℍ[ℚ, a, b]) :
    z ∈ conj X (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] δ * x) ↔
      ((δ⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * z * δ ∈ conj X x := by
  rw [Submodule.mem_conjByFiniteIdele_iff, Submodule.mem_conjByFiniteIdele_iff, mem_map_conj_iff, mem_map_conj_iff]
  have key : (((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] δ * x)⁻¹ : 𝔾) : 𝔸ℍ) *
        z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) * ((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] δ * x : 𝔾) : 𝔸ℍ) =
      ((x⁻¹ : 𝔾) : 𝔸ℍ) * (((δ⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * z * δ) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) *
        (x : 𝔸ℍ) := by
    rw [mul_inv_rev, Units.val_mul, Units.val_mul, ← map_inv, Submodule.val_finiteIdeleDiagonal_apply,
      Submodule.val_finiteIdeleDiagonal_apply]
    simp only [mul_assoc]
    congr 1
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, one_mul, mul_assoc]
  rw [key]

theorem unitGroup_conj_diagonal_mul {X : Submodule ℤ ℍ[ℚ, a, b]} (hX : IsOrder X) (δ : (ℍ[ℚ, a, b])ˣ) (x : 𝔾) :
    unitGroup (conj X (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] δ * x)) =
      (unitGroup (conj X x)).map (MulAut.conj δ).toMonoidHom := by
  ext γ
  rw [Subgroup.mem_map_equiv, mem_unitGroup_iff (isOrder_conj hX _), mem_unitGroup_iff (isOrder_conj hX _),
    MulAut.conj_symm_apply, mem_conj_diagonal_mul_iff, mem_conj_diagonal_mul_iff]
  simp only [mul_inv_rev, inv_inv, Units.val_mul, mul_assoc]

theorem unitGroup_conj_mul_of_mem_stab {X : Submodule ℤ ℍ[ℚ, a, b]} (hX : IsOrder X) (x : 𝔾) {u : 𝔾} (hu : u ∈ U X) :
    unitGroup (conj X (x * u)) = unitGroup (conj X x) := by
  rw [Submodule.conjByFiniteIdele_mul_eq_of_mem_finiteIdeleStabilizer X hX.one_mem (fun x y hx hy => hX.mul_mem hx hy) x u hu]

theorem card_unitGroup_conj_out {X : Submodule ℤ ℍ[ℚ, a, b]} (hX : IsOrder X)
    {V : Subgroup 𝔾} (hV : V ≤ U X) (x : 𝔾) :
    Nat.card (unitGroup (conj X (ClassSet.mk V x).out)) = Nat.card (unitGroup (conj X x)) := by
  obtain ⟨δ, u, hu, hout⟩ := exists_out_eq V x
  rw [hout, unitGroup_conj_mul_of_mem_stab hX _ (hV hu), unitGroup_conj_diagonal_mul hX]
  exact Nat.card_congr ((unitGroup (conj X x)).equivMapOfInjective _ (MulAut.conj δ).injective).toEquiv.symm

theorem relIndex_unitGroup_conj_out {X X' : Submodule ℤ ℍ[ℚ, a, b]} (hX : IsOrder X) (hX' : IsOrder X')
    {V : Subgroup 𝔾} (x g : 𝔾) (hV : ∀ u ∈ V, g⁻¹ * u * g ∈ U X) (hV' : V ≤ U X') :
    (unitGroup (conj X' (ClassSet.mk V x).out)).relIndex (unitGroup (conj X ((ClassSet.mk V x).out * g))) =
      (unitGroup (conj X' x)).relIndex (unitGroup (conj X (x * g))) := by
  obtain ⟨δ, u, hu, hout⟩ := exists_out_eq V x
  have hre : Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] δ * x * u * g =
      Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] δ * (x * g) * (g⁻¹ * u * g) := by
    simp only [mul_assoc, mul_inv_cancel_left]
  rw [hout, hre, unitGroup_conj_mul_of_mem_stab hX _ (hV u hu), unitGroup_conj_mul_of_mem_stab hX' _ (hV' hu),
    unitGroup_conj_diagonal_mul hX, unitGroup_conj_diagonal_mul hX',
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj δ).injective]

section StoreyUnits

variable {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) {n s n' : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}
  (hnn' : n⁻¹ * n' ∈ U R) (hsn' : s * n' = n' * s)
include hR hnn' hsn'

theorem unitGroup_conj_S'_le (x : 𝔾) :
    unitGroup (conj (meetOrder (meetOrder R s) n') x) ≤ unitGroup (conj (meetOrder R n) x) := by
  refine unitGroup_mono (isOrder_conj (isOrder_meetOrder (isOrder_meetOrder hR s) n') x)
    (isOrder_conj (isOrder_meetOrder hR n) x) ?_
  rw [meetOrder_meetOrder_comm hR hnn' hsn', conj_meetOrder (isOrder_meetOrder hR n)]
  exact inf_le_left

theorem unitGroup_conj_S'_le_shift (x : 𝔾) :
    unitGroup (conj (meetOrder (meetOrder R s) n') x) ≤ unitGroup (conj (meetOrder R n) (x * s)) := by
  refine unitGroup_mono (isOrder_conj (isOrder_meetOrder (isOrder_meetOrder hR s) n') x)
    (isOrder_conj (isOrder_meetOrder hR n) _) ?_
  rw [meetOrder_meetOrder_comm hR hnn' hsn', conj_meetOrder (isOrder_meetOrder hR n)]
  exact inf_le_right

omit hnn' hsn' in
theorem unitGroup_conj_R'_le (x : 𝔾) : unitGroup (conj (meetOrder R s) x) ≤ unitGroup (conj R x) := by
  refine unitGroup_mono (isOrder_conj (isOrder_meetOrder hR s) x) (isOrder_conj hR x) ?_
  rw [conj_meetOrder hR]
  exact inf_le_left

omit hnn' hsn' in
theorem unitGroup_conj_R'_le_shift (x : 𝔾) : unitGroup (conj (meetOrder R s) x) ≤ unitGroup (conj R (x * s)) := by
  refine unitGroup_mono (isOrder_conj (isOrder_meetOrder hR s) x) (isOrder_conj hR _) ?_
  rw [conj_meetOrder hR]
  exact inf_le_right

end StoreyUnits
p2m_reactivate "P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.DoubleCosetFibre"

theorem two_dvd_card_unitGroup {X : Submodule ℤ ℍ[ℚ, a, b]} (hX : IsOrder X) [Finite (unitGroup X)] :
    2 ∣ Nat.card (unitGroup X) ∧ 0 < Nat.card (unitGroup X) := by
  have h2 : Nat.card (Subgroup.zpowers (-1 : (ℍ[ℚ, a, b])ˣ)) = 2 := by
    rw [Nat.card_zpowers]
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime (by simp) ?_
    intro h
    have h' : ((-1 : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = ((1 : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) := by rw [h]
    simp only [Units.val_neg, Units.val_one] at h'
    have h'' := congrArg QuaternionAlgebra.re h'
    simp at h''
    norm_num at h''
  have hle : Subgroup.zpowers (-1 : (ℍ[ℚ, a, b])ˣ) ≤ unitGroup X :=
    (Subgroup.zpowers_le).mpr (neg_one_mem_unitGroup hX)
  refine ⟨?_, Nat.card_pos⟩
  rw [← h2]
  exact Subgroup.card_dvd_of_le hle

theorem coe_unitWeight_eq {X : Submodule ℤ ℍ[ℚ, a, b]} (hX : IsOrder X) [Finite (unitGroup X)] :
    (unitWeight X : ℕ) = Nat.card (unitGroup X) / 2 ∧ 2 ∣ Nat.card (unitGroup X) ∧ 0 < Nat.card (unitGroup X) / 2 := by
  obtain ⟨h2, hpos⟩ := two_dvd_card_unitGroup hX
  have hpos' : 0 < Nat.card (unitGroup X) / 2 :=
    Nat.div_pos (Nat.le_of_dvd hpos h2) two_pos
  refine ⟨?_, h2, hpos'⟩
  rw [unitWeight, ← card_unitGroup_eq hX, Nat.toPNat'_coe, if_pos hpos']

theorem unitWeight_eq_relIndex_mul {X X' : Submodule ℤ ℍ[ℚ, a, b]} (hX : IsOrder X) (hX' : IsOrder X')
    (hle : unitGroup X' ≤ unitGroup X) [Finite (unitGroup X)] :
    (unitWeight X : ℕ) = (unitGroup X').relIndex (unitGroup X) * (unitWeight X' : ℕ) ∧
      0 < (unitGroup X').relIndex (unitGroup X) := by
  haveI : Finite (unitGroup X') := Finite.of_injective _ (Subgroup.inclusion_injective hle)
  have hcard : (unitGroup X').relIndex (unitGroup X) * Nat.card (unitGroup X') = Nat.card (unitGroup X) := by
    have h := Subgroup.card_mul_index ((unitGroup X').subgroupOf (unitGroup X))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at h
    rw [Subgroup.relIndex, mul_comm]
    exact h
  obtain ⟨hw, h2, hpos⟩ := coe_unitWeight_eq hX
  obtain ⟨hw', h2', hpos'⟩ := coe_unitWeight_eq hX'
  refine ⟨?_, ?_⟩
  · rw [hw, hw', ← hcard, Nat.mul_div_assoc _ h2']
  · rcases Nat.eq_zero_or_pos ((unitGroup X').relIndex (unitGroup X)) with h0 | h0
    · rw [h0, zero_mul] at hcard
      exact absurd hcard.symm (two_dvd_card_unitGroup hX).2.ne'
    · exact h0

theorem unitWeight_congr {X Y : Submodule ℤ ℍ[ℚ, a, b]}
    (h : Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf X u} = Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf Y u}) :
    unitWeight X = unitWeight Y := by
  rw [unitWeight, unitWeight, h]

section StoreyWidths

variable {q' : ℕ} (hdef : IsDefiniteRamifiedExactlyAt a b q') {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R)
  {n s n' : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ} (hnn' : n⁻¹ * n' ∈ U R) (hsn' : s * n' = n' * s)
include hdef hR hnn' hsn'

theorem w_forget (e : ClassSet (U (meetOrder (meetOrder R s) n'))) :
    ((classSetDegeneracyData R n).w (classSetForget _ (U (meetOrder R n)) e) : ℕ) =
      (unitGroup (conj (meetOrder (meetOrder R s) n') e.out)).relIndex (unitGroup (conj (meetOrder R n) e.out)) *
        ((classSetDegeneracyData (meetOrder R s) n').w e : ℕ) ∧
    0 < (unitGroup (conj (meetOrder (meetOrder R s) n') e.out)).relIndex (unitGroup (conj (meetOrder R n) e.out)) := by
  have hS : IsOrder (meetOrder R n) := isOrder_meetOrder hR n
  have hS' : IsOrder (meetOrder (meetOrder R s) n') := isOrder_meetOrder (isOrder_meetOrder hR s) n'
  haveI : Finite (unitGroup (conj (meetOrder R n) e.out)) := finite_unitGroup hdef (isOrder_conj hS _)
  have hw : (classSetDegeneracyData R n).w (classSetForget _ (U (meetOrder R n)) e) = unitWeight (conj (meetOrder R n) e.out) := by
    show unitWeight (conj (meetOrder R n) (ClassSet.mk (U (meetOrder R n)) e.out).out) = _
    apply unitWeight_congr
    rw [← card_unitGroup_eq (isOrder_conj hS _), ← card_unitGroup_eq (isOrder_conj hS _),
      card_unitGroup_conj_out hS le_rfl]
  have hw' : (classSetDegeneracyData (meetOrder R s) n').w e = unitWeight (conj (meetOrder (meetOrder R s) n') e.out) := rfl
  rw [hw, hw']
  exact unitWeight_eq_relIndex_mul (isOrder_conj hS _) (isOrder_conj hS' _) (unitGroup_conj_S'_le hR hnn' hsn' e.out)

theorem w_shift (e : ClassSet (U (meetOrder (meetOrder R s) n'))) :
    ((classSetDegeneracyData R n).w (ClassSet.mk (U (meetOrder R n)) (e.out * s)) : ℕ) =
      (unitGroup (conj (meetOrder (meetOrder R s) n') e.out)).relIndex (unitGroup (conj (meetOrder R n) (e.out * s))) *
        ((classSetDegeneracyData (meetOrder R s) n').w e : ℕ) ∧
    0 < (unitGroup (conj (meetOrder (meetOrder R s) n') e.out)).relIndex (unitGroup (conj (meetOrder R n) (e.out * s))) := by
  have hS : IsOrder (meetOrder R n) := isOrder_meetOrder hR n
  have hS' : IsOrder (meetOrder (meetOrder R s) n') := isOrder_meetOrder (isOrder_meetOrder hR s) n'
  haveI : Finite (unitGroup (conj (meetOrder R n) (e.out * s))) := finite_unitGroup hdef (isOrder_conj hS _)
  have hw : (classSetDegeneracyData R n).w (ClassSet.mk (U (meetOrder R n)) (e.out * s)) =
      unitWeight (conj (meetOrder R n) (e.out * s)) := by
    show unitWeight (conj (meetOrder R n) (ClassSet.mk (U (meetOrder R n)) (e.out * s)).out) = _
    apply unitWeight_congr
    rw [← card_unitGroup_eq (isOrder_conj hS _), ← card_unitGroup_eq (isOrder_conj hS _),
      card_unitGroup_conj_out hS le_rfl]
  have hw' : (classSetDegeneracyData (meetOrder R s) n').w e = unitWeight (conj (meetOrder (meetOrder R s) n') e.out) := rfl
  rw [hw, hw']
  exact unitWeight_eq_relIndex_mul (isOrder_conj hS _) (isOrder_conj hS' _) (unitGroup_conj_S'_le_shift hR hnn' hsn' e.out)

omit hR hnn' hsn' in
theorem relIndex_mul_card_of_le {X X' : Submodule ℤ ℍ[ℚ, a, b]} (hX : IsOrder X) (hX' : IsOrder X')
    (hle : unitGroup X' ≤ unitGroup X) :
    (unitGroup X').relIndex (unitGroup X) * Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf X' u} =
      Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf X u} := by
  haveI : Finite (unitGroup X) := finite_unitGroup hdef hX
  have h := Subgroup.card_mul_index ((unitGroup X').subgroupOf (unitGroup X))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at h
  rw [← card_unitGroup_eq hX, ← card_unitGroup_eq hX', Subgroup.relIndex, mul_comm]
  exact h

theorem relIndex_mul_card_edge_forget (e : ClassSet (U (meetOrder (meetOrder R s) n'))) :
    (unitGroup (conj (meetOrder (meetOrder R s) n') e.out)).relIndex (unitGroup (conj (meetOrder R n) e.out)) *
        Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf (conj (meetOrder (meetOrder R s) n') e.out) u} =
      Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf (conj (meetOrder R n) e.out) u} :=
  relIndex_mul_card_of_le hdef (isOrder_conj (isOrder_meetOrder hR n) _)
    (isOrder_conj (isOrder_meetOrder (isOrder_meetOrder hR s) n') _) (unitGroup_conj_S'_le hR hnn' hsn' e.out)

theorem relIndex_mul_card_edge_shift (e : ClassSet (U (meetOrder (meetOrder R s) n'))) :
    (unitGroup (conj (meetOrder (meetOrder R s) n') e.out)).relIndex (unitGroup (conj (meetOrder R n) (e.out * s))) *
        Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf (conj (meetOrder (meetOrder R s) n') e.out) u} =
      Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf (conj (meetOrder R n) (e.out * s)) u} :=
  relIndex_mul_card_of_le hdef (isOrder_conj (isOrder_meetOrder hR n) _)
    (isOrder_conj (isOrder_meetOrder (isOrder_meetOrder hR s) n') _) (unitGroup_conj_S'_le_shift hR hnn' hsn' e.out)

omit hnn' hsn' in
theorem relIndex_mul_card_vertex_forget (v : ClassSet (U (meetOrder R s))) :
    (unitGroup (conj (meetOrder R s) v.out)).relIndex (unitGroup (conj R v.out)) *
        Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf (conj (meetOrder R s) v.out) u} =
      Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf (conj R v.out) u} :=
  relIndex_mul_card_of_le hdef (isOrder_conj hR _) (isOrder_conj (isOrder_meetOrder hR s) _)
    (unitGroup_conj_R'_le hR v.out)

omit hnn' hsn' in
theorem relIndex_mul_card_vertex_shift (v : ClassSet (U (meetOrder R s))) :
    (unitGroup (conj (meetOrder R s) v.out)).relIndex (unitGroup (conj R (v.out * s))) *
        Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf (conj (meetOrder R s) v.out) u} =
      Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf (conj R (v.out * s)) u} :=
  relIndex_mul_card_of_le hdef (isOrder_conj hR _) (isOrder_conj (isOrder_meetOrder hR s) _)
    (unitGroup_conj_R'_le_shift hR v.out)

end StoreyWidths
p2m_reactivate "P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.DoubleCosetFibre"

end CSTower
p2m_reactivate "P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.DoubleCosetFibre P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.CSTower"

namespace CSTower

variable {a b : ℚ}

local notation "𝔾" => (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ
local notation "U" => Submodule.finiteIdeleStabilizer
local notation "conj" => Submodule.conjByFiniteIdele

def degEForget (R : Submodule ℤ ℍ[ℚ, a, b]) (n s n' : 𝔾) (e : ClassSet (U (meetOrder (meetOrder R s) n'))) : ℕ+ :=
  Nat.toPNat' ((unitGroup (conj (meetOrder (meetOrder R s) n') e.out)).relIndex (unitGroup (conj (meetOrder R n) e.out)))

def degEShift (R : Submodule ℤ ℍ[ℚ, a, b]) (n s n' : 𝔾) (e : ClassSet (U (meetOrder (meetOrder R s) n'))) : ℕ+ :=
  Nat.toPNat' ((unitGroup (conj (meetOrder (meetOrder R s) n') e.out)).relIndex (unitGroup (conj (meetOrder R n) (e.out * s))))

def degVForget (R : Submodule ℤ ℍ[ℚ, a, b]) (s : 𝔾) (v : ClassSet (U (meetOrder R s))) : ℕ+ :=
  Nat.toPNat' ((unitGroup (conj (meetOrder R s) v.out)).relIndex (unitGroup (conj R v.out)))

def degVShift (R : Submodule ℤ ℍ[ℚ, a, b]) (s : 𝔾) (v : ClassSet (U (meetOrder R s))) : ℕ+ :=
  Nat.toPNat' ((unitGroup (conj (meetOrder R s) v.out)).relIndex (unitGroup (conj R (v.out * s))))

section Assembly

open Finset

variable {q' : ℕ} (hdef : IsDefiniteRamifiedExactlyAt a b q') {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R)
  {n s n' : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ} (hnn' : n⁻¹ * n' ∈ U R) (hsn' : s * n' = n' * s)
include hdef hR hnn' hsn'

theorem coe_degEForget (e : ClassSet (U (meetOrder (meetOrder R s) n'))) :
    (degEForget R n s n' e : ℕ) =
      (unitGroup (conj (meetOrder (meetOrder R s) n') e.out)).relIndex (unitGroup (conj (meetOrder R n) e.out)) :=
  PNat.toPNat'_coe (w_forget hdef hR hnn' hsn' e).2

theorem coe_degEShift (e : ClassSet (U (meetOrder (meetOrder R s) n'))) :
    (degEShift R n s n' e : ℕ) =
      (unitGroup (conj (meetOrder (meetOrder R s) n') e.out)).relIndex (unitGroup (conj (meetOrder R n) (e.out * s))) :=
  PNat.toPNat'_coe (w_shift hdef hR hnn' hsn' e).2

omit hnn' hsn' in
theorem coe_degVForget (v : ClassSet (U (meetOrder R s))) :
    (degVForget R s v : ℕ) = (unitGroup (conj (meetOrder R s) v.out)).relIndex (unitGroup (conj R v.out)) := by
  haveI : Finite (unitGroup (conj R v.out)) := finite_unitGroup hdef (isOrder_conj hR _)
  exact PNat.toPNat'_coe (unitWeight_eq_relIndex_mul (isOrder_conj hR _) (isOrder_conj (isOrder_meetOrder hR s) _)
    (unitGroup_conj_R'_le hR v.out)).2

omit hnn' hsn' in
theorem coe_degVShift (v : ClassSet (U (meetOrder R s))) :
    (degVShift R s v : ℕ) = (unitGroup (conj (meetOrder R s) v.out)).relIndex (unitGroup (conj R (v.out * s))) := by
  haveI : Finite (unitGroup (conj R (v.out * s))) := finite_unitGroup hdef (isOrder_conj hR _)
  exact PNat.toPNat'_coe (unitWeight_eq_relIndex_mul (isOrder_conj hR _) (isOrder_conj (isOrder_meetOrder hR s) _)
    (unitGroup_conj_R'_le_shift hR v.out)).2

theorem assemble
    [Fintype (ClassSet (U (meetOrder (meetOrder R s) n')))] [Fintype (ClassSet (U (meetOrder R s)))]
    [DecidableEq (ClassSet (U (meetOrder R s)))] [DecidableEq (ClassSet (U (meetOrder R n)))]
    [DecidableEq (ClassSet (U R))]
    (d : ℕ) (hd : 0 < d)
    (sumV_forget : ∀ v' : ClassSet (U R),
      ∑ v ∈ univ.filter (fun v => classSetForget _ (U R) v = v'), (degVForget R s v : ℕ) = d)
    (harm_a_forget : ∀ (v : ClassSet (U (meetOrder R s))) (e' : ClassSet (U (meetOrder R n))),
      (classSetDegeneracyData R n).a e' = classSetForget _ (U R) v →
        ∑ e ∈ univ.filter (fun e => (classSetDegeneracyData (meetOrder R s) n').a e = v ∧
          classSetForget _ (U (meetOrder R n)) e = e'), (degEForget R n s n' e : ℕ) = degVForget R s v)
    (harm_b_forget : ∀ (v : ClassSet (U (meetOrder R s))) (e' : ClassSet (U (meetOrder R n))),
      (classSetDegeneracyData R n).b e' = classSetForget _ (U R) v →
        ∑ e ∈ univ.filter (fun e => (classSetDegeneracyData (meetOrder R s) n').b e = v ∧
          classSetForget _ (U (meetOrder R n)) e = e'), (degEForget R n s n' e : ℕ) = degVForget R s v)
    (sumV_shift : ∀ v' : ClassSet (U R),
      ∑ v ∈ univ.filter (fun v => ClassSet.mk (U R) (v.out * s) = v'), (degVShift R s v : ℕ) = d)
    (harm_a_shift : ∀ (v : ClassSet (U (meetOrder R s))) (e' : ClassSet (U (meetOrder R n))),
      (classSetDegeneracyData R n).a e' = ClassSet.mk (U R) (v.out * s) →
        ∑ e ∈ univ.filter (fun e => (classSetDegeneracyData (meetOrder R s) n').a e = v ∧
          ClassSet.mk (U (meetOrder R n)) (e.out * s) = e'), (degEShift R n s n' e : ℕ) = degVShift R s v)
    (harm_b_shift : ∀ (v : ClassSet (U (meetOrder R s))) (e' : ClassSet (U (meetOrder R n))),
      (classSetDegeneracyData R n).b e' = ClassSet.mk (U R) (v.out * s) →
        ∑ e ∈ univ.filter (fun e => (classSetDegeneracyData (meetOrder R s) n').b e = v ∧
          ClassSet.mk (U (meetOrder R n)) (e.out * s) = e'), (degEShift R n s n' e : ℕ) = degVShift R s v) :
    ∃ α β : (classSetDegeneracyData (meetOrder R s) n').FiniteHom (classSetDegeneracyData R n),
      α.mapV = classSetForget _ _ ∧
      α.mapE = classSetForget _ _ ∧
      (∀ e, (α.deg e : ℕ) *
          Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf (Submodule.conjByFiniteIdele (meetOrder (meetOrder R s) n') e.out) u} =
        Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf (Submodule.conjByFiniteIdele (meetOrder R n) e.out) u}) ∧
      (∀ v, (α.degV v : ℕ) *
          Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf (Submodule.conjByFiniteIdele (meetOrder R s) v.out) u} =
        Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf (Submodule.conjByFiniteIdele R v.out) u}) ∧
      (α.degTotal : ℕ) = d ∧
      (β.mapV = fun v => ClassSet.mk _ (v.out * s)) ∧
      (β.mapE = fun e => ClassSet.mk _ (e.out * s)) ∧
      (∀ e, (β.deg e : ℕ) *
          Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf (Submodule.conjByFiniteIdele (meetOrder (meetOrder R s) n') e.out) u} =
        Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf (Submodule.conjByFiniteIdele (meetOrder R n) (e.out * s)) u}) ∧
      (∀ v, (β.degV v : ℕ) *
          Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf (Submodule.conjByFiniteIdele (meetOrder R s) v.out) u} =
        Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf (Submodule.conjByFiniteIdele R (v.out * s)) u}) ∧
      (β.degTotal : ℕ) = d := by
  let dP : ℕ+ := ⟨d, hd⟩
  let α : (classSetDegeneracyData (meetOrder R s) n').FiniteHom (classSetDegeneracyData R n) :=
    { mapV := classSetForget _ _
      mapE := classSetForget _ _
      a_mapE := fun e => a_forget hR hnn' hsn' e
      b_mapE := fun e => b_forget hR hnn' hsn' e
      deg := degEForget R n s n'
      degV := degVForget R s
      degTotal := dP
      w_mapE := fun e => by
        apply PNat.eq
        rw [PNat.mul_coe, coe_degEForget hdef hR hnn' hsn' e]
        exact (w_forget hdef hR hnn' hsn' e).1
      sum_deg_a := harm_a_forget
      sum_deg_b := harm_b_forget
      sum_degV := sumV_forget }
  let β : (classSetDegeneracyData (meetOrder R s) n').FiniteHom (classSetDegeneracyData R n) :=
    { mapV := fun v => ClassSet.mk _ (v.out * s)
      mapE := fun e => ClassSet.mk _ (e.out * s)
      a_mapE := fun e => a_shift hR hnn' hsn' e
      b_mapE := fun e => b_shift hR hnn' hsn' e
      deg := degEShift R n s n'
      degV := degVShift R s
      degTotal := dP
      w_mapE := fun e => by
        apply PNat.eq
        rw [PNat.mul_coe, coe_degEShift hdef hR hnn' hsn' e]
        exact (w_shift hdef hR hnn' hsn' e).1
      sum_deg_a := harm_a_shift
      sum_deg_b := harm_b_shift
      sum_degV := sumV_shift }
  refine ⟨α, β, rfl, rfl, fun e => ?_, fun v => ?_, rfl, rfl, rfl, fun e => ?_, fun v => ?_, rfl⟩
  · show (degEForget R n s n' e : ℕ) * _ = _
    rw [coe_degEForget hdef hR hnn' hsn' e]
    exact relIndex_mul_card_edge_forget hdef hR hnn' hsn' e
  · show (degVForget R s v : ℕ) * _ = _
    rw [coe_degVForget hdef hR v]
    exact relIndex_mul_card_vertex_forget hdef hR v
  · show (degEShift R n s n' e : ℕ) * _ = _
    rw [coe_degEShift hdef hR hnn' hsn' e]
    exact relIndex_mul_card_edge_shift hdef hR hnn' hsn' e
  · show (degVShift R s v : ℕ) * _ = _
    rw [coe_degVShift hdef hR v]
    exact relIndex_mul_card_vertex_shift hdef hR v

end Assembly
p2m_reactivate "P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.DoubleCosetFibre P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.CSTower"

end CSTower
p2m_reactivate "P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.DoubleCosetFibre P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.CSTower"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.DoubleCosetFibre P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.CSTower"

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

noncomputable section

namespace CSTowerT21

variable {a b : ℚ}

local notation "ℍ𝔸" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ

abbrev Δ (a b : ℚ) : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ :=
  (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]).range

def somePlace : HeightOneSpectrum (𝓞 ℚ) := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨2, Nat.prime_two⟩

theorem tmul_one_injective : Function.Injective (fun d : ℍ[ℚ, a, b] => d ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) := by
  intro d d' h
  have h2 := congrArg (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] somePlace) h
  simp only [Submodule.finiteAdeleEvalAt_tmul] at h2
  have e1 : (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) somePlace = 1 := rfl
  rw [e1] at h2
  exact Algebra.TensorProduct.includeLeft_injective (S := ℚ)
    (algebraMap ℚ (somePlace.adicCompletion ℚ)).injective h2

theorem finiteIdeleDiagonal_injective : Function.Injective (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]) := by
  intro d d' h
  apply Units.ext
  have hv := congrArg (fun u : (ℍ𝔸)ˣ => (u : ℍ𝔸)) h
  simp only [Submodule.val_finiteIdeleDiagonal_apply] at hv
  exact tmul_one_injective hv

def unitOf {Λ : Submodule ℤ ℍ[ℚ, a, b]} {u : ℍ[ℚ, a, b]} (hu : IsUnitOf Λ u) : (ℍ[ℚ, a, b])ˣ :=
  ⟨u, hu.2.choose, hu.2.choose_spec.2.1, hu.2.choose_spec.2.2⟩

@[scoped simp] theorem val_unitOf {Λ : Submodule ℤ ℍ[ℚ, a, b]} {u : ℍ[ℚ, a, b]} (hu : IsUnitOf Λ u) :
    ((unitOf hu : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = u := rfl

theorem diag_unitOf_mem_stabH {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (y : (ℍ𝔸)ˣ) {u : ℍ[ℚ, a, b]}
    (hu : IsUnitOf (Submodule.conjByFiniteIdele Λ y) u) :
    Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (unitOf hu) ∈
      DoubleCosetFibre.stabH (Δ a b) (Submodule.finiteIdeleStabilizer Λ) y := by
  rw [DoubleCosetFibre.mem_stabH]
  obtain ⟨μ, hμ, hμe⟩ := (hΛ.isUnitOf_conjByFiniteIdele_iff Λ y u).mp hu
  refine ⟨⟨unitOf hu, rfl⟩, ?_⟩
  have : y⁻¹ * Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (unitOf hu) * y = μ := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Submodule.val_finiteIdeleDiagonal_apply, val_unitOf, hμe]
    simp only [← Units.val_mul]
    congr 1; group
  rw [this]; exact hμ

theorem exists_of_mem_stabH {Λ : Submodule ℤ ℍ[ℚ, a, b]} {y : (ℍ𝔸)ˣ}
    {δ : (ℍ𝔸)ˣ} (hδ : δ ∈ DoubleCosetFibre.stabH (Δ a b) (Submodule.finiteIdeleStabilizer Λ) y) :
    ∃ d : (ℍ[ℚ, a, b])ˣ, Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] d = δ :=
  MonoidHom.mem_range.mp (DoubleCosetFibre.mem_stabH.mp hδ).1

theorem isUnitOf_of_mem_stabH {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (y : (ℍ𝔸)ˣ)
    {δ : (ℍ𝔸)ˣ} (hδ : δ ∈ DoubleCosetFibre.stabH (Δ a b) (Submodule.finiteIdeleStabilizer Λ) y)
    (d : (ℍ[ℚ, a, b])ˣ) (hd : Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] d = δ) :
    IsUnitOf (Submodule.conjByFiniteIdele Λ y) (d : ℍ[ℚ, a, b]) := by
  rw [hΛ.isUnitOf_conjByFiniteIdele_iff Λ y]
  refine ⟨y⁻¹ * δ * y, (DoubleCosetFibre.mem_stabH.mp hδ).2, ?_⟩
  rw [← Units.val_mul, ← Units.val_mul, show y * (y⁻¹ * δ * y) * y⁻¹ = δ by group, ← hd,
    Submodule.val_finiteIdeleDiagonal_apply]

def unitsEquivStabH (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsOrder Λ) (y : (ℍ𝔸)ˣ) :
    {u : ℍ[ℚ, a, b] // IsUnitOf (Submodule.conjByFiniteIdele Λ y) u} ≃
      DoubleCosetFibre.stabH (Δ a b) (Submodule.finiteIdeleStabilizer Λ) y where
  toFun u := ⟨Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (unitOf u.2), diag_unitOf_mem_stabH hΛ y u.2⟩
  invFun δ := ⟨((exists_of_mem_stabH δ.2).choose : (ℍ[ℚ, a, b])ˣ),
    isUnitOf_of_mem_stabH hΛ y δ.2 _ (exists_of_mem_stabH δ.2).choose_spec⟩
  left_inv u := by
    apply Subtype.ext
    dsimp only
    generalize_proofs _ _ hu H
    rw [show H.choose = unitOf hu from finiteIdeleDiagonal_injective H.choose_spec, val_unitOf]
  right_inv δ := by
    apply Subtype.ext
    dsimp only
    generalize_proofs _ _ H1 H2
    rw [show unitOf H2 = H1.choose from Units.ext rfl]
    exact H1.choose_spec

theorem natCard_units_conj_eq (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsOrder Λ) (y : (ℍ𝔸)ˣ) :
    Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf (Submodule.conjByFiniteIdele Λ y) u} =
      Nat.card (DoubleCosetFibre.stabH (Δ a b) (Submodule.finiteIdeleStabilizer Λ) y) :=
  Nat.card_congr (unitsEquivStabH Λ hΛ y)

theorem card_mul_relIndex_of_le {G : Type*} [Group G] {A B : Subgroup G} (h : A ≤ B) :
    Nat.card A * A.relIndex B = Nat.card B := by
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv, Subgroup.relIndex]
  exact Subgroup.card_mul_index _

theorem dV_eq_relIndex (R R' : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsOrder R) (hR' : IsOrder R')
    (hle : Submodule.finiteIdeleStabilizer R' ≤ Submodule.finiteIdeleStabilizer R)
    (y : (ℍ𝔸)ˣ) (hfin : Finite {u : ℍ[ℚ, a, b] // IsUnitOf (Submodule.conjByFiniteIdele R y) u})
    (d : ℕ) (hd : d * Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf (Submodule.conjByFiniteIdele R' y) u} =
      Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf (Submodule.conjByFiniteIdele R y) u}) :
    d = (DoubleCosetFibre.stabH (Δ a b) (Submodule.finiteIdeleStabilizer R') y).relIndex
        (DoubleCosetFibre.stabH (Δ a b) (Submodule.finiteIdeleStabilizer R) y) := by
  rw [natCard_units_conj_eq R hR, natCard_units_conj_eq R' hR'] at hd
  have hAB := DoubleCosetFibre.stabH_mono (H := Δ a b) hle y
  haveI : Finite (DoubleCosetFibre.stabH (Δ a b) (Submodule.finiteIdeleStabilizer R) y) :=
    Finite.of_equiv _ (unitsEquivStabH R hR y)
  haveI : Finite (DoubleCosetFibre.stabH (Δ a b) (Submodule.finiteIdeleStabilizer R') y) :=
    Finite.of_injective _ (Subgroup.inclusion_injective hAB)
  have hc := card_mul_relIndex_of_le hAB
  rw [← hd, mul_comm d] at hc
  exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos hc).symm

theorem sum_filter_classSetForget_eq_relIndex
    (R R' : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsOrder R) (hR' : IsOrder R')
    (hle : Submodule.finiteIdeleStabilizer R' ≤ Submodule.finiteIdeleStabilizer R)
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer R'))]
    [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer R))]
    [(Submodule.finiteIdeleStabilizer R').IsFiniteRelIndex (Submodule.finiteIdeleStabilizer R)]
    (hfin : ∀ y : (ℍ𝔸)ˣ, Finite {u : ℍ[ℚ, a, b] // IsUnitOf (Submodule.conjByFiniteIdele R y) u})
    (dV : ClassSet (Submodule.finiteIdeleStabilizer R') → ℕ)
    (hdV : ∀ v, dV v *
        Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf (Submodule.conjByFiniteIdele R' v.out) u} =
      Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf (Submodule.conjByFiniteIdele R v.out) u})
    (x : ClassSet (Submodule.finiteIdeleStabilizer R)) :
    ∑ v ∈ Finset.univ.filter
        (fun v => classSetForget (Submodule.finiteIdeleStabilizer R') (Submodule.finiteIdeleStabilizer R) v = x),
      dV v = (Submodule.finiteIdeleStabilizer R').relIndex (Submodule.finiteIdeleStabilizer R) := by
  classical
  obtain ⟨x, rfl⟩ := ClassSet.mk_surjective x
  have key : ∀ v : ClassSet (Submodule.finiteIdeleStabilizer R'),
      dV v = (DoubleCosetFibre.stabH (Δ a b) (Submodule.finiteIdeleStabilizer R') v.out).relIndex
        (DoubleCosetFibre.stabH (Δ a b) (Submodule.finiteIdeleStabilizer R) v.out) :=
    fun v => dV_eq_relIndex R R' hR hR' hle v.out (hfin _) (dV v) (hdV v)
  rw [Finset.sum_congr rfl (fun v _ => key v),
    Finset.sum_subtype (Finset.univ.filter (fun v => classSetForget (Submodule.finiteIdeleStabilizer R')
        (Submodule.finiteIdeleStabilizer R) v = ClassSet.mk (Submodule.finiteIdeleStabilizer R) x))
      (p := fun v => classSetForget (Submodule.finiteIdeleStabilizer R') (Submodule.finiteIdeleStabilizer R) v =
        ClassSet.mk (Submodule.finiteIdeleStabilizer R) x)
      (fun v => by rw [Finset.mem_filter]; simp)]
  convert DoubleCosetFibre.sum_fibre_relIndex_stabH_eq_relIndex (Δ a b) (Submodule.finiteIdeleStabilizer R)
    (Submodule.finiteIdeleStabilizer R') hle x using 3 <;>
    first | rfl | infer_instance | exact Subsingleton.elim _ _

end CSTowerT21
p2m_reactivate "P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.DoubleCosetFibre P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.CSTower P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.CSTowerT21"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.DoubleCosetFibre P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.CSTower P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.CSTowerT21"

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

noncomputable section

namespace CSTower9

variable {a b : ℚ}

local notation "ℍ𝔸" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "U" => Submodule.finiteIdeleStabilizer
local notation "conj" => Submodule.conjByFiniteIdele

open CSTowerT21 in

theorem sum_filter_forget_forget_eq
    (R R' S S' : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsOrder R) (hR' : IsOrder R') (hS : IsOrder S) (hS' : IsOrder S')
    (hSR : U S ≤ U R) (hR'R : U R' ≤ U R) (h₁ : U S' ≤ U S) (h₂ : U S' ≤ U R') (hinf : U S ⊓ U R' ≤ U S')
    (hsurj : ∀ k : ↥(U R), ∃ k₁ : ↥(U S), ((k₁ : (ℍ𝔸)ˣ)⁻¹ * k) ∈ U R')
    [Fintype (ClassSet (U S'))] [DecidableEq (ClassSet (U R'))] [DecidableEq (ClassSet (U S))]
    [(U R').IsFiniteRelIndex (U R)] [(U S').IsFiniteRelIndex (U S)]
    (hfinS : ∀ y : (ℍ𝔸)ˣ, Finite {u : ℍ[ℚ, a, b] // IsUnitOf (conj S y) u})
    (hfinR : ∀ y : (ℍ𝔸)ˣ, Finite {u : ℍ[ℚ, a, b] // IsUnitOf (conj R y) u})
    (degE : ClassSet (U S') → ℕ)
    (hdegE : ∀ e, degE e * Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf (conj S' e.out) u} =
      Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf (conj S e.out) u})
    (degV : ClassSet (U R') → ℕ)
    (hdegV : ∀ v, degV v * Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf (conj R' v.out) u} =
      Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf (conj R v.out) u})
    (v : ClassSet (U R')) (e' : ClassSet (U S))
    (he' : classSetForget (U S) (U R) e' = classSetForget (U R') (U R) v) :
    ∑ e ∈ Finset.univ.filter (fun e : ClassSet (U S') =>
        classSetForget (U S') (U R') e = v ∧ classSetForget (U S') (U S) e = e'), degE e = degV v := by
  classical

  set y : (ℍ𝔸)ˣ := v.out with hy
  set z : (ℍ𝔸)ˣ := e'.out with hz
  have hv : v = ClassSet.mk (U R') y := (DoubleCoset.out_eq' _ _ v).symm
  have he : e' = ClassSet.mk (U S) z := (DoubleCoset.out_eq' _ _ e').symm
  have hyz : DoubleCoset.mk (Δ a b) (U R) z = DoubleCoset.mk (Δ a b) (U R) y := he'

  have hPiff : ∀ e : ClassSet (U S'),
      (classSetForget (U S') (U R') e = v ∧ classSetForget (U S') (U S) e = e') ↔
      (DoubleCoset.mk (Δ a b) (U R') e.out = DoubleCoset.mk (Δ a b) (U R') y ∧
        DoubleCoset.mk (Δ a b) (U S) e.out = DoubleCoset.mk (Δ a b) (U S) z) := by
    intro e
    rw [hv, he]
    rfl
  rw [Finset.sum_subtype (Finset.univ.filter (fun e : ClassSet (U S') =>
        classSetForget (U S') (U R') e = v ∧ classSetForget (U S') (U S) e = e'))
      (p := fun e => classSetForget (U S') (U R') e = v ∧ classSetForget (U S') (U S) e = e') (fun e => by simp)]
  rw [Fintype.sum_equiv (Equiv.subtypeEquivRight hPiff) (fun e => degE e.1) (fun c => degE c.1) (fun _ => rfl)]

  have hsummand : ∀ c : {c : ClassSet (U S') //
      DoubleCoset.mk (Δ a b) (U R') c.out = DoubleCoset.mk (Δ a b) (U R') y ∧
        DoubleCoset.mk (Δ a b) (U S) c.out = DoubleCoset.mk (Δ a b) (U S) z},
      degE c.1 = (DoubleCosetFibre.stabH (Δ a b) (U S') c.1.out).relIndex (DoubleCosetFibre.stabH (Δ a b) (U S) c.1.out) :=
    fun c => dV_eq_relIndex S S' hS hS' h₁ c.1.out (hfinS _) (degE c.1) (hdegE c.1)
  rw [Fintype.sum_congr _ _ hsummand, dV_eq_relIndex R R' hR hR' hR'R y (hfinR _) (degV v) (hdegV v)]

  exact Subgroup.sum_fibre_doubleCoset_relIndex_inf_map_conj_eq_relIndex_of_le_inf
    (Δ a b) (U R) (U S) (U R') (U S') hSR hR'R h₁ h₂ hinf hsurj z y hyz

theorem sum_filter_shift_forget_eq
    (R R' S S' : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsOrder R) (hR' : IsOrder R') (hS : IsOrder S) (hS' : IsOrder S')
    (hSR : U S ≤ U R) (hR'R : U R' ≤ U R) (h₁ : U S' ≤ U S) (h₂ : U S' ≤ U R') (hinf : U S ⊓ U R' ≤ U S')
    (hsurj : ∀ k : ↥(U R), ∃ k₁ : ↥(U S), ((k₁ : (ℍ𝔸)ˣ)⁻¹ * k) ∈ U R')
    [Fintype (ClassSet (U S'))] [DecidableEq (ClassSet (U R'))] [DecidableEq (ClassSet (U S))]
    [(U R').IsFiniteRelIndex (U R)] [(U S').IsFiniteRelIndex (U S)]
    (hfinS : ∀ y : (ℍ𝔸)ˣ, Finite {u : ℍ[ℚ, a, b] // IsUnitOf (conj S y) u})
    (hfinR : ∀ y : (ℍ𝔸)ˣ, Finite {u : ℍ[ℚ, a, b] // IsUnitOf (conj R y) u})
    (degE : ClassSet (U S') → ℕ)
    (hdegE : ∀ e, degE e * Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf (conj S' e.out) u} =
      Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf (conj S e.out) u})
    (degV : ClassSet (U R') → ℕ)
    (hdegV : ∀ v, degV v * Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf (conj R' v.out) u} =
      Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf (conj R v.out) u})

    (t t' : (ℍ𝔸)ˣ)
    (σ' : ClassSet (U S') ≃ ClassSet (U S')) (σ : ClassSet (U S) ≃ ClassSet (U S))
    (hcomm : ∀ e : ClassSet (U S'), classSetForget (U S') (U S) (σ' e) = σ (classSetForget (U S') (U S) e))
    (ha' : ∀ e : ClassSet (U S'), classSetForget (U S') (U R') (σ' e) = ClassSet.mk (U R') (e.out * t'))
    (ha : ∀ e : ClassSet (U S), classSetForget (U S) (U R) (σ e) = ClassSet.mk (U R) (e.out * t))
    (hdegσ : ∀ e, degE (σ' e) = degE e)
    (v : ClassSet (U R')) (e' : ClassSet (U S))
    (he' : ClassSet.mk (U R) (e'.out * t) = classSetForget (U R') (U R) v) :
    ∑ e ∈ Finset.univ.filter (fun e : ClassSet (U S') =>
        ClassSet.mk (U R') (e.out * t') = v ∧ classSetForget (U S') (U S) e = e'), degE e = degV v := by
  classical

  have hre : ∀ e : ClassSet (U S'),
      (ClassSet.mk (U R') (e.out * t') = v ∧ classSetForget (U S') (U S) e = e') ↔
      (classSetForget (U S') (U R') (σ' e) = v ∧ classSetForget (U S') (U S) (σ' e) = σ e') := by
    intro e
    rw [ha', hcomm]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [h2]⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, σ.injective h2⟩
  have step : ∑ e ∈ Finset.univ.filter (fun e : ClassSet (U S') =>
        ClassSet.mk (U R') (e.out * t') = v ∧ classSetForget (U S') (U S) e = e'), degE e =
      ∑ e ∈ Finset.univ.filter (fun e : ClassSet (U S') =>
        classSetForget (U S') (U R') e = v ∧ classSetForget (U S') (U S) e = σ e'), degE e := by
    rw [Finset.sum_filter, Finset.sum_filter]
    rw [← Equiv.sum_comp σ' (fun e => if classSetForget (U S') (U R') e = v ∧
        classSetForget (U S') (U S) e = σ e' then degE e else 0)]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [hre e, hdegσ]
  rw [step]
  exact sum_filter_forget_forget_eq R R' S S' hR hR' hS hS' hSR hR'R h₁ h₂ hinf hsurj hfinS hfinR degE hdegE degV hdegV
    v (σ e') (by rw [ha, he'])

end CSTower9
p2m_reactivate "P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.DoubleCosetFibre P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.CSTower P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.CSTowerT21"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.DoubleCosetFibre P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.CSTower P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.CSTowerT21"

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

namespace DoubleCosetFibre

variable {G : Type*} [Group G]

theorem stabH_map_conj (H K : Subgroup G) (g x : G) :
    stabH H (K.map (MulAut.conj g).toMonoidHom) x = stabH H K (x * g) := by
  ext h
  rw [mem_stabH, mem_stabH, Subgroup.mem_map_equiv, MulAut.conj_symm_apply,
    show g⁻¹ * (x⁻¹ * h * x) * g = (x * g)⁻¹ * h * (x * g) by group]

theorem mk_map_conj_eq_iff (H K : Subgroup G) (g x y : G) :
    DoubleCoset.mk H (K.map (MulAut.conj g).toMonoidHom) x = DoubleCoset.mk H (K.map (MulAut.conj g).toMonoidHom) y ↔
      DoubleCoset.mk H K (x * g) = DoubleCoset.mk H K (y * g) := by
  rw [DoubleCoset.eq, DoubleCoset.eq]
  constructor
  · rintro ⟨h, hh, k, hk, he⟩
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply] at hk
    exact ⟨h, hh, g⁻¹ * k * g, hk, by rw [he]; group⟩
  · rintro ⟨h, hh, k, hk, he⟩
    refine ⟨h, hh, g * k * g⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, show g⁻¹ * (g * k * g⁻¹) * g = k by group]
      exact hk
    · have e2 : y = (h * (x * g) * k) * g⁻¹ := by rw [← he]; group
      rw [e2]; group

theorem isFiniteRelIndex_of_square (K K₁ K₂ K₁₂ : Subgroup G) (hK₁ : K₁ ≤ K)
    (h₂ : K₁₂ ≤ K₂) (hinf : K₁ ⊓ K₂ ≤ K₁₂)
    (hsurj : ∀ k : K, ∃ k₁ : K₁, ((k₁ : G)⁻¹ * k) ∈ K₂) [K₂.IsFiniteRelIndex K] :
    K₁₂.IsFiniteRelIndex K₁ := by
  haveI : Finite (K ⧸ K₂.subgroupOf K) := Subgroup.finite_quotient_of_finiteIndex
  haveI : Finite (K₁ ⧸ K₁₂.subgroupOf K₁) :=
    Finite.of_injective _ (theta_bijective K K₁ K₂ K₁₂ hK₁ h₂ hinf hsurj).1
  rw [Subgroup.isFiniteRelIndex_iff_finiteIndex]
  exact Subgroup.finiteIndex_of_finite_quotient

end DoubleCosetFibre
p2m_reactivate "P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.DoubleCosetFibre P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.CSTower P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.CSTowerT21"

noncomputable section

namespace CSTowerU9

variable {a b : ℚ}

local notation "ℍ𝔸" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "U" => Submodule.finiteIdeleStabilizer
local notation "conj" => Submodule.conjByFiniteIdele

open CSTowerT21 DoubleCosetFibre

theorem d_eq_relIndex_shift (X X' : Submodule ℤ ℍ[ℚ, a, b]) (hX : IsOrder X) (hX' : IsOrder X') (g : (ℍ𝔸)ˣ)
    (hle : U X' ≤ (U X).map (MulAut.conj g).toMonoidHom)
    (y : (ℍ𝔸)ˣ) (hfin : Finite {u : ℍ[ℚ, a, b] // IsUnitOf (conj X (y * g)) u})
    (d : ℕ) (hd : d * Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf (conj X' y) u} =
      Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf (conj X (y * g)) u}) :
    d = (stabH (Δ a b) (U X') y).relIndex (stabH (Δ a b) ((U X).map (MulAut.conj g).toMonoidHom) y) := by
  rw [natCard_units_conj_eq X hX, natCard_units_conj_eq X' hX'] at hd
  rw [stabH_map_conj] at ⊢
  have hAB : stabH (Δ a b) (U X') y ≤ stabH (Δ a b) (U X) (y * g) := by
    rw [← stabH_map_conj]; exact stabH_mono hle y
  haveI : Finite (stabH (Δ a b) (U X) (y * g)) := Finite.of_equiv _ (unitsEquivStabH X hX (y * g))
  haveI : Finite (stabH (Δ a b) (U X') y) := Finite.of_injective _ (Subgroup.inclusion_injective hAB)
  have hc := card_mul_relIndex_of_le hAB
  rw [← hd, mul_comm d] at hc
  exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos hc).symm

theorem finite_units {q' : ℕ} (hdef : IsDefiniteRamifiedExactlyAt a b q') {X : Submodule ℤ ℍ[ℚ, a, b]} (hX : IsOrder X)
    (y : (ℍ𝔸)ˣ) : Finite {u : ℍ[ℚ, a, b] // IsUnitOf (conj X y) u} :=
  haveI := CSTower.finite_unitGroup hdef (CSTower.isOrder_conj hX y)
  Finite.of_equiv _ (CSTower.isUnitOfEquiv (CSTower.isOrder_conj hX y)).symm

section Storey

open Finset

variable {q' : ℕ} (hdef : IsDefiniteRamifiedExactlyAt a b q') {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R)
  {n s n' : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}
  (hnn' : n⁻¹ * n' ∈ Submodule.finiteIdeleStabilizer R) (hsn' : s * n' = n' * s)
include hdef hR hnn' hsn'

omit hdef hR hnn' hsn' in

theorem mem_stab_conj_iff {X : Submodule ℤ ℍ[ℚ, a, b]} (hX : IsOrder X) (g u : (ℍ𝔸)ˣ) :
    u ∈ U (conj X g) ↔ g⁻¹ * u * g ∈ U X := by
  rw [Submodule.mem_finiteIdeleStabilizer_iff, Submodule.mem_finiteIdeleStabilizer_iff,
    Submodule.finiteAdeleBox_conjByFiniteIdele X hX.fg hX.spanTop g]
  set B : AddSubgroup (ℍ𝔸) := (Submodule.finiteAdeleBox X : AddSubgroup (ℍ𝔸)) with hB
  set φ := (AddMonoidHom.mulRight ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)).comp (AddMonoidHom.mulLeft (g : ℍ𝔸)) with hφ

  have memL : ∀ (w : (ℍ𝔸)ˣ) (S : Set (ℍ𝔸)) (x : ℍ𝔸), x ∈ w • S ↔ ((w⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * x ∈ S := by
    intro w S x
    rw [Set.mem_smul_set_iff_inv_smul_mem, Units.smul_def, smul_eq_mul]
  have memφ : ∀ x : ℍ𝔸, x ∈ ((B.map φ : AddSubgroup (ℍ𝔸)) : Set (ℍ𝔸)) ↔ ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * x * g ∈ (B : Set (ℍ𝔸)) := by
    intro x
    exact CSTower.mem_map_conj_iff B g x
  constructor
  · intro h
    ext y
    have hy := Set.ext_iff.mp h ((g : ℍ𝔸) * y * ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸))
    rw [memL, memφ, memφ] at hy
    rw [memL]
    have e1 : ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * (((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * ((g : ℍ𝔸) * y * ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸))) * g =
        (((g⁻¹ * u * g)⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * y := by
      simp only [mul_inv_rev, inv_inv, Units.val_mul, mul_assoc, Units.inv_mul_cancel_left, Units.inv_mul, mul_one]
    have e2 : ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * ((g : ℍ𝔸) * y * ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) * g = y := by
      simp only [mul_assoc, Units.inv_mul_cancel_left, Units.inv_mul, mul_one]
    rw [e1, e2] at hy
    exact hy
  · intro h
    ext x
    have hx := Set.ext_iff.mp h (((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * x * g)
    rw [memL] at hx
    rw [memL, memφ, memφ]
    have e1 : (((g⁻¹ * u * g)⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * (((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * x * g) =
        ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * (((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * x) * g := by
      simp only [mul_inv_rev, inv_inv, Units.val_mul, mul_assoc, Units.mul_inv_cancel_left]
    rw [e1] at hx
    exact hx

omit hdef hR hnn' hsn' in

theorem stab_normal_of_conj_eq {X : Submodule ℤ ℍ[ℚ, a, b]} (hX : IsOrder X) {g : (ℍ𝔸)ˣ} (hg : conj X g = X)
    (u : (ℍ𝔸)ˣ) (hu : u ∈ U X) : g⁻¹ * u * g ∈ U X := by
  rw [← hg] at hu
  rwa [mem_stab_conj_iff hX] at hu

omit hdef hnn' hsn' in

theorem relIndex_map_conj_eq_of_inv (d : ℕ)
    (hidx : (U (meetOrder R s⁻¹)).relIndex (U R) = d) :
    (U (meetOrder R s)).relIndex ((U R).map (MulAut.conj s).toMonoidHom) = d := by
  have hmem : ∀ (t u : (ℍ𝔸)ˣ), u ∈ U (meetOrder R t) ↔ u ∈ U R ∧ t⁻¹ * u * t ∈ U R :=
    fun t u => CSTower.mem_stab_meetOrder_iff hR t u
  have e1 : (U (meetOrder R s)).map (MulAut.conj s⁻¹).toMonoidHom = U (meetOrder R s⁻¹) := by
    ext u
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, hmem, hmem, inv_inv]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨by simpa [mul_assoc] using h2, ?_⟩
      simpa [mul_assoc] using h1
    · rintro ⟨h1, h2⟩
      refine ⟨by simpa [mul_assoc] using h2, ?_⟩
      simpa [mul_assoc] using h1
  have e2 : ((U R).map (MulAut.conj s).toMonoidHom).map (MulAut.conj s⁻¹).toMonoidHom = U R := by
    ext u
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv]
    simp [mul_assoc]
  rw [← hidx, ← Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj s⁻¹).toMonoidHom) (U (meetOrder R s))
    ((U R).map (MulAut.conj s).toMonoidHom) (MulAut.conj s⁻¹).injective, e1, e2]

omit hdef hnn' hsn' in

theorem stab_R'_le_map : U (meetOrder R s) ≤ (U R).map (MulAut.conj s).toMonoidHom := by
  intro u hu
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  exact ((CSTower.mem_stab_meetOrder_iff hR s u).mp hu).2

omit hdef in

theorem stab_S'_le_map : U (meetOrder (meetOrder R s) n') ≤ (U (meetOrder R n)).map (MulAut.conj s).toMonoidHom := by
  intro u hu
  rw [CSTower.meetOrder_meetOrder_comm hR hnn' hsn'] at hu
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  exact ((CSTower.mem_stab_meetOrder_iff (CSTower.isOrder_meetOrder hR n) s u).mp hu).2

omit hnn' hsn' in

theorem sumV_forget (d : ℕ) (hd : 0 < d)
    (IDX : (Submodule.finiteIdeleStabilizer (meetOrder R s)).relIndex (Submodule.finiteIdeleStabilizer R) = d)
    [Fintype (ClassSet (U (meetOrder R s)))] [DecidableEq (ClassSet (U R))] (v' : ClassSet (U R)) :
    ∑ v ∈ univ.filter (fun v => classSetForget _ (U R) v = v'), (CSTower.degVForget R s v : ℕ) = d := by
  haveI : (U (meetOrder R s)).IsFiniteRelIndex (U R) := ⟨by rw [IDX]; exact hd.ne'⟩
  rw [← IDX]
  refine sum_filter_classSetForget_eq_relIndex R (meetOrder R s) hR (CSTower.isOrder_meetOrder hR s)
    (CSTower.stab_R'_le_R hR) (fun y => finite_units hdef hR y) _ (fun v => ?_) v'
  beta_reduce
  rw [CSTower.coe_degVForget hdef hR v]
  exact CSTower.relIndex_mul_card_vertex_forget hdef hR v

theorem harm_a_forget (d : ℕ) (hd : 0 < d)
    (IDX : (Submodule.finiteIdeleStabilizer (meetOrder R s)).relIndex (Submodule.finiteIdeleStabilizer R) = d)
    (F1 : Submodule.finiteIdeleStabilizer (meetOrder R n) ⊓ Submodule.finiteIdeleStabilizer (meetOrder R s) ≤
      Submodule.finiteIdeleStabilizer (meetOrder (meetOrder R s) n'))
    (F2 : ∀ k : ↥(Submodule.finiteIdeleStabilizer R), ∃ k₁ : ↥(Submodule.finiteIdeleStabilizer (meetOrder R n)),
      ((k₁ : (ℍ𝔸)ˣ)⁻¹ * k) ∈ Submodule.finiteIdeleStabilizer (meetOrder R s))
    [Fintype (ClassSet (U (meetOrder (meetOrder R s) n')))]
    [DecidableEq (ClassSet (U (meetOrder R s)))] [DecidableEq (ClassSet (U (meetOrder R n)))]
    (v : ClassSet (U (meetOrder R s))) (e' : ClassSet (U (meetOrder R n)))
    (he' : (classSetDegeneracyData R n).a e' = classSetForget _ (U R) v) :
    ∑ e ∈ univ.filter (fun e => (classSetDegeneracyData (meetOrder R s) n').a e = v ∧
      classSetForget _ (U (meetOrder R n)) e = e'), (CSTower.degEForget R n s n' e : ℕ) = CSTower.degVForget R s v := by
  haveI : (U (meetOrder R s)).IsFiniteRelIndex (U R) := ⟨by rw [IDX]; exact hd.ne'⟩
  haveI : (U (meetOrder (meetOrder R s) n')).IsFiniteRelIndex (U (meetOrder R n)) :=
    isFiniteRelIndex_of_square (U R) (U (meetOrder R n)) (U (meetOrder R s)) _ (CSTower.stab_meetOrder_le hR n)
      (CSTower.stab_S'_le_R' hR) F1 F2
  exact CSTower9.sum_filter_forget_forget_eq R (meetOrder R s) (meetOrder R n) (meetOrder (meetOrder R s) n')
    hR (CSTower.isOrder_meetOrder hR s) (CSTower.isOrder_meetOrder hR n)
    (CSTower.isOrder_meetOrder (CSTower.isOrder_meetOrder hR s) n')
    (CSTower.stab_meetOrder_le hR n) (CSTower.stab_R'_le_R hR) (CSTower.stab_S'_le_S hR hnn' hsn')
    (CSTower.stab_S'_le_R' hR) F1 F2 (fun y => finite_units hdef (CSTower.isOrder_meetOrder hR n) y)
    (fun y => finite_units hdef hR y)
    (fun e => (CSTower.degEForget R n s n' e : ℕ))
    (fun e => by beta_reduce; rw [CSTower.coe_degEForget hdef hR hnn' hsn' e]; exact CSTower.relIndex_mul_card_edge_forget hdef hR hnn' hsn' e)
    (fun v => (CSTower.degVForget R s v : ℕ))
    (fun v => by beta_reduce; rw [CSTower.coe_degVForget hdef hR v]; exact CSTower.relIndex_mul_card_vertex_forget hdef hR v)
    v e' he'

theorem harm_b_forget (d : ℕ) (hd : 0 < d)
    (IDX : (Submodule.finiteIdeleStabilizer (meetOrder R s)).relIndex (Submodule.finiteIdeleStabilizer R) = d)
    (F1 : Submodule.finiteIdeleStabilizer (meetOrder R n) ⊓ Submodule.finiteIdeleStabilizer (meetOrder R s) ≤
      Submodule.finiteIdeleStabilizer (meetOrder (meetOrder R s) n'))
    (F2 : ∀ k : ↥(Submodule.finiteIdeleStabilizer R), ∃ k₁ : ↥(Submodule.finiteIdeleStabilizer (meetOrder R n)),
      ((k₁ : (ℍ𝔸)ˣ)⁻¹ * k) ∈ Submodule.finiteIdeleStabilizer (meetOrder R s))
    (NS : ∀ u ∈ U (meetOrder R n), n⁻¹ * u * n ∈ U (meetOrder R n))
    (NN'S : n⁻¹ * n' ∈ U (meetOrder R n))
    (hnorm : Submodule.conjByFiniteIdele (meetOrder R n) n = meetOrder R n)
    (hnorm' : Submodule.conjByFiniteIdele (meetOrder (meetOrder R s) n') n' = meetOrder (meetOrder R s) n')
    (hsq : ∀ x : ClassSet (U (meetOrder R n)), classSetShift _ n (classSetShift _ n x) = x)
    (hsq' : ∀ x : ClassSet (U (meetOrder (meetOrder R s) n')), classSetShift _ n' (classSetShift _ n' x) = x)
    [Fintype (ClassSet (U (meetOrder (meetOrder R s) n')))]
    [DecidableEq (ClassSet (U (meetOrder R s)))] [DecidableEq (ClassSet (U (meetOrder R n)))]
    (v : ClassSet (U (meetOrder R s))) (e' : ClassSet (U (meetOrder R n)))
    (he' : (classSetDegeneracyData R n).b e' = classSetForget _ (U R) v) :
    ∑ e ∈ univ.filter (fun e => (classSetDegeneracyData (meetOrder R s) n').b e = v ∧
      classSetForget _ (U (meetOrder R n)) e = e'), (CSTower.degEForget R n s n' e : ℕ) = CSTower.degVForget R s v := by
  classical
  haveI : (U (meetOrder R s)).IsFiniteRelIndex (U R) := ⟨by rw [IDX]; exact hd.ne'⟩
  haveI : (U (meetOrder (meetOrder R s) n')).IsFiniteRelIndex (U (meetOrder R n)) :=
    isFiniteRelIndex_of_square (U R) (U (meetOrder R n)) (U (meetOrder R s)) _ (CSTower.stab_meetOrder_le hR n)
      (CSTower.stab_S'_le_R' hR) F1 F2
  have hS : IsOrder (meetOrder R n) := CSTower.isOrder_meetOrder hR n
  have hR' : IsOrder (meetOrder R s) := CSTower.isOrder_meetOrder hR s
  have hS' : IsOrder (meetOrder (meetOrder R s) n') := CSTower.isOrder_meetOrder hR' n'
  have h₁ := CSTower.stab_S'_le_S hR hnn' hsn'

  have hconjS' : ∀ x : (ℍ𝔸)ˣ, conj (meetOrder (meetOrder R s) n') (x * n') = conj (meetOrder (meetOrder R s) n') x := by
    intro x; rw [← CSTower.conj_conj hS' n' x, hnorm']
  have hconjS : ∀ x : (ℍ𝔸)ˣ, conj (meetOrder R n) (x * n') = conj (meetOrder R n) x := by
    intro x; rw [← CSTower.conj_conj hS n' x, CSTower.conj_eq_conj_of_inv_mul_mem hS NN'S, hnorm]
  refine CSTower9.sum_filter_shift_forget_eq R (meetOrder R s) (meetOrder R n) (meetOrder (meetOrder R s) n')
    hR hR' hS hS' (CSTower.stab_meetOrder_le hR n) (CSTower.stab_R'_le_R hR) h₁ (CSTower.stab_S'_le_R' hR) F1 F2
    (fun y => finite_units hdef hS y) (fun y => finite_units hdef hR y)
    (fun e => (CSTower.degEForget R n s n' e : ℕ))
    (fun e => by beta_reduce; rw [CSTower.coe_degEForget hdef hR hnn' hsn' e]; exact CSTower.relIndex_mul_card_edge_forget hdef hR hnn' hsn' e)
    (fun v => (CSTower.degVForget R s v : ℕ))
    (fun v => by beta_reduce; rw [CSTower.coe_degVForget hdef hR v]; exact CSTower.relIndex_mul_card_vertex_forget hdef hR v)
    n n' (Function.Involutive.toPerm _ hsq') (Function.Involutive.toPerm _ hsq) ?_ ?_ ?_ ?_ v e' he'
  ·
    intro e
    show ClassSet.mk (U (meetOrder R n)) ((ClassSet.mk (U (meetOrder (meetOrder R s) n')) (e.out * n')).out) =
      ClassSet.mk (U (meetOrder R n)) ((ClassSet.mk (U (meetOrder R n)) e.out).out * n)
    rw [CSTower.mk_out_mul n NS e.out]
    have := CSTower.classSetForget_mk h₁ (e.out * n')
    rw [show classSetForget (U (meetOrder (meetOrder R s) n')) (U (meetOrder R n))
        (ClassSet.mk (U (meetOrder (meetOrder R s) n')) (e.out * n')) =
        ClassSet.mk (U (meetOrder R n)) ((ClassSet.mk (U (meetOrder (meetOrder R s) n')) (e.out * n')).out) from rfl] at this
    rw [this, DoubleCoset.eq]
    exact ⟨1, Subgroup.one_mem _, (n⁻¹ * n')⁻¹, Subgroup.inv_mem _ NN'S, by group⟩
  · intro e
    exact CSTower.classSetForget_mk (CSTower.stab_S'_le_R' hR) (e.out * n')
  · intro e
    exact CSTower.classSetForget_mk (CSTower.stab_meetOrder_le hR n) (e.out * n)
  ·
    intro e
    beta_reduce
    rw [CSTower.coe_degEForget hdef hR hnn' hsn', CSTower.coe_degEForget hdef hR hnn' hsn']
    show (CSTower.unitGroup (conj (meetOrder (meetOrder R s) n') (ClassSet.mk (U (meetOrder (meetOrder R s) n')) (e.out * n')).out)).relIndex
        (CSTower.unitGroup (conj (meetOrder R n) (ClassSet.mk (U (meetOrder (meetOrder R s) n')) (e.out * n')).out)) = _
    have key := CSTower.relIndex_unitGroup_conj_out hS hS' (V := U (meetOrder (meetOrder R s) n')) (e.out * n') 1
      (fun u hu => by simpa using h₁ hu) le_rfl
    rw [mul_one, mul_one] at key
    rw [key, hconjS', hconjS]

omit hnn' hsn' in

theorem sumV_shift (d : ℕ) (hd : 0 < d)
    (IDXs : (Submodule.finiteIdeleStabilizer (meetOrder R s)).relIndex
      ((Submodule.finiteIdeleStabilizer R).map (MulAut.conj s).toMonoidHom) = d)
    [Fintype (ClassSet (U (meetOrder R s)))] [DecidableEq (ClassSet (U R))] (v' : ClassSet (U R)) :
    ∑ v ∈ univ.filter (fun v => ClassSet.mk (U R) (v.out * s) = v'), (CSTower.degVShift R s v : ℕ) = d := by
  classical
  set K : Subgroup (ℍ𝔸)ˣ := (U R).map (MulAut.conj s).toMonoidHom with hK
  haveI : (U (meetOrder R s)).IsFiniteRelIndex K := ⟨by rw [IDXs]; exact hd.ne'⟩
  have hR' : IsOrder (meetOrder R s) := CSTower.isOrder_meetOrder hR s
  set x : (ℍ𝔸)ˣ := v'.out * s⁻¹ with hx
  have hv' : v' = ClassSet.mk (U R) (x * s) := by
    rw [hx, inv_mul_cancel_right]; exact (DoubleCoset.out_eq' _ _ v').symm
  have hPiff : ∀ v : ClassSet (U (meetOrder R s)),
      ClassSet.mk (U R) (v.out * s) = v' ↔ DoubleCoset.mk (Δ a b) K v.out = DoubleCoset.mk (Δ a b) K x := by
    intro v; rw [hv', hK, mk_map_conj_eq_iff]
  rw [Finset.sum_subtype (univ.filter (fun v : ClassSet (U (meetOrder R s)) => ClassSet.mk (U R) (v.out * s) = v'))
      (p := fun v => ClassSet.mk (U R) (v.out * s) = v') (fun v => by simp)]
  rw [Fintype.sum_equiv (Equiv.subtypeEquivRight hPiff) (fun v => (CSTower.degVShift R s v.1 : ℕ))
    (fun c => (CSTower.degVShift R s c.1 : ℕ)) (fun _ => rfl)]
  have hsummand : ∀ c : {c : ClassSet (U (meetOrder R s)) // DoubleCoset.mk (Δ a b) K c.out = DoubleCoset.mk (Δ a b) K x},
      (CSTower.degVShift R s c.1 : ℕ) = (stabH (Δ a b) (U (meetOrder R s)) c.1.out).relIndex (stabH (Δ a b) K c.1.out) := by
    intro c
    rw [CSTower.coe_degVShift hdef hR]
    exact d_eq_relIndex_shift R (meetOrder R s) hR hR' s (stab_R'_le_map hR) c.1.out (finite_units hdef hR _) _
      (CSTower.relIndex_mul_card_vertex_shift hdef hR c.1)
  rw [Fintype.sum_congr _ _ hsummand, ← IDXs]
  exact Subgroup.sum_fibre_doubleCoset_relIndex_inf_map_conj_eq_relIndex (Δ a b) K (U (meetOrder R s))
    (stab_R'_le_map hR) x

theorem harm_a_shift (d : ℕ) (hd : 0 < d)
    (IDXs : (Submodule.finiteIdeleStabilizer (meetOrder R s)).relIndex
      ((Submodule.finiteIdeleStabilizer R).map (MulAut.conj s).toMonoidHom) = d)
    (F1s : (Submodule.finiteIdeleStabilizer (meetOrder R n)).map (MulAut.conj s).toMonoidHom ⊓
        Submodule.finiteIdeleStabilizer (meetOrder R s) ≤ Submodule.finiteIdeleStabilizer (meetOrder (meetOrder R s) n'))
    (F2s : ∀ k : ↥((Submodule.finiteIdeleStabilizer R).map (MulAut.conj s).toMonoidHom),
      ∃ k₁ : ↥((Submodule.finiteIdeleStabilizer (meetOrder R n)).map (MulAut.conj s).toMonoidHom),
        ((k₁ : (ℍ𝔸)ˣ)⁻¹ * k) ∈ Submodule.finiteIdeleStabilizer (meetOrder R s))
    [Fintype (ClassSet (U (meetOrder (meetOrder R s) n')))]
    [DecidableEq (ClassSet (U (meetOrder R s)))] [DecidableEq (ClassSet (U (meetOrder R n)))]
    (v : ClassSet (U (meetOrder R s))) (e' : ClassSet (U (meetOrder R n)))
    (he' : (classSetDegeneracyData R n).a e' = ClassSet.mk (U R) (v.out * s)) :
    ∑ e ∈ univ.filter (fun e => (classSetDegeneracyData (meetOrder R s) n').a e = v ∧
      ClassSet.mk (U (meetOrder R n)) (e.out * s) = e'), (CSTower.degEShift R n s n' e : ℕ) = CSTower.degVShift R s v := by
  classical
  set K : Subgroup (ℍ𝔸)ˣ := (U R).map (MulAut.conj s).toMonoidHom with hK
  set K₁ : Subgroup (ℍ𝔸)ˣ := (U (meetOrder R n)).map (MulAut.conj s).toMonoidHom with hK₁
  have hR' : IsOrder (meetOrder R s) := CSTower.isOrder_meetOrder hR s
  have hS : IsOrder (meetOrder R n) := CSTower.isOrder_meetOrder hR n
  have hS' : IsOrder (meetOrder (meetOrder R s) n') := CSTower.isOrder_meetOrder hR' n'
  have hK₁K : K₁ ≤ K := Subgroup.map_mono (CSTower.stab_meetOrder_le hR n)
  have hK₂K : U (meetOrder R s) ≤ K := stab_R'_le_map hR
  have h₁ : U (meetOrder (meetOrder R s) n') ≤ K₁ := stab_S'_le_map hR hnn' hsn'
  have h₂ : U (meetOrder (meetOrder R s) n') ≤ U (meetOrder R s) := CSTower.stab_S'_le_R' hR
  haveI : (U (meetOrder R s)).IsFiniteRelIndex K := ⟨by rw [IDXs]; exact hd.ne'⟩
  haveI : (U (meetOrder (meetOrder R s) n')).IsFiniteRelIndex K₁ :=
    isFiniteRelIndex_of_square K K₁ (U (meetOrder R s)) _ hK₁K h₂ F1s F2s

  set y : (ℍ𝔸)ˣ := v.out with hy
  set z : (ℍ𝔸)ˣ := e'.out * s⁻¹ with hz
  have hv : v = ClassSet.mk (U (meetOrder R s)) y := (DoubleCoset.out_eq' _ _ v).symm
  have he : e' = ClassSet.mk (U (meetOrder R n)) (z * s) := by
    rw [hz, inv_mul_cancel_right]; exact (DoubleCoset.out_eq' _ _ e').symm
  have hyz : DoubleCoset.mk (Δ a b) K z = DoubleCoset.mk (Δ a b) K y := by
    rw [hK, mk_map_conj_eq_iff, hz, inv_mul_cancel_right]
    exact he'
  have hPiff : ∀ e : ClassSet (U (meetOrder (meetOrder R s) n')),
      ((classSetDegeneracyData (meetOrder R s) n').a e = v ∧ ClassSet.mk (U (meetOrder R n)) (e.out * s) = e') ↔
      (DoubleCoset.mk (Δ a b) (U (meetOrder R s)) e.out = DoubleCoset.mk (Δ a b) (U (meetOrder R s)) y ∧
        DoubleCoset.mk (Δ a b) K₁ e.out = DoubleCoset.mk (Δ a b) K₁ z) := by
    intro e
    rw [hv, he, hK₁, mk_map_conj_eq_iff]
    rfl
  rw [Finset.sum_subtype (univ.filter (fun e : ClassSet (U (meetOrder (meetOrder R s) n')) =>
        (classSetDegeneracyData (meetOrder R s) n').a e = v ∧ ClassSet.mk (U (meetOrder R n)) (e.out * s) = e'))
      (p := fun e => (classSetDegeneracyData (meetOrder R s) n').a e = v ∧ ClassSet.mk (U (meetOrder R n)) (e.out * s) = e')
      (fun e => by simp)]
  rw [Fintype.sum_equiv (Equiv.subtypeEquivRight hPiff) (fun e => (CSTower.degEShift R n s n' e.1 : ℕ))
    (fun c => (CSTower.degEShift R n s n' c.1 : ℕ)) (fun _ => rfl)]
  have hsummand : ∀ c : {c : ClassSet (U (meetOrder (meetOrder R s) n')) //
      DoubleCoset.mk (Δ a b) (U (meetOrder R s)) c.out = DoubleCoset.mk (Δ a b) (U (meetOrder R s)) y ∧
        DoubleCoset.mk (Δ a b) K₁ c.out = DoubleCoset.mk (Δ a b) K₁ z},
      (CSTower.degEShift R n s n' c.1 : ℕ) =
        (stabH (Δ a b) (U (meetOrder (meetOrder R s) n')) c.1.out).relIndex (stabH (Δ a b) K₁ c.1.out) := by
    intro c
    rw [CSTower.coe_degEShift hdef hR hnn' hsn']
    exact d_eq_relIndex_shift (meetOrder R n) (meetOrder (meetOrder R s) n') hS hS' s h₁ c.1.out
      (finite_units hdef hS _) _ (CSTower.relIndex_mul_card_edge_shift hdef hR hnn' hsn' c.1)
  rw [Fintype.sum_congr _ _ hsummand, CSTower.coe_degVShift hdef hR v,
    d_eq_relIndex_shift R (meetOrder R s) hR hR' s hK₂K y (finite_units hdef hR _) _
      (CSTower.relIndex_mul_card_vertex_shift hdef hR v)]
  exact Subgroup.sum_fibre_doubleCoset_relIndex_inf_map_conj_eq_relIndex_of_le_inf
    (Δ a b) K K₁ (U (meetOrder R s)) (U (meetOrder (meetOrder R s) n')) hK₁K hK₂K h₁ h₂ F1s F2s z y hyz

theorem harm_b_shift (d : ℕ) (hd : 0 < d)
    (IDXs : (Submodule.finiteIdeleStabilizer (meetOrder R s)).relIndex
      ((Submodule.finiteIdeleStabilizer R).map (MulAut.conj s).toMonoidHom) = d)
    (F1s : (Submodule.finiteIdeleStabilizer (meetOrder R n)).map (MulAut.conj s).toMonoidHom ⊓
        Submodule.finiteIdeleStabilizer (meetOrder R s) ≤ Submodule.finiteIdeleStabilizer (meetOrder (meetOrder R s) n'))
    (F2s : ∀ k : ↥((Submodule.finiteIdeleStabilizer R).map (MulAut.conj s).toMonoidHom),
      ∃ k₁ : ↥((Submodule.finiteIdeleStabilizer (meetOrder R n)).map (MulAut.conj s).toMonoidHom),
        ((k₁ : (ℍ𝔸)ˣ)⁻¹ * k) ∈ Submodule.finiteIdeleStabilizer (meetOrder R s))
    (NS : ∀ u ∈ U (meetOrder R n), n⁻¹ * u * n ∈ U (meetOrder R n))
    (NN'S : n⁻¹ * n' ∈ U (meetOrder R n))
    (hnorm : Submodule.conjByFiniteIdele (meetOrder R n) n = meetOrder R n)
    (hnorm' : Submodule.conjByFiniteIdele (meetOrder (meetOrder R s) n') n' = meetOrder (meetOrder R s) n')
    (hsq : ∀ x : ClassSet (U (meetOrder R n)), classSetShift _ n (classSetShift _ n x) = x)
    (hsq' : ∀ x : ClassSet (U (meetOrder (meetOrder R s) n')), classSetShift _ n' (classSetShift _ n' x) = x)
    [Fintype (ClassSet (U (meetOrder (meetOrder R s) n')))]
    [DecidableEq (ClassSet (U (meetOrder R s)))] [DecidableEq (ClassSet (U (meetOrder R n)))]
    (v : ClassSet (U (meetOrder R s))) (e' : ClassSet (U (meetOrder R n)))
    (he' : (classSetDegeneracyData R n).b e' = ClassSet.mk (U R) (v.out * s)) :
    ∑ e ∈ univ.filter (fun e => (classSetDegeneracyData (meetOrder R s) n').b e = v ∧
      ClassSet.mk (U (meetOrder R n)) (e.out * s) = e'), (CSTower.degEShift R n s n' e : ℕ) = CSTower.degVShift R s v := by
  classical
  have hR' : IsOrder (meetOrder R s) := CSTower.isOrder_meetOrder hR s
  have hS : IsOrder (meetOrder R n) := CSTower.isOrder_meetOrder hR n
  have hS' : IsOrder (meetOrder (meetOrder R s) n') := CSTower.isOrder_meetOrder hR' n'
  have h₂ : U (meetOrder (meetOrder R s) n') ≤ U (meetOrder R s) := CSTower.stab_S'_le_R' hR
  let σ' : Equiv.Perm (ClassSet (U (meetOrder (meetOrder R s) n'))) := Function.Involutive.toPerm _ hsq'
  let σ : Equiv.Perm (ClassSet (U (meetOrder R n))) := Function.Involutive.toPerm _ hsq
  have hσ' : ∀ e, σ' e = ClassSet.mk (U (meetOrder (meetOrder R s) n')) (e.out * n') := fun _ => rfl
  have hσ : ∀ e, σ e = ClassSet.mk (U (meetOrder R n)) (e.out * n) := fun _ => rfl

  have hb' : ∀ e, (classSetDegeneracyData (meetOrder R s) n').b e = (classSetDegeneracyData (meetOrder R s) n').a (σ' e) := by
    intro e
    rw [hσ']
    exact (CSTower.classSetForget_mk h₂ (e.out * n')).symm

  have hcomm : ∀ e : ClassSet (U (meetOrder (meetOrder R s) n')),
      ClassSet.mk (U (meetOrder R n)) ((σ' e).out * s) = σ (ClassSet.mk (U (meetOrder R n)) (e.out * s)) := by
    intro e
    rw [hσ', hσ, CSTower.mk_out_mul s (fun u hu => CSTower.inv_mul_mul_mem_stab_S_of_mem_stab_S' hR hnn' hsn' hu) (e.out * n'),
      CSTower.mk_out_mul n NS (e.out * s), DoubleCoset.eq]
    refine ⟨1, Subgroup.one_mem _, (n⁻¹ * n')⁻¹, Subgroup.inv_mem _ NN'S, ?_⟩
    rw [one_mul, mul_assoc (e.out : (ℍ𝔸)ˣ) n' s, ← hsn', ← mul_assoc]
    group

  have hdeg : ∀ e, (CSTower.degEShift R n s n' (σ' e) : ℕ) = CSTower.degEShift R n s n' e := by
    intro e
    rw [CSTower.coe_degEShift hdef hR hnn' hsn', CSTower.coe_degEShift hdef hR hnn' hsn', hσ']
    have key := CSTower.relIndex_unitGroup_conj_out hS hS' (V := U (meetOrder (meetOrder R s) n')) (e.out * n') s
      (fun u hu => CSTower.inv_mul_mul_mem_stab_S_of_mem_stab_S' hR hnn' hsn' hu) le_rfl
    rw [key, ← CSTower.conj_conj hS' n' e.out, hnorm', mul_assoc, ← hsn', ← mul_assoc,
      ← CSTower.conj_conj hS n' (e.out * s), CSTower.conj_eq_conj_of_inv_mul_mem hS NN'S, hnorm]

  have hre : ∀ e, ((classSetDegeneracyData (meetOrder R s) n').b e = v ∧ ClassSet.mk (U (meetOrder R n)) (e.out * s) = e') ↔
      ((classSetDegeneracyData (meetOrder R s) n').a (σ' e) = v ∧ ClassSet.mk (U (meetOrder R n)) ((σ' e).out * s) = σ e') := by
    intro e
    rw [hb', hcomm]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [h2]⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, σ.injective h2⟩
  have step : ∑ e ∈ univ.filter (fun e => (classSetDegeneracyData (meetOrder R s) n').b e = v ∧
        ClassSet.mk (U (meetOrder R n)) (e.out * s) = e'), (CSTower.degEShift R n s n' e : ℕ) =
      ∑ e ∈ univ.filter (fun e => (classSetDegeneracyData (meetOrder R s) n').a e = v ∧
        ClassSet.mk (U (meetOrder R n)) (e.out * s) = σ e'), (CSTower.degEShift R n s n' e : ℕ) := by
    rw [Finset.sum_filter, Finset.sum_filter]
    rw [← Equiv.sum_comp σ' (fun e => if (classSetDegeneracyData (meetOrder R s) n').a e = v ∧
        ClassSet.mk (U (meetOrder R n)) (e.out * s) = σ e' then (CSTower.degEShift R n s n' e : ℕ) else 0)]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [hre e, hdeg]
  rw [step]
  refine harm_a_shift hdef hR hnn' hsn' d hd IDXs F1s F2s v (σ e') ?_
  rw [hσ, ← he']
  exact CSTower.classSetForget_mk (CSTower.stab_meetOrder_le hR n) (e'.out * n)

end Storey
p2m_reactivate "P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.DoubleCosetFibre P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.CSTower P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.CSTowerT21"

end CSTowerU9
p2m_reactivate "P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.DoubleCosetFibre P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.CSTower P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.CSTowerT21"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.DoubleCosetFibre P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.CSTower P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.CSTowerT21"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField Pointwise
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

namespace CSTowerT21
namespace Stab

variable {a b : ℚ}

local notation "ℍ𝔸" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "ev" w => Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w

noncomputable abbrev evU (w : HeightOneSpectrum (𝓞 ℚ)) :
    (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ →* (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ :=
  Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w).toRingHom.toMonoidHom

def boxGen (Λ : Submodule ℤ ℍ[ℚ, a, b]) : Set (ℍ𝔸) :=
  {x | ∃ z ∈ Λ, ∃ c : FiniteAdeleRing (𝓞 ℚ) ℚ,
      (∀ v : HeightOneSpectrum (𝓞 ℚ), c v ∈ v.adicCompletionIntegers ℚ) ∧ x = z ⊗ₜ[ℚ] c}

theorem mem_box_iff_span {Λ : Submodule ℤ ℍ[ℚ, a, b]} {x : ℍ𝔸} :
    x ∈ Submodule.finiteAdeleBox Λ ↔ x ∈ Submodule.span ℤ (boxGen Λ) := by
  have e : Submodule.finiteAdeleBox Λ = (Submodule.span ℤ (boxGen Λ)).toAddSubgroup := by
    rw [Submodule.span_int_eq_addSubgroupClosure]; rfl
  rw [e]; rfl

theorem box_mul_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    {x y : ℍ𝔸} (hx : x ∈ Submodule.finiteAdeleBox Λ) (hy : y ∈ Submodule.finiteAdeleBox Λ) :
    x * y ∈ Submodule.finiteAdeleBox Λ := by
  rw [mem_box_iff_span] at hx hy ⊢
  induction hy using Submodule.span_induction with
  | mem y hy' =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hy'
    induction hx using Submodule.span_induction with
    | mem x hx' =>
      obtain ⟨z', hz', c', hc', rfl⟩ := hx'
      refine Submodule.subset_span ⟨z' * z, hΛ.mul_mem hz' hz, c' * c, fun v => ?_, ?_⟩
      · have e : (c' * c) v = c' v * c v := rfl
        rw [e]
        exact mul_mem (hc' v) (hc v)
      · rw [Algebra.TensorProduct.tmul_mul_tmul]
    | zero => rw [zero_mul]; exact zero_mem _
    | add x₁ x₂ _ _ h₁ h₂ => rw [add_mul]; exact add_mem h₁ h₂
    | smul m x₁ _ h₁ => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ h₁
  | zero => rw [mul_zero]; exact zero_mem _
  | add y₁ y₂ _ _ h₁ h₂ => rw [mul_add]; exact add_mem h₁ h₂
  | smul m y₁ _ h₁ => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h₁

theorem one_mem_box {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) : (1 : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ := by
  unfold Submodule.finiteAdeleBox
  refine AddSubgroup.subset_closure ⟨1, hΛ.one_mem, 1, fun v => ?_, rfl⟩
  have e : (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) v = 1 := rfl
  rw [e]; exact one_mem _

private theorem _root_.CSTowerT21.Stab.mem_stabilizer_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (u : (ℍ𝔸)ˣ) :
    u ∈ Submodule.finiteIdeleStabilizer Λ ↔
      (u : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ ∧ ((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ := by
  constructor
  · intro hu
    have key : ∀ w : (ℍ𝔸)ˣ, w ∈ Submodule.finiteIdeleStabilizer Λ → (w : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ := by
      intro w hw
      have h := (Submodule.mem_finiteIdeleStabilizer_iff Λ w).mp hw
      have h1 : (w : ℍ𝔸) * 1 ∈ w • ((Submodule.finiteAdeleBox Λ : AddSubgroup ℍ𝔸) : Set ℍ𝔸) :=
        Set.smul_mem_smul_set (one_mem_box hΛ)
      rw [h, mul_one] at h1
      exact h1
    exact ⟨key u hu, key u⁻¹ (inv_mem hu)⟩
  · rintro ⟨hu, hui⟩
    rw [Submodule.mem_finiteIdeleStabilizer_iff]
    apply Set.Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact box_mul_mem hΛ hu hx
    · intro x hx
      refine ⟨(u⁻¹ : (ℍ𝔸)ˣ) • x, box_mul_mem hΛ hui hx, ?_⟩
      show (u : ℍ𝔸) * (((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * x) = x
      rw [← mul_assoc, Units.mul_inv, one_mul]

p2m_export "CSTowerT21.Stab" "mem_stabilizer_iff"

private theorem _root_.CSTowerT21.Stab.isOrder_meetOrder {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) (g : (ℍ𝔸)ˣ) :
    IsOrder (meetOrder R g) :=
  hR.inf (IsOrder.conjByFiniteIdele R hR g)

p2m_export "CSTowerT21.Stab" "isOrder_meetOrder"

theorem mem_finiteIdeleStabilizer_meetOrder_iff {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) (g u : (ℍ𝔸)ˣ) :
    u ∈ Submodule.finiteIdeleStabilizer (meetOrder R g) ↔
      u ∈ Submodule.finiteIdeleStabilizer R ∧ g⁻¹ * u * g ∈ Submodule.finiteIdeleStabilizer R := by
  obtain ⟨hbox, -, hle, hconj⟩ := IsOrder.finiteAdeleBox_inf_conjByFiniteIdele_eq_and_finiteIdeleStabilizer_le R hR g
  constructor
  · intro hu
    exact ⟨hle hu, hconj u hu⟩
  · rintro ⟨hu, hgu⟩
    have hRg : IsOrder (meetOrder R g) := isOrder_meetOrder hR g
    rw [mem_stabilizer_iff hR] at hu hgu
    rw [mem_stabilizer_iff hRg]
    rw [show meetOrder R g = R ⊓ Submodule.conjByFiniteIdele R g from rfl, hbox]
    have key : ∀ w : ℍ𝔸, w ∈ Submodule.finiteAdeleBox R →
        ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * w * (g : ℍ𝔸) ∈ Submodule.finiteAdeleBox R →
        w ∈ Submodule.finiteAdeleBox R ⊓ (Submodule.finiteAdeleBox R).map
          ((AddMonoidHom.mulRight ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)).comp (AddMonoidHom.mulLeft (g : ℍ𝔸))) := by
      intro w hw hgw
      refine ⟨hw, ⟨_, hgw, ?_⟩⟩
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulLeft, AddMonoidHom.coe_mulRight]
      rw [← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one]
    refine ⟨key _ hu.1 ?_, key _ hu.2 ?_⟩
    · simpa only [Units.val_mul] using hgu.1
    · have e : (((g⁻¹ * u * g)⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) = ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * ((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * (g : ℍ𝔸) := by
        rw [mul_inv_rev, mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul, mul_assoc]
      rw [← e]; exact hgu.2

theorem finiteIdeleStabilizer_meetOrder_eq {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) (g : (ℍ𝔸)ˣ) :
    Submodule.finiteIdeleStabilizer (meetOrder R g) =
      Submodule.finiteIdeleStabilizer R ⊓ (Submodule.finiteIdeleStabilizer R).map (MulAut.conj g).toMonoidHom := by
  ext u
  rw [mem_finiteIdeleStabilizer_meetOrder_iff hR, Subgroup.mem_inf, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

def localBoxGen (Λ : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :=
  {x | ∃ z ∈ Λ, ∃ c : v.adicCompletion ℚ, c ∈ v.adicCompletionIntegers ℚ ∧ x = z ⊗ₜ[ℚ] c}

theorem mem_localBox_iff_span {Λ : Submodule ℤ ℍ[ℚ, a, b]} {v : HeightOneSpectrum (𝓞 ℚ)}
    {x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ} :
    x ∈ Submodule.localBox Λ v ↔ x ∈ Submodule.span ℤ (localBoxGen Λ v) := by
  have : Submodule.localBox Λ v = (Submodule.span ℤ (localBoxGen Λ v)).toAddSubgroup := by
    rw [Submodule.span_int_eq_addSubgroupClosure]; rfl
  rw [this]; rfl

theorem finiteAdeleEvalAt_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (v : HeightOneSpectrum (𝓞 ℚ))
    {x : ℍ𝔸} (hx : x ∈ Submodule.finiteAdeleBox Λ) :
    (ev v) x ∈ Submodule.localBox Λ v := by
  rw [mem_box_iff_span] at hx
  rw [mem_localBox_iff_span]
  induction hx using Submodule.span_induction with
  | mem x hx' =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hx'
    refine Submodule.subset_span ⟨z, hz, c v, hc v, ?_⟩
    simp [Submodule.finiteAdeleEvalAt, Submodule.finiteAdeleEvalAlgHom_apply]
  | zero => rw [map_zero]; exact zero_mem _
  | add x₁ x₂ _ _ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
  | smul m x₁ _ h₁ => rw [map_zsmul]; exact Submodule.smul_mem _ _ h₁

private theorem _root_.CSTowerT21.Stab.localBox_mul_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (v : HeightOneSpectrum (𝓞 ℚ))
    {x y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ} (hx : x ∈ Submodule.localBox Λ v) (hy : y ∈ Submodule.localBox Λ v) :
    x * y ∈ Submodule.localBox Λ v := by
  rw [mem_localBox_iff_span] at hx hy ⊢
  induction hy using Submodule.span_induction with
  | mem y hy' =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hy'
    induction hx using Submodule.span_induction with
    | mem x hx' =>
      obtain ⟨z', hz', c', hc', rfl⟩ := hx'
      refine Submodule.subset_span ⟨z' * z, hΛ.mul_mem hz' hz, c' * c, mul_mem hc' hc, ?_⟩
      rw [Algebra.TensorProduct.tmul_mul_tmul]
    | zero => rw [zero_mul]; exact zero_mem _
    | add x₁ x₂ _ _ h₁ h₂ => rw [add_mul]; exact add_mem h₁ h₂
    | smul m x₁ _ h₁ => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ h₁
  | zero => rw [mul_zero]; exact zero_mem _
  | add y₁ y₂ _ _ h₁ h₂ => rw [mul_add]; exact add_mem h₁ h₂
  | smul m y₁ _ h₁ => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h₁

p2m_export "CSTowerT21.Stab" "localBox_mul_mem"
theorem one_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    (1 : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox Λ v := by
  rw [mem_localBox_iff_span]
  exact Submodule.subset_span ⟨1, hΛ.one_mem, 1, one_mem _, rfl⟩

theorem ev_smul (v : HeightOneSpectrum (𝓞 ℚ)) (c : ℚ) (x : ℍ𝔸) : (ev v) (c • x) = c • (ev v) x := map_smul _ _ _

theorem ratSmul_eq_one_tmul_mul (v : HeightOneSpectrum (𝓞 ℚ)) (c : ℚ) (x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :
    c • x = ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ (v.adicCompletion ℚ) c) * x := by
  have e1 : ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ (v.adicCompletion ℚ) c) = c • (1 : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) := by
    rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
  rw [e1, smul_mul_assoc, one_mul]

theorem smul_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (v : HeightOneSpectrum (𝓞 ℚ)) {c : ℚ}
    (hc : algebraMap ℚ (v.adicCompletion ℚ) c ∈ v.adicCompletionIntegers ℚ)
    {x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ} (hx : x ∈ Submodule.localBox Λ v) : c • x ∈ Submodule.localBox Λ v := by
  rw [ratSmul_eq_one_tmul_mul, mem_localBox_iff_span]
  rw [mem_localBox_iff_span] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨z, hz, c', hc', rfl⟩ := hy
    refine Submodule.subset_span ⟨z, hz, algebraMap ℚ (v.adicCompletion ℚ) c * c', mul_mem hc hc', ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [mul_zero]; exact zero_mem _
  | add x₁ x₂ _ _ h₁ h₂ => rw [mul_add]; exact add_mem h₁ h₂
  | smul m x₁ _ h₁ => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h₁

theorem inv_natCast_mem_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ)
    (hnv : ((n : ℕ) : 𝓞 ℚ) ∉ v.asIdeal) :
    ((n : v.adicCompletion ℚ))⁻¹ ∈ v.adicCompletionIntegers ℚ := by
  have h1 : ((n : ℕ) : v.adicCompletion ℚ) = algebraMap (𝓞 ℚ) (v.adicCompletion ℚ) ((n : ℕ) : 𝓞 ℚ) := by
    rw [map_natCast]
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h1]
  have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) v ((n : ℕ) : 𝓞 ℚ)
  erw [h2, (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := ℚ) v).mpr hnv, inv_one]

theorem algebraMap_inv_natCast_mem (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) (hnv : ((n : ℕ) : 𝓞 ℚ) ∉ v.asIdeal) :
    algebraMap ℚ (v.adicCompletion ℚ) ((n : ℚ)⁻¹) ∈ v.adicCompletionIntegers ℚ := by
  rw [map_inv₀, map_natCast]; exact inv_natCast_mem_adicCompletionIntegers v n hnv

theorem ev_mem_localBox_of_smul_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} {c : ℕ} (hc : c ≠ 0) (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : ((c : ℕ) : 𝓞 ℚ) ∉ v.asIdeal) {y : ℍ𝔸} (hy : (c : ℚ) • y ∈ Submodule.finiteAdeleBox Λ) :
    (ev v) y ∈ Submodule.localBox Λ v := by
  have := smul_mem_localBox v (algebraMap_inv_natCast_mem v c hv) (finiteAdeleEvalAt_mem_localBox v hy)
  rwa [ev_smul, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hc : (c : ℚ) ≠ 0), one_smul] at this

theorem natGenerator_dvd_iff' (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    Rat.HeightOneSpectrum.natGenerator v ∣ n ↔ ((n : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff, ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) n,
    Ideal.apply_mem_of_equiv_iff]

theorem not_mem_of_prime_ne {p ℓ : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime) (hne : ℓ ≠ p) {v : HeightOneSpectrum (𝓞 ℚ)}
    (hv : ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) : ((ℓ : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := by
  intro hℓv
  rw [← natGenerator_dvd_iff'] at hv hℓv
  have h1 := (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator v) hp).mp hv
  have h2 := (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator v) hℓ).mp hℓv
  exact hne (h2.symm.trans h1)

theorem exists_place (p : ℕ) (hp : p.Prime) : ∃ v : HeightOneSpectrum (𝓞 ℚ), ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
  refine ⟨(Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨p, hp⟩, ?_⟩
  rw [← natGenerator_dvd_iff']
  have : Rat.HeightOneSpectrum.natGenerator ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨p, hp⟩) = p := by
    have e := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply ⟨p, hp⟩
    exact congrArg Subtype.val e
  rw [this]

theorem mem_localBoxUnits_iff' (Λ : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ))
    (t : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) :
    t ∈ Submodule.localBoxUnits Λ v ↔
      (t : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox Λ v ∧
        ((t⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox Λ v :=
  Submodule.mem_localBoxUnits_iff Λ v t

theorem conj_mem_localBoxUnits_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (v : HeightOneSpectrum (𝓞 ℚ))
    {g : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ} (hg : g ∈ Submodule.localBoxUnits Λ v)
    (t : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) :
    g⁻¹ * t * g ∈ Submodule.localBoxUnits Λ v ↔ t ∈ Submodule.localBoxUnits Λ v := by
  rw [mem_localBoxUnits_iff'] at hg
  have key : ∀ s : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ, s ∈ Submodule.localBoxUnits Λ v →
      g⁻¹ * s * g ∈ Submodule.localBoxUnits Λ v := by
    intro s hs
    rw [mem_localBoxUnits_iff'] at hs ⊢
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul, Units.val_mul]
      exact localBox_mul_mem hΛ v (localBox_mul_mem hΛ v hg.2 hs.1) hg.1
    · rw [mul_inv_rev, mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul]
      exact localBox_mul_mem hΛ v hg.2 (localBox_mul_mem hΛ v hs.2 hg.1)
  constructor
  · intro h
    have hgi : g⁻¹ ∈ Submodule.localBoxUnits Λ v := by
      rw [mem_localBoxUnits_iff', inv_inv]; exact ⟨hg.2, hg.1⟩
    have h2 := key _ h

    have key' : ∀ s : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ, s ∈ Submodule.localBoxUnits Λ v →
        g * s * g⁻¹ ∈ Submodule.localBoxUnits Λ v := by
      intro s hs
      rw [mem_localBoxUnits_iff'] at hs ⊢
      refine ⟨?_, ?_⟩
      · rw [Units.val_mul, Units.val_mul]
        exact localBox_mul_mem hΛ v (localBox_mul_mem hΛ v hg.1 hs.1) hg.2
      · rw [mul_inv_rev, mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul]
        exact localBox_mul_mem hΛ v hg.1 (localBox_mul_mem hΛ v hs.2 hg.2)
    have h3 := key' _ h
    have e : g * (g⁻¹ * t * g) * g⁻¹ = t := by group
    rwa [e] at h3
  · exact key t

theorem map_mem_localBoxUnits_of_mem_stabilizer {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {u : (ℍ𝔸)ˣ}
    (hu : u ∈ Submodule.finiteIdeleStabilizer Λ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    (evU (a := a) (b := b) v) u ∈ Submodule.localBoxUnits Λ v :=
  (IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits Λ hΛ u).mp hu v

theorem map_mem_localBoxUnits_of_mem_primeHeckeSet {Λ : Submodule ℤ ℍ[ℚ, a, b]} {p : ℕ} (hp : p ≠ 0)
    {g : (ℍ𝔸)ˣ} (hg : g ∈ primeHeckeSet Λ p) {v : HeightOneSpectrum (𝓞 ℚ)} (hv : ((p : ℕ) : 𝓞 ℚ) ∉ v.asIdeal) :
    (evU (a := a) (b := b) v) g ∈ Submodule.localBoxUnits Λ v := by
  obtain ⟨h1, h2, -, -⟩ := hg
  rw [mem_localBoxUnits_iff', Units.coe_map, Units.coe_map_inv]
  exact ⟨finiteAdeleEvalAt_mem_localBox v h1, ev_mem_localBox_of_smul_mem hp v hv h2⟩

theorem mem_localBoxUnits_meetOrder_iff {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) (g : (ℍ𝔸)ˣ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (t : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) :
    t ∈ Submodule.localBoxUnits (meetOrder R g) v ↔
      t ∈ Submodule.localBoxUnits R v ∧ ((evU (a := a) (b := b) v) g)⁻¹ * t * (evU (a := a) (b := b) v) g ∈ Submodule.localBoxUnits R v := by
  have hc : IsOrder (Submodule.conjByFiniteIdele R g) := IsOrder.conjByFiniteIdele R hR g
  have hbox : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ∈ Submodule.localBox (meetOrder R g) v ↔
      x ∈ Submodule.localBox R v ∧
        (ev v) ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * x * (ev v) (g : ℍ𝔸) ∈ Submodule.localBox R v := by
    intro x
    rw [show meetOrder R g = R ⊓ Submodule.conjByFiniteIdele R g from rfl,
      Submodule.localBox_inf R (Submodule.conjByFiniteIdele R g) hR.fg hR.spanTop hc.fg hc.spanTop v,
      AddSubgroup.mem_inf, Submodule.mem_localBox_conjByFiniteIdele_iff R hR.fg hR.spanTop g v]
    have i3 : (ev v) (g : ℍ𝔸) * (ev v) ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    have i4 : (ev v) ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * (ev v) (g : ℍ𝔸) = 1 := by rw [← map_mul, Units.inv_mul, map_one]
    refine and_congr Iff.rfl ⟨?_, ?_⟩
    · rintro ⟨y, hy, rfl⟩
      rw [← mul_assoc, ← mul_assoc, i4, one_mul, mul_assoc, i4, mul_one]; exact hy
    · intro h
      refine ⟨_, h, ?_⟩
      rw [← mul_assoc, ← mul_assoc, i3, one_mul, mul_assoc, i3, mul_one]
  rw [mem_localBoxUnits_iff', mem_localBoxUnits_iff', mem_localBoxUnits_iff', hbox, hbox]
  simp only [Units.val_mul, Units.coe_map, Units.coe_map_inv, mul_inv_rev, inv_inv, MonoidHom.coe_coe,
    RingHom.coe_coe, RingHom.toMonoidHom_eq_coe, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨h1, h3⟩, by simpa only [mul_assoc, MonoidHom.coe_coe, RingHom.coe_coe, AlgHom.coe_toRingHom] using h2,
      by simpa only [mul_assoc, MonoidHom.coe_coe, RingHom.coe_coe, AlgHom.coe_toRingHom] using h4⟩
  · rintro ⟨⟨h1, h3⟩, h2, h4⟩
    exact ⟨⟨h1, by simpa only [mul_assoc, MonoidHom.coe_coe, RingHom.coe_coe, AlgHom.coe_toRingHom] using h2⟩, h3,
      by simpa only [mul_assoc, MonoidHom.coe_coe, RingHom.coe_coe, AlgHom.coe_toRingHom] using h4⟩

theorem one_mem_localBoxUnits {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    (1 : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) ∈ Submodule.localBoxUnits Λ v := by
  rw [mem_localBoxUnits_iff', inv_one, Units.val_one]
  exact ⟨one_mem_localBox hΛ v, one_mem_localBox hΛ v⟩

theorem mem_stabilizer_iff_forall {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (u : (ℍ𝔸)ˣ) :
    u ∈ Submodule.finiteIdeleStabilizer Λ ↔ ∀ v, (evU (a := a) (b := b) v) u ∈ Submodule.localBoxUnits Λ v :=
  IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits Λ hΛ u

private theorem _root_.CSTowerT21.Stab.eq_of_natCast_prime_mem {ℓ : ℕ} (hℓ : ℓ.Prime) {v w : HeightOneSpectrum (𝓞 ℚ)}
    (hv : ((ℓ : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) (hw : ((ℓ : ℕ) : 𝓞 ℚ) ∈ w.asIdeal) : v = w := by
  apply (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective
  apply Subtype.ext
  show Rat.HeightOneSpectrum.natGenerator v = Rat.HeightOneSpectrum.natGenerator w
  rw [← natGenerator_dvd_iff'] at hv hw
  rw [(Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator v) hℓ).mp hv,
    (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator w) hℓ).mp hw]

p2m_export "CSTowerT21.Stab" "eq_of_natCast_prime_mem"

theorem mem_stabilizer_tower_iff {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) {q ℓ : ℕ} (hq : q.Prime) (hℓ : ℓ.Prime)
    (hℓq : ℓ ≠ q) {n m n' : (ℍ𝔸)ˣ} (hn : n ∈ primeHeckeSet R q) (hm : m ∈ primeHeckeSet R ℓ)
    (hn' : n' ∈ primeHeckeSet (meetOrder R m) q) (hnn' : n⁻¹ * n' ∈ Submodule.finiteIdeleStabilizer R) (u : (ℍ𝔸)ˣ) :
    u ∈ Submodule.finiteIdeleStabilizer (meetOrder (meetOrder R m) n') ↔
      u ∈ Submodule.finiteIdeleStabilizer (meetOrder R n) ∧ u ∈ Submodule.finiteIdeleStabilizer (meetOrder R m) := by
  have hR' : IsOrder (meetOrder R m) := isOrder_meetOrder hR m
  have hS : IsOrder (meetOrder R n) := isOrder_meetOrder hR n
  have hS' : IsOrder (meetOrder (meetOrder R m) n') := isOrder_meetOrder hR' n'
  rw [mem_stabilizer_iff_forall hS', mem_stabilizer_iff_forall hS, mem_stabilizer_iff_forall hR', ← forall_and]
  refine forall_congr' fun v => ?_
  rw [mem_localBoxUnits_meetOrder_iff hR' n' v, mem_localBoxUnits_meetOrder_iff hR n v]
  by_cases hqv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal
  ·
    have hℓv := not_mem_of_prime_ne hq hℓ hℓq hqv
    have hmv := map_mem_localBoxUnits_of_mem_primeHeckeSet hℓ.ne_zero hm hℓv
    have hw := map_mem_localBoxUnits_of_mem_stabilizer hR hnn' v
    have hR'U : ∀ s, s ∈ Submodule.localBoxUnits (meetOrder R m) v ↔ s ∈ Submodule.localBoxUnits R v := fun s => by
      rw [mem_localBoxUnits_meetOrder_iff hR m v, conj_mem_localBoxUnits_iff hR v hmv, and_self]
    have e : (evU (a := a) (b := b) v) n' = (evU (a := a) (b := b) v) n * (evU (a := a) (b := b) v) (n⁻¹ * n') := by
      rw [← map_mul, mul_inv_cancel_left]
    have e2 : ((evU (a := a) (b := b) v) n')⁻¹ * (evU (a := a) (b := b) v) u * (evU (a := a) (b := b) v) n' =
        ((evU (a := a) (b := b) v) (n⁻¹ * n'))⁻¹ *
          (((evU (a := a) (b := b) v) n)⁻¹ * (evU (a := a) (b := b) v) u * (evU (a := a) (b := b) v) n) *
          (evU (a := a) (b := b) v) (n⁻¹ * n') := by
      rw [e]; group
    rw [hR'U, hR'U, e2, conj_mem_localBoxUnits_iff hR v hw]
    tauto
  ·
    have hnv := map_mem_localBoxUnits_of_mem_primeHeckeSet hq.ne_zero hn hqv
    have hn'v := map_mem_localBoxUnits_of_mem_primeHeckeSet hq.ne_zero hn' hqv
    have hsub : (evU (a := a) (b := b) v) u ∈ Submodule.localBoxUnits (meetOrder R m) v →
        (evU (a := a) (b := b) v) u ∈ Submodule.localBoxUnits R v := fun h =>
      ((mem_localBoxUnits_meetOrder_iff hR m v _).mp h).1
    rw [conj_mem_localBoxUnits_iff hR' v hn'v, conj_mem_localBoxUnits_iff hR v hnv]
    tauto

theorem exists_mem_stabilizer_meetOrder_inv_mul_mem {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) {q ℓ : ℕ}
    (hq : q.Prime) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) {n m : (ℍ𝔸)ˣ} (hn : n ∈ primeHeckeSet R q)
    (hm : m ∈ primeHeckeSet R ℓ) (u : (ℍ𝔸)ˣ) (hu : u ∈ Submodule.finiteIdeleStabilizer R) :
    ∃ k ∈ Submodule.finiteIdeleStabilizer (meetOrder R m), k⁻¹ * u ∈ Submodule.finiteIdeleStabilizer (meetOrder R n) := by
  classical
  have hR' : IsOrder (meetOrder R m) := isOrder_meetOrder hR m
  have hS : IsOrder (meetOrder R n) := isOrder_meetOrder hR n
  obtain ⟨vℓ, hvℓ⟩ := exists_place ℓ hℓ
  obtain ⟨β, hβ1, hβ2⟩ := Submodule.exists_units_finiteAdeleEvalAt_eq (D := ℍ[ℚ, a, b]) {vℓ}
    (fun v => ((evU (a := a) (b := b) v) u)⁻¹)
  have eβ : ∀ v, (evU (a := a) (b := b) v) β = if v = vℓ then ((evU (a := a) (b := b) v) u)⁻¹ else 1 := by
    intro v
    apply Units.ext
    by_cases hv : v = vℓ
    · rw [if_pos hv]; exact hβ1 v (by rw [Finset.mem_singleton]; exact hv)
    · rw [if_neg hv]; exact hβ2 v (by rw [Finset.mem_singleton]; exact hv)
  have huv : ∀ v, (evU (a := a) (b := b) v) u ∈ Submodule.localBoxUnits R v :=
    fun v => map_mem_localBoxUnits_of_mem_stabilizer hR hu v
  refine ⟨u * β, ?_, ?_⟩
  · rw [mem_stabilizer_iff_forall hR']
    intro v
    rw [mem_localBoxUnits_meetOrder_iff hR m v, map_mul, eβ v]
    by_cases hv : v = vℓ
    · rw [if_pos hv, mul_inv_cancel, mul_one, inv_mul_cancel]
      exact ⟨one_mem_localBoxUnits hR v, one_mem_localBoxUnits hR v⟩
    · rw [if_neg hv, mul_one]
      have hℓv : ((ℓ : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := fun h => hv (eq_of_natCast_prime_mem hℓ h hvℓ)
      have hmv := map_mem_localBoxUnits_of_mem_primeHeckeSet hℓ.ne_zero hm hℓv
      exact ⟨huv v, (conj_mem_localBoxUnits_iff hR v hmv _).mpr (huv v)⟩
  · have e : (u * β)⁻¹ * u = β⁻¹ := by group
    rw [e, mem_stabilizer_iff_forall hS]
    intro v
    rw [mem_localBoxUnits_meetOrder_iff hR n v, map_inv, eβ v]
    by_cases hv : v = vℓ
    · subst hv
      rw [if_pos rfl, inv_inv]
      have hqv : ((q : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := not_mem_of_prime_ne hℓ hq (Ne.symm hℓq) hvℓ
      have hnv := map_mem_localBoxUnits_of_mem_primeHeckeSet hq.ne_zero hn hqv
      exact ⟨huv v, (conj_mem_localBoxUnits_iff hR v hnv _).mpr (huv v)⟩
    · rw [if_neg hv, inv_one, mul_one, inv_mul_cancel]
      exact ⟨one_mem_localBoxUnits hR v, one_mem_localBoxUnits hR v⟩

theorem exists_mem_stabilizer_meetOrder_inv_mul_mem' {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) {q ℓ : ℕ}
    (hq : q.Prime) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) {n m : (ℍ𝔸)ˣ} (hn : n ∈ primeHeckeSet R q)
    (hm : m ∈ primeHeckeSet R ℓ) (u : (ℍ𝔸)ˣ) (hu : u ∈ Submodule.finiteIdeleStabilizer R) :
    ∃ k ∈ Submodule.finiteIdeleStabilizer (meetOrder R n), k⁻¹ * u ∈ Submodule.finiteIdeleStabilizer (meetOrder R m) := by
  obtain ⟨k, hk, hku⟩ := exists_mem_stabilizer_meetOrder_inv_mul_mem hR hq hℓ hℓq hn hm u⁻¹ (inv_mem hu)
  refine ⟨u * k, ?_, ?_⟩
  · have e : u * k = (k⁻¹ * u⁻¹)⁻¹ := by group
    rw [e]; exact inv_mem hku
  · have e : (u * k)⁻¹ * u = k⁻¹ := by group
    rw [e]; exact inv_mem hk

theorem mem_stabilizer_tower_iff_loc {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) {q ℓ : ℕ} (hq : q.Prime) (hℓ : ℓ.Prime)
    (hℓq : ℓ ≠ q) {n m n' : (ℍ𝔸)ˣ}
    (hn : ∀ v : HeightOneSpectrum (𝓞 ℚ), ((q : ℕ) : 𝓞 ℚ) ∉ v.asIdeal → (evU (a := a) (b := b) v) n ∈ Submodule.localBoxUnits R v)
    (hm : ∀ v : HeightOneSpectrum (𝓞 ℚ), ((ℓ : ℕ) : 𝓞 ℚ) ∉ v.asIdeal → (evU (a := a) (b := b) v) m ∈ Submodule.localBoxUnits R v)
    (hn' : ∀ v : HeightOneSpectrum (𝓞 ℚ), ((q : ℕ) : 𝓞 ℚ) ∉ v.asIdeal → (evU (a := a) (b := b) v) n' ∈ Submodule.localBoxUnits (meetOrder R m) v)
    (hnn' : n⁻¹ * n' ∈ Submodule.finiteIdeleStabilizer R) (u : (ℍ𝔸)ˣ) :
    u ∈ Submodule.finiteIdeleStabilizer (meetOrder (meetOrder R m) n') ↔
      u ∈ Submodule.finiteIdeleStabilizer (meetOrder R n) ∧ u ∈ Submodule.finiteIdeleStabilizer (meetOrder R m) := by
  have hR' : IsOrder (meetOrder R m) := isOrder_meetOrder hR m
  have hS : IsOrder (meetOrder R n) := isOrder_meetOrder hR n
  have hS' : IsOrder (meetOrder (meetOrder R m) n') := isOrder_meetOrder hR' n'
  rw [mem_stabilizer_iff_forall hS', mem_stabilizer_iff_forall hS, mem_stabilizer_iff_forall hR', ← forall_and]
  refine forall_congr' fun v => ?_
  rw [mem_localBoxUnits_meetOrder_iff hR' n' v, mem_localBoxUnits_meetOrder_iff hR n v]
  by_cases hqv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal
  ·
    have hℓv := not_mem_of_prime_ne hq hℓ hℓq hqv
    have hmv := hm v hℓv
    have hw := map_mem_localBoxUnits_of_mem_stabilizer hR hnn' v
    have hR'U : ∀ s, s ∈ Submodule.localBoxUnits (meetOrder R m) v ↔ s ∈ Submodule.localBoxUnits R v := fun s => by
      rw [mem_localBoxUnits_meetOrder_iff hR m v, conj_mem_localBoxUnits_iff hR v hmv, and_self]
    have e : (evU (a := a) (b := b) v) n' = (evU (a := a) (b := b) v) n * (evU (a := a) (b := b) v) (n⁻¹ * n') := by
      rw [← map_mul, mul_inv_cancel_left]
    have e2 : ((evU (a := a) (b := b) v) n')⁻¹ * (evU (a := a) (b := b) v) u * (evU (a := a) (b := b) v) n' =
        ((evU (a := a) (b := b) v) (n⁻¹ * n'))⁻¹ *
          (((evU (a := a) (b := b) v) n)⁻¹ * (evU (a := a) (b := b) v) u * (evU (a := a) (b := b) v) n) *
          (evU (a := a) (b := b) v) (n⁻¹ * n') := by
      rw [e]; group
    rw [hR'U, hR'U, e2, conj_mem_localBoxUnits_iff hR v hw]
    tauto
  ·
    have hnv := hn v hqv
    have hn'v := hn' v hqv
    have hsub : (evU (a := a) (b := b) v) u ∈ Submodule.localBoxUnits (meetOrder R m) v →
        (evU (a := a) (b := b) v) u ∈ Submodule.localBoxUnits R v := fun h =>
      ((mem_localBoxUnits_meetOrder_iff hR m v _).mp h).1
    rw [conj_mem_localBoxUnits_iff hR' v hn'v, conj_mem_localBoxUnits_iff hR v hnv]
    tauto

theorem exists_mem_stabilizer_meetOrder_inv_mul_mem_loc {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) {q ℓ : ℕ}
    (hq : q.Prime) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) {n m : (ℍ𝔸)ˣ}
    (hn : ∀ v : HeightOneSpectrum (𝓞 ℚ), ((q : ℕ) : 𝓞 ℚ) ∉ v.asIdeal → (evU (a := a) (b := b) v) n ∈ Submodule.localBoxUnits R v)
    (hm : ∀ v : HeightOneSpectrum (𝓞 ℚ), ((ℓ : ℕ) : 𝓞 ℚ) ∉ v.asIdeal → (evU (a := a) (b := b) v) m ∈ Submodule.localBoxUnits R v)
    (u : (ℍ𝔸)ˣ) (hu : u ∈ Submodule.finiteIdeleStabilizer R) :
    ∃ k ∈ Submodule.finiteIdeleStabilizer (meetOrder R m), k⁻¹ * u ∈ Submodule.finiteIdeleStabilizer (meetOrder R n) := by
  classical
  have hR' : IsOrder (meetOrder R m) := isOrder_meetOrder hR m
  have hS : IsOrder (meetOrder R n) := isOrder_meetOrder hR n
  obtain ⟨vℓ, hvℓ⟩ := exists_place ℓ hℓ
  obtain ⟨β, hβ1, hβ2⟩ := Submodule.exists_units_finiteAdeleEvalAt_eq (D := ℍ[ℚ, a, b]) {vℓ}
    (fun v => ((evU (a := a) (b := b) v) u)⁻¹)
  have eβ : ∀ v, (evU (a := a) (b := b) v) β = if v = vℓ then ((evU (a := a) (b := b) v) u)⁻¹ else 1 := by
    intro v
    apply Units.ext
    by_cases hv : v = vℓ
    · rw [if_pos hv]; exact hβ1 v (by rw [Finset.mem_singleton]; exact hv)
    · rw [if_neg hv]; exact hβ2 v (by rw [Finset.mem_singleton]; exact hv)
  have huv : ∀ v, (evU (a := a) (b := b) v) u ∈ Submodule.localBoxUnits R v :=
    fun v => map_mem_localBoxUnits_of_mem_stabilizer hR hu v
  refine ⟨u * β, ?_, ?_⟩
  · rw [mem_stabilizer_iff_forall hR']
    intro v
    rw [mem_localBoxUnits_meetOrder_iff hR m v, map_mul, eβ v]
    by_cases hv : v = vℓ
    · rw [if_pos hv, mul_inv_cancel, mul_one, inv_mul_cancel]
      exact ⟨one_mem_localBoxUnits hR v, one_mem_localBoxUnits hR v⟩
    · rw [if_neg hv, mul_one]
      have hℓv : ((ℓ : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := fun h => hv (eq_of_natCast_prime_mem hℓ h hvℓ)
      have hmv := hm v hℓv
      exact ⟨huv v, (conj_mem_localBoxUnits_iff hR v hmv _).mpr (huv v)⟩
  · have e : (u * β)⁻¹ * u = β⁻¹ := by group
    rw [e, mem_stabilizer_iff_forall hS]
    intro v
    rw [mem_localBoxUnits_meetOrder_iff hR n v, map_inv, eβ v]
    by_cases hv : v = vℓ
    · subst hv
      rw [if_pos rfl, inv_inv]
      have hqv : ((q : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := not_mem_of_prime_ne hℓ hq (Ne.symm hℓq) hvℓ
      have hnv := hn v hqv
      exact ⟨huv v, (conj_mem_localBoxUnits_iff hR v hnv _).mpr (huv v)⟩
    · rw [if_neg hv, inv_one, mul_one, inv_mul_cancel]
      exact ⟨one_mem_localBoxUnits hR v, one_mem_localBoxUnits hR v⟩

theorem inv_mem_localBoxUnits {Λ : Submodule ℤ ℍ[ℚ, a, b]} {v : HeightOneSpectrum (𝓞 ℚ)}
    {t : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ} (ht : t ∈ Submodule.localBoxUnits Λ v) :
    t⁻¹ ∈ Submodule.localBoxUnits Λ v := by
  rw [mem_localBoxUnits_iff'] at ht ⊢
  rw [inv_inv]
  exact ⟨ht.2, ht.1⟩

theorem loc_n {R : Submodule ℤ ℍ[ℚ, a, b]} {q : ℕ} (hq : q.Prime) {n : (ℍ𝔸)ˣ} (hn : n ∈ primeHeckeSet R q) :
    ∀ v : HeightOneSpectrum (𝓞 ℚ), ((q : ℕ) : 𝓞 ℚ) ∉ v.asIdeal →
      (evU (a := a) (b := b) v) n ∈ Submodule.localBoxUnits R v :=
  fun _ hv => map_mem_localBoxUnits_of_mem_primeHeckeSet hq.ne_zero hn hv

theorem loc_s {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) {ℓ : ℕ} (hℓ : ℓ.Prime) {n s : (ℍ𝔸)ˣ} (hsS : s ∈ primeHeckeSet (meetOrder R n) ℓ) :
    ∀ v : HeightOneSpectrum (𝓞 ℚ), ((ℓ : ℕ) : 𝓞 ℚ) ∉ v.asIdeal →
      (evU (a := a) (b := b) v) s ∈ Submodule.localBoxUnits R v :=
  fun v hv => ((mem_localBoxUnits_meetOrder_iff hR n v _).mp (map_mem_localBoxUnits_of_mem_primeHeckeSet hℓ.ne_zero hsS hv)).1

theorem loc_s_inv {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) {ℓ : ℕ} (hℓ : ℓ.Prime) {n s : (ℍ𝔸)ˣ} (hsS : s ∈ primeHeckeSet (meetOrder R n) ℓ) :
    ∀ v : HeightOneSpectrum (𝓞 ℚ), ((ℓ : ℕ) : 𝓞 ℚ) ∉ v.asIdeal →
      (evU (a := a) (b := b) v) s⁻¹ ∈ Submodule.localBoxUnits R v :=
  fun v hv => by rw [map_inv]; exact inv_mem_localBoxUnits (loc_s hR hℓ hsS v hv)

theorem loc_n'_inv {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) {q : ℕ} (hq : q.Prime) {s n' : (ℍ𝔸)ˣ} (hn' : n' ∈ primeHeckeSet (meetOrder R s) q)
    (hsn' : s * n' = n' * s) :
    ∀ v : HeightOneSpectrum (𝓞 ℚ), ((q : ℕ) : 𝓞 ℚ) ∉ v.asIdeal →
      (evU (a := a) (b := b) v) n' ∈ Submodule.localBoxUnits (meetOrder R s⁻¹) v := by
  intro v hv
  have h := (mem_localBoxUnits_meetOrder_iff hR s v _).mp (loc_n hq hn' v hv)
  rw [mem_localBoxUnits_meetOrder_iff hR s⁻¹ v, map_inv, inv_inv]
  refine ⟨h.1, ?_⟩
  have e : (evU (a := a) (b := b) v) s * (evU (a := a) (b := b) v) n' * ((evU (a := a) (b := b) v) s)⁻¹ =
      (evU (a := a) (b := b) v) n' := by
    rw [← map_mul, hsn', map_mul, mul_inv_cancel_right]
  rw [e]; exact h.1

theorem F1_iff {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) {q ℓ : ℕ} (hq : q.Prime) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) {n s n' : (ℍ𝔸)ˣ} (hn : n ∈ primeHeckeSet R q)
    (hsS : s ∈ primeHeckeSet (meetOrder R n) ℓ) (hn' : n' ∈ primeHeckeSet (meetOrder R s) q)
    (hnn' : n⁻¹ * n' ∈ Submodule.finiteIdeleStabilizer R) (u : (ℍ𝔸)ˣ) :
    u ∈ Submodule.finiteIdeleStabilizer (meetOrder (meetOrder R s) n') ↔
      u ∈ Submodule.finiteIdeleStabilizer (meetOrder R n) ∧ u ∈ Submodule.finiteIdeleStabilizer (meetOrder R s) :=
  mem_stabilizer_tower_iff_loc hR hq hℓ hℓq (loc_n hq hn) (loc_s hR hℓ hsS) (fun v hv => loc_n hq hn' v hv) hnn' u

theorem F1 {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) {q ℓ : ℕ} (hq : q.Prime) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) {n s n' : (ℍ𝔸)ˣ} (hn : n ∈ primeHeckeSet R q)
    (hsS : s ∈ primeHeckeSet (meetOrder R n) ℓ) (hn' : n' ∈ primeHeckeSet (meetOrder R s) q)
    (hnn' : n⁻¹ * n' ∈ Submodule.finiteIdeleStabilizer R) :
    Submodule.finiteIdeleStabilizer (meetOrder R n) ⊓ Submodule.finiteIdeleStabilizer (meetOrder R s) ≤
      Submodule.finiteIdeleStabilizer (meetOrder (meetOrder R s) n') :=
  fun u hu => (F1_iff hR hq hℓ hℓq hn hsS hn' hnn' u).mpr hu

theorem F2_loc {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) {q ℓ : ℕ} (hq : q.Prime) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) {n m : (ℍ𝔸)ˣ} (hn : n ∈ primeHeckeSet R q)
    (hm : ∀ v : HeightOneSpectrum (𝓞 ℚ), ((ℓ : ℕ) : 𝓞 ℚ) ∉ v.asIdeal → (evU (a := a) (b := b) v) m ∈ Submodule.localBoxUnits R v) :
    ∀ k : ↥(Submodule.finiteIdeleStabilizer R), ∃ k₁ : ↥(Submodule.finiteIdeleStabilizer (meetOrder R n)),
      ((k₁ : (ℍ𝔸)ˣ)⁻¹ * k) ∈ Submodule.finiteIdeleStabilizer (meetOrder R m) := by
  intro k
  obtain ⟨k₀, hk₀, hk₀u⟩ := exists_mem_stabilizer_meetOrder_inv_mul_mem_loc hR hq hℓ hℓq (loc_n hq hn) hm
    (k : (ℍ𝔸)ˣ)⁻¹ (inv_mem k.2)
  refine ⟨⟨(k : (ℍ𝔸)ˣ) * k₀, ?_⟩, ?_⟩
  · have e : (k : (ℍ𝔸)ˣ) * k₀ = (k₀⁻¹ * (k : (ℍ𝔸)ˣ)⁻¹)⁻¹ := by group
    rw [e]; exact inv_mem hk₀u
  · have e : ((k : (ℍ𝔸)ˣ) * k₀)⁻¹ * (k : (ℍ𝔸)ˣ) = k₀⁻¹ := by group
    show ((k : (ℍ𝔸)ˣ) * k₀)⁻¹ * (k : (ℍ𝔸)ˣ) ∈ _
    rw [e]; exact inv_mem hk₀

theorem F2 {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) {q ℓ : ℕ} (hq : q.Prime) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) {n s : (ℍ𝔸)ˣ} (hn : n ∈ primeHeckeSet R q)
    (hsS : s ∈ primeHeckeSet (meetOrder R n) ℓ) :
    ∀ k : ↥(Submodule.finiteIdeleStabilizer R), ∃ k₁ : ↥(Submodule.finiteIdeleStabilizer (meetOrder R n)),
      ((k₁ : (ℍ𝔸)ˣ)⁻¹ * k) ∈ Submodule.finiteIdeleStabilizer (meetOrder R s) :=
  F2_loc hR hq hℓ hℓq hn (loc_s hR hℓ hsS)

theorem map_conj_stabilizer_meetOrder_inv {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) (s : (ℍ𝔸)ˣ) :
    (Submodule.finiteIdeleStabilizer (meetOrder R s⁻¹)).map (MulAut.conj s).toMonoidHom =
      Submodule.finiteIdeleStabilizer (meetOrder R s) := by
  ext u
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, mem_finiteIdeleStabilizer_meetOrder_iff hR,
    mem_finiteIdeleStabilizer_meetOrder_iff hR, inv_inv]
  have e : s * (s⁻¹ * u * s) * s⁻¹ = u := by group
  rw [e, and_comm]

theorem map_conj_stabilizer_meetOrder_meetOrder_inv {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) {s n' : (ℍ𝔸)ˣ} (hsn' : s * n' = n' * s) :
    (Submodule.finiteIdeleStabilizer (meetOrder (meetOrder R s⁻¹) n')).map (MulAut.conj s).toMonoidHom =
      Submodule.finiteIdeleStabilizer (meetOrder (meetOrder R s) n') := by
  ext u
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply,
    mem_finiteIdeleStabilizer_meetOrder_iff (isOrder_meetOrder hR s⁻¹),
    mem_finiteIdeleStabilizer_meetOrder_iff (isOrder_meetOrder hR s),
    mem_finiteIdeleStabilizer_meetOrder_iff hR, mem_finiteIdeleStabilizer_meetOrder_iff hR,
    mem_finiteIdeleStabilizer_meetOrder_iff hR, mem_finiteIdeleStabilizer_meetOrder_iff hR, inv_inv]
  have hc : n'⁻¹ * s⁻¹ = s⁻¹ * n'⁻¹ := by rw [← mul_inv_rev, ← mul_inv_rev, hsn']
  have e1 : s * (s⁻¹ * u * s) * s⁻¹ = u := by group
  have e2 : n'⁻¹ * (s⁻¹ * u * s) * n' = s⁻¹ * (n'⁻¹ * u * n') * s := by
    calc n'⁻¹ * (s⁻¹ * u * s) * n' = (n'⁻¹ * s⁻¹) * u * (s * n') := by group
      _ = (s⁻¹ * n'⁻¹) * u * (n' * s) := by rw [hc, hsn']
      _ = s⁻¹ * (n'⁻¹ * u * n') * s := by group
  have e3 : s * (s⁻¹ * (n'⁻¹ * u * n') * s) * s⁻¹ = n'⁻¹ * u * n' := by group
  rw [e1, e2, e3]
  tauto

theorem F1s {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) {q ℓ : ℕ} (hq : q.Prime) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) {n s n' : (ℍ𝔸)ˣ} (hn : n ∈ primeHeckeSet R q)
    (hsS : s ∈ primeHeckeSet (meetOrder R n) ℓ) (hn' : n' ∈ primeHeckeSet (meetOrder R s) q)
    (hnn' : n⁻¹ * n' ∈ Submodule.finiteIdeleStabilizer R) (hsn' : s * n' = n' * s) :
    (Submodule.finiteIdeleStabilizer (meetOrder R n)).map (MulAut.conj s).toMonoidHom ⊓
      Submodule.finiteIdeleStabilizer (meetOrder R s) ≤ Submodule.finiteIdeleStabilizer (meetOrder (meetOrder R s) n') := by
  rw [← map_conj_stabilizer_meetOrder_inv hR s, ← map_conj_stabilizer_meetOrder_meetOrder_inv hR hsn',
    ← Subgroup.map_inf _ _ _ (MulAut.conj s).injective]
  exact Subgroup.map_mono (fun u hu =>
    (mem_stabilizer_tower_iff_loc hR hq hℓ hℓq (loc_n hq hn) (loc_s_inv hR hℓ hsS) (loc_n'_inv hR hq hn' hsn') hnn' u).mpr hu)

theorem F2s {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) {q ℓ : ℕ} (hq : q.Prime) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) {n s : (ℍ𝔸)ˣ} (hn : n ∈ primeHeckeSet R q)
    (hsS : s ∈ primeHeckeSet (meetOrder R n) ℓ) :
    ∀ k : ↥((Submodule.finiteIdeleStabilizer R).map (MulAut.conj s).toMonoidHom),
      ∃ k₁ : ↥((Submodule.finiteIdeleStabilizer (meetOrder R n)).map (MulAut.conj s).toMonoidHom),
        ((k₁ : (ℍ𝔸)ˣ)⁻¹ * k) ∈ Submodule.finiteIdeleStabilizer (meetOrder R s) := by
  intro k
  have hk : s⁻¹ * (k : (ℍ𝔸)ˣ) * s ∈ Submodule.finiteIdeleStabilizer R := by
    have h2 := k.2
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply] at h2
    exact h2
  obtain ⟨k₁, hk₁⟩ := F2_loc hR hq hℓ hℓq hn (loc_s_inv hR hℓ hsS) ⟨_, hk⟩
  refine ⟨⟨s * (k₁ : (ℍ𝔸)ˣ) * s⁻¹, ?_⟩, ?_⟩
  · rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    have e : s⁻¹ * (s * (k₁ : (ℍ𝔸)ˣ) * s⁻¹) * s = k₁ := by group
    rw [e]; exact k₁.2
  · show (s * (k₁ : (ℍ𝔸)ˣ) * s⁻¹)⁻¹ * (k : (ℍ𝔸)ˣ) ∈ _
    rw [← map_conj_stabilizer_meetOrder_inv hR s, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    have e : s⁻¹ * ((s * (k₁ : (ℍ𝔸)ˣ) * s⁻¹)⁻¹ * (k : (ℍ𝔸)ˣ)) * s = (k₁ : (ℍ𝔸)ˣ)⁻¹ * (s⁻¹ * (k : (ℍ𝔸)ˣ) * s) := by group
    rw [e]; exact hk₁

theorem inv_mul_mem_stabilizer_meetOrder {R : Submodule ℤ ℍ[ℚ, a, b]} {N N' : ℕ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    (hqq' : q' ≠ q) (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (hRE : IsEichlerOrder R N) (hqN : ¬ q ∣ N) {n s n' : (ℍ𝔸)ˣ} (hn : n ∈ primeHeckeSet R q)
    (hS : IsEichlerOrder (meetOrder R n) (N * q)) (hnorm : Submodule.conjByFiniteIdele (meetOrder R n) n = meetOrder R n)
    (hR'E : IsEichlerOrder (meetOrder R s) N') (hqN' : ¬ q ∣ N') (hn' : n' ∈ primeHeckeSet (meetOrder R s) q)
    (hS' : IsEichlerOrder (meetOrder (meetOrder R s) n') (N' * q))
    (hnorm' : Submodule.conjByFiniteIdele (meetOrder (meetOrder R s) n') n' = meetOrder (meetOrder R s) n')
    (hnn' : n⁻¹ * n' ∈ Submodule.finiteIdeleStabilizer R) :
    n⁻¹ * n' ∈ Submodule.finiteIdeleStabilizer (meetOrder R n) := by
  have hR : IsOrder R := hRE.isOrder
  obtain ⟨u₀, hu₀, he⟩ := (CerednikDrinfeld.exists_mul_self_eq_finiteIdeleDiagonal_mul_and_mem_finiteIdeleStabilizer_meetOrder_of_conjByFiniteIdele_mul_eq
    R q n hRE hqN hqq' hdef hn hS hnorm).1
  obtain ⟨u₀', hu₀', he'⟩ := (CerednikDrinfeld.exists_mul_self_eq_finiteIdeleDiagonal_mul_and_mem_finiteIdeleStabilizer_meetOrder_of_conjByFiniteIdele_mul_eq
    (meetOrder R s) q n' hR'E hqN' hqq' hdef hn' hS' hnorm').1
  rw [mem_finiteIdeleStabilizer_meetOrder_iff hR]
  refine ⟨hnn', ?_⟩
  have hu₀R : u₀ ∈ Submodule.finiteIdeleStabilizer R := ((mem_finiteIdeleStabilizer_meetOrder_iff hR n u₀).mp hu₀).1
  have hu₀'R : u₀' ∈ Submodule.finiteIdeleStabilizer R :=
    ((mem_finiteIdeleStabilizer_meetOrder_iff hR s u₀').mp
      ((mem_finiteIdeleStabilizer_meetOrder_iff (isOrder_meetOrder hR s) n' u₀').mp hu₀').1).1
  have key : n⁻¹ * (n⁻¹ * n') * n = u₀⁻¹ * u₀' * (n⁻¹ * n')⁻¹ := by
    calc n⁻¹ * (n⁻¹ * n') * n = (n * n)⁻¹ * (n' * n') * (n⁻¹ * n')⁻¹ := by group
      _ = _ := by rw [he, he']; group
  rw [key]
  exact mul_mem (mul_mem (inv_mem hu₀R) hu₀'R) (inv_mem hnn')

end CSTowerT21.Stab
p2m_reactivate "P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.DoubleCosetFibre P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.CSTower P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.CSTowerT21"
p2m_reactivate "P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.DoubleCosetFibre P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.CSTower P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.CSTowerT21"

namespace CSTowerT21
namespace Nat

noncomputable def placesOf (ℓ : ℕ) : Finset (HeightOneSpectrum (𝓞 ℚ)) :=
  if h : (Ideal.span {(ℓ : 𝓞 ℚ)} : Ideal (𝓞 ℚ)) = ⊥ then ∅ else (Ideal.finite_factors h).toFinset

theorem span_natCast_ne_bot {ℓ : ℕ} (hℓ : ℓ ≠ 0) : (Ideal.span {(ℓ : 𝓞 ℚ)} : Ideal (𝓞 ℚ)) ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact_mod_cast hℓ

theorem mem_placesOf_iff {ℓ : ℕ} (hℓ : ℓ ≠ 0) (v : HeightOneSpectrum (𝓞 ℚ)) :
    v ∈ placesOf ℓ ↔ (ℓ : 𝓞 ℚ) ∈ v.asIdeal := by
  rw [placesOf, dif_neg (span_natCast_ne_bot hℓ), Set.Finite.mem_toFinset, Set.mem_setOf_eq,
    Ideal.dvd_span_singleton]

theorem inv_natCast_mem_adicCompletionIntegers_of_not_mem_placesOf {ℓ : ℕ} (hℓ : ℓ ≠ 0)
    {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ∉ placesOf ℓ) :
    algebraMap ℚ (v.adicCompletion ℚ) ((ℓ : ℚ)⁻¹) ∈ v.adicCompletionIntegers ℚ := by
  rw [mem_placesOf_iff hℓ] at hv
  rw [HeightOneSpectrum.mem_adicCompletionIntegers,
    show Valued.v (algebraMap ℚ (v.adicCompletion ℚ) ((ℓ : ℚ)⁻¹)) = v.valuation ℚ ((ℓ : ℚ)⁻¹) from
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _, map_inv₀]
  have h1 : v.valuation ℚ (ℓ : ℚ) = 1 := by
    have : (ℓ : ℚ) = algebraMap (𝓞 ℚ) ℚ (ℓ : 𝓞 ℚ) := by simp
    rw [this, HeightOneSpectrum.valuation_of_algebraMap]
    have hle := v.intValuation_le_one (ℓ : 𝓞 ℚ)
    have hnlt : ¬ v.intValuation (ℓ : 𝓞 ℚ) < 1 := by
      rw [HeightOneSpectrum.intValuation_lt_one_iff_mem]
      exact hv
    exact le_antisymm hle (not_lt.mp hnlt)
  rw [h1, inv_one]

theorem disjoint_placesOf_of_coprime {ℓ ℓ' : ℕ} (hℓ : ℓ ≠ 0) (hℓ' : ℓ' ≠ 0) (h : ℓ.Coprime ℓ') :
    Disjoint (placesOf ℓ) (placesOf ℓ') := by
  rw [Finset.disjoint_left]
  intro v hv hv'
  rw [mem_placesOf_iff hℓ] at hv
  rw [mem_placesOf_iff hℓ'] at hv'
  have hcop : IsCoprime (ℓ : 𝓞 ℚ) (ℓ' : 𝓞 ℚ) := by
    have := (Nat.isCoprime_iff_coprime.mpr h : IsCoprime (ℓ : ℤ) (ℓ' : ℤ))
    simpa using this.map (Int.castRingHom (𝓞 ℚ))
  obtain ⟨x, y, hxy⟩ := hcop
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hxy]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hv) (Ideal.mul_mem_left _ _ hv')

theorem not_mem_placesOf_of_mem_placesOf_of_coprime {ℓ ℓ' : ℕ} (hℓ : ℓ ≠ 0) (hℓ' : ℓ' ≠ 0) (h : ℓ.Coprime ℓ')
    {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ∈ placesOf ℓ) : v ∉ placesOf ℓ' :=
  Finset.disjoint_left.mp (disjoint_placesOf_of_coprime hℓ hℓ' h) hv

theorem isMaximal_span_natCast_of_prime {p : ℕ} (hp : p.Prime) :
    (Ideal.span {(p : 𝓞 ℚ)} : Ideal (𝓞 ℚ)).IsMaximal := by
  have e : 𝓞 ℚ ≃+* ℤ := Rat.ringOfIntegersEquiv
  have hpZ : _root_.Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpO : _root_.Prime (p : 𝓞 ℚ) := by
    have : (p : 𝓞 ℚ) = e.symm (p : ℤ) := by rw [map_natCast]
    rw [this]
    exact (MulEquiv.prime_iff (e.symm : ℤ ≃* 𝓞 ℚ)).mpr hpZ
  have hprime : (Ideal.span {(p : 𝓞 ℚ)} : Ideal (𝓞 ℚ)).IsPrime := (Ideal.span_singleton_prime hpO.ne_zero).mpr hpO
  exact hprime.isMaximal (span_natCast_ne_bot hp.ne_zero)

theorem HeightOneSpectrum.eq_of_natCast_prime_mem {p : ℕ} (hp : p.Prime) {v v' : HeightOneSpectrum (𝓞 ℚ)}
    (hv : (p : 𝓞 ℚ) ∈ v.asIdeal) (hv' : (p : 𝓞 ℚ) ∈ v'.asIdeal) : v = v' := by
  have hmax := isMaximal_span_natCast_of_prime hp
  have h1 : v.asIdeal = Ideal.span {(p : 𝓞 ℚ)} :=
    (hmax.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).mpr hv)).symm
  have h2 : v'.asIdeal = Ideal.span {(p : 𝓞 ℚ)} :=
    (hmax.eq_of_le v'.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).mpr hv')).symm
  exact HeightOneSpectrum.ext (h1.trans h2.symm)

end CSTowerT21.Nat
p2m_reactivate "P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.DoubleCosetFibre P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.CSTower P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.CSTowerT21"
p2m_reactivate "P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.DoubleCosetFibre P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.CSTower P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.CSTowerT21"

namespace CSTowerT21
namespace HL

variable {a b : ℚ}

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "ℍ𝔸" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ

def boxGen (Λ : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ𝔸 :=
  {x | ∃ z ∈ Λ, ∃ c : FiniteAdeleRing (𝓞 ℚ) ℚ,
      (∀ v : HeightOneSpectrum (𝓞 ℚ), c v ∈ v.adicCompletionIntegers ℚ) ∧ x = z ⊗ₜ[ℚ] c}

theorem box_eq_span (Λ : Submodule ℤ ℍ[ℚ, a, b]) :
    Submodule.finiteAdeleBox Λ = (Submodule.span ℤ (boxGen Λ)).toAddSubgroup := by
  rw [Submodule.span_int_eq_addSubgroupClosure]; rfl

theorem mem_box_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} {x : ℍ𝔸} :
    x ∈ Submodule.finiteAdeleBox Λ ↔ x ∈ Submodule.span ℤ (boxGen Λ) := by
  rw [box_eq_span]; rfl

theorem box_mul_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    {x y : ℍ𝔸} (hx : x ∈ Submodule.finiteAdeleBox Λ) (hy : y ∈ Submodule.finiteAdeleBox Λ) :
    x * y ∈ Submodule.finiteAdeleBox Λ := by
  rw [mem_box_iff] at hx hy ⊢
  induction hy using Submodule.span_induction with
  | mem y hy' =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hy'
    induction hx using Submodule.span_induction with
    | mem x hx' =>
      obtain ⟨z', hz', c', hc', rfl⟩ := hx'
      refine Submodule.subset_span ⟨z' * z, hΛ.mul_mem hz' hz, c' * c, fun v => ?_, ?_⟩
      · have e : (c' * c) v = c' v * c v := rfl
        rw [e]
        exact mul_mem (hc' v) (hc v)
      · rw [Algebra.TensorProduct.tmul_mul_tmul]
    | zero => rw [zero_mul]; exact zero_mem _
    | add x₁ x₂ _ _ h₁ h₂ => rw [add_mul]; exact add_mem h₁ h₂
    | smul m x₁ _ h₁ => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ h₁
  | zero => rw [mul_zero]; exact zero_mem _
  | add y₁ y₂ _ _ h₁ h₂ => rw [mul_add]; exact add_mem h₁ h₂
  | smul m y₁ _ h₁ => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h₁

theorem one_mem_box {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) :
    (1 : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ := by
  unfold Submodule.finiteAdeleBox
  refine AddSubgroup.subset_closure ⟨1, hΛ.one_mem, 1, fun v => ?_, ?_⟩
  · have e : (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) v = 1 := rfl
    rw [e]; exact one_mem _
  · rfl

theorem coe_mem_box_of_mem_stabilizer {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    {u : (ℍ𝔸)ˣ} (hu : u ∈ Submodule.finiteIdeleStabilizer Λ) :
    (u : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ := by
  have h := (Submodule.mem_finiteIdeleStabilizer_iff Λ u).mp hu

  have h1 : (u : ℍ𝔸) * 1 ∈ u • ((Submodule.finiteAdeleBox Λ : AddSubgroup ℍ𝔸) : Set ℍ𝔸) :=
    Set.smul_mem_smul_set (one_mem_box hΛ)
  rw [h, mul_one] at h1
  exact h1

theorem coe_inv_mem_box_of_mem_stabilizer {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    {u : (ℍ𝔸)ˣ} (hu : u ∈ Submodule.finiteIdeleStabilizer Λ) :
    ((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ :=
  coe_mem_box_of_mem_stabilizer hΛ (inv_mem hu)

theorem mul_mem_primeHeckeSet_of_mem_stabilizer {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    (ℓ : ℕ) {u h : (ℍ𝔸)ˣ} (hu : u ∈ Submodule.finiteIdeleStabilizer Λ) (hh : h ∈ QuaternionAlgebra.primeHeckeSet Λ ℓ) :
    u * h ∈ QuaternionAlgebra.primeHeckeSet Λ ℓ := by
  obtain ⟨h1, h2, h3, h4⟩ := hh
  have hub := coe_mem_box_of_mem_stabilizer hΛ hu
  have huib := coe_inv_mem_box_of_mem_stabilizer hΛ hu
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Units.val_mul]; exact box_mul_mem hΛ hub h1
  · rw [mul_inv_rev, Units.val_mul, ← smul_mul_assoc]
    exact box_mul_mem hΛ h2 huib
  · intro hmem
    apply h3
    have : ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) = (((u * h)⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * (u : ℍ𝔸) := by
      rw [mul_inv_rev, Units.val_mul, mul_assoc, Units.inv_mul, mul_one]
    rw [this]; exact box_mul_mem hΛ hmem hub
  · intro hmem
    apply h4
    have : (ℓ : ℚ)⁻¹ • (h : ℍ𝔸) = ((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * ((ℓ : ℚ)⁻¹ • ((u * h : (ℍ𝔸)ˣ) : ℍ𝔸)) := by
      rw [mul_smul_comm, Units.val_mul, ← mul_assoc, Units.inv_mul, one_mul]
    rw [this]; exact box_mul_mem hΛ huib hmem

theorem mul_mem_primeHeckeSet_of_mem_stabilizer' {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    (ℓ : ℕ) {u h : (ℍ𝔸)ˣ} (hu : u ∈ Submodule.finiteIdeleStabilizer Λ) (hh : h ∈ QuaternionAlgebra.primeHeckeSet Λ ℓ) :
    h * u ∈ QuaternionAlgebra.primeHeckeSet Λ ℓ := by
  obtain ⟨h1, h2, h3, h4⟩ := hh
  have hub := coe_mem_box_of_mem_stabilizer hΛ hu
  have huib := coe_inv_mem_box_of_mem_stabilizer hΛ hu
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Units.val_mul]; exact box_mul_mem hΛ h1 hub
  · rw [mul_inv_rev, Units.val_mul, ← mul_smul_comm]
    exact box_mul_mem hΛ huib h2
  · intro hmem
    apply h3
    have : ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) = (u : ℍ𝔸) * (((h * u)⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) := by
      rw [mul_inv_rev, Units.val_mul, ← mul_assoc, Units.mul_inv, one_mul]
    rw [this]; exact box_mul_mem hΛ hub hmem
  · intro hmem
    apply h4
    have : (ℓ : ℚ)⁻¹ • (h : ℍ𝔸) = ((ℓ : ℚ)⁻¹ • ((h * u : (ℍ𝔸)ˣ) : ℍ𝔸)) * ((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) := by
      rw [smul_mul_assoc, Units.val_mul, mul_assoc, Units.mul_inv, mul_one]
    rw [this]; exact box_mul_mem hΛ hmem huib

theorem box_mono {Λ Λ' : Submodule ℤ ℍ[ℚ, a, b]} (h : Λ ≤ Λ') :
    Submodule.finiteAdeleBox Λ ≤ Submodule.finiteAdeleBox Λ' := by
  unfold Submodule.finiteAdeleBox
  refine AddSubgroup.closure_mono ?_
  rintro x ⟨z, hz, c, hc, rfl⟩
  exact ⟨z, h hz, c, hc, rfl⟩

theorem mem_stabilizer_of_coe_mem_of_coe_inv_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    {u : (ℍ𝔸)ˣ} (hu : (u : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ) (hui : ((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ) :
    u ∈ Submodule.finiteIdeleStabilizer Λ := by
  rw [Submodule.mem_finiteIdeleStabilizer_iff]
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact box_mul_mem hΛ hu hx
  · intro x hx
    refine ⟨(u⁻¹ : (ℍ𝔸)ˣ) • x, box_mul_mem hΛ hui hx, ?_⟩
    show (u : ℍ𝔸) * (((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * x) = x
    rw [← mul_assoc, Units.mul_inv, one_mul]

theorem stabilizer_mono {S R : Submodule ℤ ℍ[ℚ, a, b]} (hS : QuaternionAlgebra.IsOrder S) (hR : QuaternionAlgebra.IsOrder R)
    (h : S ≤ R) : Submodule.finiteIdeleStabilizer S ≤ Submodule.finiteIdeleStabilizer R := by
  intro u hu
  exact mem_stabilizer_of_coe_mem_of_coe_inv_mem hR (box_mono h (coe_mem_box_of_mem_stabilizer hS hu))
    (box_mono h (coe_inv_mem_box_of_mem_stabilizer hS hu))

private theorem _root_.CSTowerT21.HL.mem_stabilizer_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (u : (ℍ𝔸)ˣ) :
    u ∈ Submodule.finiteIdeleStabilizer Λ ↔
      (u : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ ∧ ((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ :=
  ⟨fun hu => ⟨coe_mem_box_of_mem_stabilizer hΛ hu, coe_inv_mem_box_of_mem_stabilizer hΛ hu⟩,
   fun h => mem_stabilizer_of_coe_mem_of_coe_inv_mem hΛ h.1 h.2⟩

p2m_export "CSTowerT21.HL" "mem_stabilizer_iff"

def localBoxGen (Λ : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :=
  {x | ∃ z ∈ Λ, ∃ c : v.adicCompletion ℚ, c ∈ v.adicCompletionIntegers ℚ ∧ x = z ⊗ₜ[ℚ] c}

theorem mem_localBox_iff_span {Λ : Submodule ℤ ℍ[ℚ, a, b]} {v : HeightOneSpectrum (𝓞 ℚ)} {x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ} :
    x ∈ Submodule.localBox Λ v ↔ x ∈ Submodule.span ℤ (localBoxGen Λ v) := by
  have : Submodule.localBox Λ v = (Submodule.span ℤ (localBoxGen Λ v)).toAddSubgroup := by
    rw [Submodule.span_int_eq_addSubgroupClosure]; rfl
  rw [this]; rfl

theorem finiteAdeleEvalAt_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (v : HeightOneSpectrum (𝓞 ℚ))
    {x : ℍ𝔸} (hx : x ∈ Submodule.finiteAdeleBox Λ) :
    Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v x ∈ Submodule.localBox Λ v := by
  rw [mem_box_iff] at hx
  rw [mem_localBox_iff_span]
  induction hx using Submodule.span_induction with
  | mem x hx' =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hx'
    refine Submodule.subset_span ⟨z, hz, c v, hc v, ?_⟩
    simp [Submodule.finiteAdeleEvalAt, Submodule.finiteAdeleEvalAlgHom_apply]
  | zero => rw [map_zero]; exact zero_mem _
  | add x₁ x₂ _ _ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
  | smul m x₁ _ h₁ => rw [map_zsmul]; exact Submodule.smul_mem _ _ h₁

theorem tmul_one_mul_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (v : HeightOneSpectrum (𝓞 ℚ))
    {c : v.adicCompletion ℚ} (hc : c ∈ v.adicCompletionIntegers ℚ)
    {x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ} (hx : x ∈ Submodule.localBox Λ v) :
    ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) * x ∈ Submodule.localBox Λ v := by
  rw [mem_localBox_iff_span] at hx ⊢
  induction hx using Submodule.span_induction with
  | mem x hx' =>
    obtain ⟨z, hz, c', hc', rfl⟩ := hx'
    refine Submodule.subset_span ⟨z, hz, c * c', mul_mem hc hc', ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [mul_zero]; exact zero_mem _
  | add x₁ x₂ _ _ h₁ h₂ => rw [mul_add]; exact add_mem h₁ h₂
  | smul m x₁ _ h₁ => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h₁

theorem map_finiteAdeleEvalAt_mem_localBoxUnits_of_mem_primeHeckeSet {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    (ℓ : ℕ) {h : (ℍ𝔸)ˣ} (hh : h ∈ QuaternionAlgebra.primeHeckeSet Λ ℓ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hℓv : algebraMap ℚ (v.adicCompletion ℚ) ((ℓ : ℚ)⁻¹) ∈ v.adicCompletionIntegers ℚ) :
    Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom h ∈ Submodule.localBoxUnits Λ v := by
  obtain ⟨h1, h2, -, h4⟩ := hh
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓpos
  · exfalso; apply h4
    rw [Nat.cast_zero, inv_zero, zero_smul]; exact zero_mem _
  have hℓ0 : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓpos.ne'
  rw [Submodule.mem_localBoxUnits_iff]
  refine ⟨finiteAdeleEvalAt_mem_localBox v h1, ?_⟩

  set f := Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v with hf
  have e1 : (((Units.map f.toRingHom.toMonoidHom h)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)
      = f ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) := Units.coe_map_inv _ _
  have e2 : f ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) =
      ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ (v.adicCompletion ℚ) ((ℓ : ℚ)⁻¹)) * f ((ℓ : ℚ) • ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) := by
    rw [map_smul, ← Algebra.TensorProduct.algebraMap_apply', ← Algebra.smul_def, smul_smul, inv_mul_cancel₀ hℓ0, one_smul]
  show (((Units.map f.toRingHom.toMonoidHom h)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ _
  rw [e1, e2]
  exact tmul_one_mul_mem_localBox v hℓv (finiteAdeleEvalAt_mem_localBox v h2)

theorem localBox_mono {Λ Λ' : Submodule ℤ ℍ[ℚ, a, b]} (h : Λ ≤ Λ') (v : HeightOneSpectrum (𝓞 ℚ)) :
    Submodule.localBox Λ v ≤ Submodule.localBox Λ' v := by
  unfold Submodule.localBox
  refine AddSubgroup.closure_mono ?_
  rintro x ⟨z, hz, c, hc, rfl⟩
  exact ⟨z, h hz, c, hc, rfl⟩

theorem mul_tmul_one_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (v : HeightOneSpectrum (𝓞 ℚ))
    {c : v.adicCompletion ℚ} (hc : c ∈ v.adicCompletionIntegers ℚ)
    {x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ} (hx : x ∈ Submodule.localBox Λ v) :
    x * ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) ∈ Submodule.localBox Λ v := by
  rw [mem_localBox_iff_span] at hx ⊢
  induction hx using Submodule.span_induction with
  | mem x hx' =>
    obtain ⟨z, hz, c', hc', rfl⟩ := hx'
    refine Submodule.subset_span ⟨z, hz, c' * c, mul_mem hc' hc, ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  | zero => rw [zero_mul]; exact zero_mem _
  | add x₁ x₂ _ _ h₁ h₂ => rw [add_mul]; exact add_mem h₁ h₂
  | smul m x₁ _ h₁ => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ h₁

theorem localBox_mul_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (v : HeightOneSpectrum (𝓞 ℚ))
    {x y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ} (hx : x ∈ Submodule.localBox Λ v) (hy : y ∈ Submodule.localBox Λ v) :
    x * y ∈ Submodule.localBox Λ v := by
  rw [mem_localBox_iff_span] at hx hy ⊢
  induction hy using Submodule.span_induction with
  | mem y hy' =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hy'
    induction hx using Submodule.span_induction with
    | mem x hx' =>
      obtain ⟨z', hz', c', hc', rfl⟩ := hx'
      refine Submodule.subset_span ⟨z' * z, hΛ.mul_mem hz' hz, c' * c, mul_mem hc' hc, ?_⟩
      rw [Algebra.TensorProduct.tmul_mul_tmul]
    | zero => rw [zero_mul]; exact zero_mem _
    | add x₁ x₂ _ _ h₁ h₂ => rw [add_mul]; exact add_mem h₁ h₂
    | smul m x₁ _ h₁ => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ h₁
  | zero => rw [mul_zero]; exact zero_mem _
  | add y₁ y₂ _ _ h₁ h₂ => rw [mul_add]; exact add_mem h₁ h₂
  | smul m y₁ _ h₁ => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h₁

theorem one_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    (1 : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox Λ v := by
  rw [mem_localBox_iff_span]
  exact Submodule.subset_span ⟨1, hΛ.one_mem, 1, one_mem _, rfl⟩

theorem tmul_one_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} {z : ℍ[ℚ, a, b]} (hz : z ∈ Λ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    z ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ) ∈ Submodule.localBox Λ v := by
  rw [mem_localBox_iff_span]
  exact Submodule.subset_span ⟨z, hz, 1, one_mem _, rfl⟩

end CSTowerT21.HL
p2m_reactivate "P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.DoubleCosetFibre P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.CSTower P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.CSTowerT21"
p2m_reactivate "P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.DoubleCosetFibre P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.CSTower P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.CSTowerT21"

namespace CSTowerT21
namespace C4T

variable {a b : ℚ}

local notation "ℍ𝔸" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ

open CSTowerT21.HL

theorem mul_mem_localBoxUnits {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (w : HeightOneSpectrum (𝓞 ℚ))
    {u u' : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ} (hu : u ∈ Submodule.localBoxUnits Λ w) (hu' : u' ∈ Submodule.localBoxUnits Λ w) :
    u * u' ∈ Submodule.localBoxUnits Λ w := by
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul]; exact localBox_mul_mem hΛ w hu.1 hu'.1
  · rw [mul_inv_rev, Units.val_mul]; exact localBox_mul_mem hΛ w hu'.2 hu.2

theorem inv_mem_localBoxUnits {Λ : Submodule ℤ ℍ[ℚ, a, b]} (w : HeightOneSpectrum (𝓞 ℚ))
    {u : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ} (hu : u ∈ Submodule.localBoxUnits Λ w) : u⁻¹ ∈ Submodule.localBoxUnits Λ w :=
  ⟨hu.2, by rw [inv_inv]; exact hu.1⟩

theorem one_mem_localBoxUnits {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (w : HeightOneSpectrum (𝓞 ℚ)) :
    (1 : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) ∈ Submodule.localBoxUnits Λ w :=
  ⟨by rw [Units.val_one]; exact one_mem_localBox hΛ w, by rw [inv_one, Units.val_one]; exact one_mem_localBox hΛ w⟩

theorem mem_stabilizer_localBox_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (w : HeightOneSpectrum (𝓞 ℚ))
    (g : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) :
    g ∈ MulAction.stabilizer (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ ((Submodule.localBox Λ w : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)) ↔
      g ∈ Submodule.localBoxUnits Λ w := by
  constructor
  · intro hg
    have hg' : g⁻¹ ∈ MulAction.stabilizer (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ ((Submodule.localBox Λ w : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)) := inv_mem hg
    rw [MulAction.mem_stabilizer_iff] at hg hg'
    refine ⟨?_, ?_⟩
    · have h1 : (g : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) * 1 ∈ g • ((Submodule.localBox Λ w : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)) :=
        Set.smul_mem_smul_set (one_mem_localBox hΛ w)
      rw [hg, mul_one] at h1; exact h1
    · have h1 : ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) * 1 ∈ g⁻¹ • ((Submodule.localBox Λ w : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)) :=
        Set.smul_mem_smul_set (one_mem_localBox hΛ w)
      rw [hg', mul_one] at h1; exact h1
  · rintro ⟨h1, h2⟩
    rw [MulAction.mem_stabilizer_iff]
    apply Set.Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact localBox_mul_mem hΛ w h1 hx
    · intro x hx
      refine ⟨(g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) • x, localBox_mul_mem hΛ w h2 hx, ?_⟩
      show (g : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) * (((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) * x) = x
      rw [← mul_assoc, Units.mul_inv, one_mul]

theorem finiteAdeleEvalAt_smul (w : HeightOneSpectrum (𝓞 ℚ)) (c : ℚ) (x : ℍ𝔸) :
    Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (c • x) =
      ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ (w.adicCompletion ℚ) c) * Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w x := by
  rw [map_smul, ← Algebra.TensorProduct.algebraMap_apply', ← Algebra.smul_def]
  try rfl

theorem natCast_smul_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (w : HeightOneSpectrum (𝓞 ℚ)) (q : ℕ)
    {y : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ} (hy : y ∈ Submodule.localBox Λ w) : (q : ℚ) • y ∈ Submodule.localBox Λ w := by
  rw [Nat.cast_smul_eq_nsmul ℚ]; exact AddSubgroup.nsmul_mem _ hy q

theorem inv_natCast_integral_of_ne {q : ℕ} (hq : q.Prime) {v w : HeightOneSpectrum (𝓞 ℚ)}
    (hqv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) (hw : w ≠ v) :
    algebraMap ℚ (w.adicCompletion ℚ) ((q : ℚ)⁻¹) ∈ w.adicCompletionIntegers ℚ := by
  apply Nat.inv_natCast_mem_adicCompletionIntegers_of_not_mem_placesOf hq.ne_zero
  intro hmem
  rw [Nat.mem_placesOf_iff hq.ne_zero] at hmem
  exact hw (Nat.HeightOneSpectrum.eq_of_natCast_prime_mem hq hmem hqv)

theorem exists_natCast_mem_asIdeal {q : ℕ} (hq : q.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 ℚ), ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal :=
  ⟨⟨Ideal.span {(q : 𝓞 ℚ)}, (Nat.isMaximal_span_natCast_of_prime hq).isPrime, Nat.span_natCast_ne_bot hq.ne_zero⟩,
    Ideal.mem_span_singleton_self _⟩

def OffUnit (Λ : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) (h : (ℍ𝔸)ˣ) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w).toRingHom.toMonoidHom h ∈ Submodule.localBoxUnits Λ w

theorem offUnit_of_mem_primeHeckeSet {Λ : Submodule ℤ ℍ[ℚ, a, b]} {q : ℕ} (hq : q.Prime)
    {v : HeightOneSpectrum (𝓞 ℚ)} (hqv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    {h : (ℍ𝔸)ˣ} (hh : h ∈ QuaternionAlgebra.primeHeckeSet Λ q) : OffUnit Λ v h :=
  fun w hw => map_finiteAdeleEvalAt_mem_localBoxUnits_of_mem_primeHeckeSet q hh w (inv_natCast_integral_of_ne hq hqv hw)

theorem exists_offUnit_map_eq {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (g : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) :
    ∃ β : (ℍ𝔸)ˣ, Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom β = g ∧ OffUnit Λ v β := by
  classical
  obtain ⟨β, h1, h2⟩ := Submodule.exists_units_finiteAdeleEvalAt_eq (D := ℍ[ℚ, a, b]) {v}
    (Function.update (fun w : HeightOneSpectrum (𝓞 ℚ) => (1 : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ)) v g)
  have h1v := h1 v (Finset.mem_singleton_self v)
  rw [Function.update_self] at h1v
  refine ⟨β, Units.ext h1v, fun w hw => ?_⟩
  have e : Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w).toRingHom.toMonoidHom β = 1 := Units.ext (h2 w (fun hmem => hw (Finset.mem_singleton.mp hmem)))
  rw [e]; exact one_mem_localBoxUnits hΛ w

theorem mem_box_iff_local {X : Submodule ℤ ℍ[ℚ, a, b]} (hX : QuaternionAlgebra.IsOrder X) (v : HeightOneSpectrum (𝓞 ℚ))
    {x : ℍ𝔸} (hx : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w x ∈ Submodule.localBox X w) :
    x ∈ Submodule.finiteAdeleBox X ↔ Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v x ∈ Submodule.localBox X v := by
  rw [Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox X hX.fg hX.spanTop]
  refine ⟨fun h => h v, fun h w => ?_⟩
  by_cases hw : w = v
  · subst hw; exact h
  · exact hx w hw

def locT (R : Submodule ℤ ℍ[ℚ, a, b]) (q : ℕ) (v : HeightOneSpectrum (𝓞 ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ :=
  {g |
        ((g : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox R v ∧
          (q : ℚ) • ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox R v ∧
          ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∉ Submodule.localBox R v ∧
          (q : ℚ)⁻¹ • (g : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∉ Submodule.localBox R v)}

theorem mem_primeHeckeSet_iff_local {R : Submodule ℤ ℍ[ℚ, a, b]} (hRo : QuaternionAlgebra.IsOrder R) {q : ℕ} (hq : q.Prime)
    {v : HeightOneSpectrum (𝓞 ℚ)} (hqv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) {h : (ℍ𝔸)ˣ} (hoff : OffUnit R v h) :
    h ∈ QuaternionAlgebra.primeHeckeSet R q ↔ Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom h ∈ locT R q v := by
  have off1 : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (h : ℍ𝔸) ∈ Submodule.localBox R w :=
    fun w hw => (hoff w hw).1
  have off2 : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.localBox R w :=
    fun w hw => (hoff w hw).2
  have off3 : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((q : ℚ) • ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) ∈ Submodule.localBox R w :=
    fun w hw => by rw [map_smul]; exact natCast_smul_mem_localBox w q (off2 w hw)
  have off4 : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((q : ℚ)⁻¹ • (h : ℍ𝔸)) ∈ Submodule.localBox R w :=
    fun w hw => by
      rw [finiteAdeleEvalAt_smul]
      exact tmul_one_mul_mem_localBox w (inv_natCast_integral_of_ne hq hqv hw) (off1 w hw)
  rw [QuaternionAlgebra.mem_primeHeckeSet_iff, mem_box_iff_local hRo v off1, mem_box_iff_local hRo v off3,
    mem_box_iff_local hRo v off2, mem_box_iff_local hRo v off4, map_smul, map_smul]
  exact Iff.rfl

theorem map_mem_stabilizer_of_mem_finiteIdeleStabilizer {R : Submodule ℤ ℍ[ℚ, a, b]} (hRo : QuaternionAlgebra.IsOrder R)
    (v : HeightOneSpectrum (𝓞 ℚ)) {u : (ℍ𝔸)ˣ} (hu : u ∈ Submodule.finiteIdeleStabilizer R) :
    Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom u ∈ MulAction.stabilizer (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ ((Submodule.localBox R v : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) := by
  rw [QuaternionAlgebra.IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits _ hRo] at hu
  exact (mem_stabilizer_localBox_iff hRo v _).mpr (hu v)

theorem inv_mul_mem_finiteIdeleStabilizer_of_local {R : Submodule ℤ ℍ[ℚ, a, b]} (hRo : QuaternionAlgebra.IsOrder R)
    {v : HeightOneSpectrum (𝓞 ℚ)} {h h' : (ℍ𝔸)ˣ} (hoff : OffUnit R v h) (hoff' : OffUnit R v h')
    (hK : (Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom h)⁻¹ * Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom h' ∈ MulAction.stabilizer (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ ((Submodule.localBox R v : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ))) :
    h⁻¹ * h' ∈ Submodule.finiteIdeleStabilizer R := by
  rw [QuaternionAlgebra.IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits _ hRo]
  intro w
  rw [map_mul, map_inv]
  by_cases hw : w = v
  · subst hw; exact (mem_stabilizer_localBox_iff hRo _ _).mp hK
  · exact mul_mem_localBoxUnits hRo w (inv_mem_localBoxUnits w (hoff w hw)) (hoff' w hw)

end CSTowerT21.C4T
p2m_reactivate "P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.DoubleCosetFibre P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.CSTower P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.CSTowerT21"
p2m_reactivate "P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.DoubleCosetFibre P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.CSTower P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.CSTowerT21"

namespace CSTowerT21
namespace DC

variable {a b : ℚ}

local notation "ℍ𝔸" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "EV" w => (Units.map (RingHom.toMonoidHom (AlgHom.toRingHom (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w))))

theorem doubleCoset_subset_primeHeckeSet {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (ℓ : ℕ) {g : (ℍ𝔸)ˣ}
    (hg : g ∈ primeHeckeSet Λ ℓ) :
    DoubleCoset.doubleCoset g (Submodule.finiteIdeleStabilizer Λ : Set (ℍ𝔸)ˣ) (Submodule.finiteIdeleStabilizer Λ) ⊆
      primeHeckeSet Λ ℓ := by
  intro h hh
  obtain ⟨x, hx, y, hy, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hh
  exact HL.mul_mem_primeHeckeSet_of_mem_stabilizer' hΛ ℓ hy (HL.mul_mem_primeHeckeSet_of_mem_stabilizer hΛ ℓ hx hg)

theorem val_ellHat (ℓ : ℕ) [Fact ℓ.Prime] :
    ((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom
        (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))) : (ℍ𝔸)ˣ) : ℍ𝔸) =
      (ℓ : ℚ) • (1 : ℍ𝔸) := by
  change (algebraMap ℚ ℍ[ℚ, a, b] (ℓ : ℚ)) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) = _
  rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul', Algebra.TensorProduct.one_def]

theorem val_ellHat_inv (ℓ : ℕ) [Fact ℓ.Prime] :
    (((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom
        (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))))⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) =
      (ℓ : ℚ)⁻¹ • (1 : ℍ𝔸) := by
  rw [← map_inv, ← map_inv]
  change (algebraMap ℚ ℍ[ℚ, a, b]
    (((Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))⁻¹ : ℚˣ) : ℚ)) ⊗ₜ[ℚ]
      (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) = _
  rw [Units.val_inv_eq_inv_val, Units.val_mk0, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul',
    Algebra.TensorProduct.one_def]

theorem mem_primeHeckeSet_iff_ellHat_mul_inv_mem (Λ : Submodule ℤ ℍ[ℚ, a, b]) (ℓ : ℕ) [Fact ℓ.Prime] (h : (ℍ𝔸)ˣ) :
    h ∈ primeHeckeSet Λ ℓ ↔
      Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]
          (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom
            (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))) * h⁻¹ ∈
        primeHeckeSet Λ ℓ := by
  set T := Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom
      (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))) with hTdef
  have hℓ0 : (ℓ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
  have hT : (T : ℍ𝔸) = (ℓ : ℚ) • (1 : ℍ𝔸) := val_ellHat ℓ
  have hTi : ((T⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) = (ℓ : ℚ)⁻¹ • (1 : ℍ𝔸) := val_ellHat_inv ℓ
  have e1 : ((T * h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) = (ℓ : ℚ) • ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) := by
    rw [Units.val_mul, hT, smul_mul_assoc, one_mul]
  have e3 : (((T * h⁻¹)⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) = (ℓ : ℚ)⁻¹ • (h : ℍ𝔸) := by
    rw [mul_inv_rev, inv_inv, Units.val_mul, hTi, mul_smul_comm, mul_one]
  have e2 : (ℓ : ℚ) • (((T * h⁻¹)⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) = (h : ℍ𝔸) := by
    rw [e3, smul_smul, mul_inv_cancel₀ hℓ0, one_smul]
  have e4 : (ℓ : ℚ)⁻¹ • ((T * h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) = ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) := by
    rw [e1, smul_smul, inv_mul_cancel₀ hℓ0, one_smul]
  rw [QuaternionAlgebra.mem_primeHeckeSet_iff, QuaternionAlgebra.mem_primeHeckeSet_iff, e2, e4, e3, e1]
  tauto

end CSTowerT21.DC
p2m_reactivate "P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.DoubleCosetFibre P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.CSTower P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.CSTowerT21"
p2m_reactivate "P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.DoubleCosetFibre P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.CSTower P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.CSTowerT21"

namespace CSTowerT21
namespace VC

variable {a b : ℚ}

local notation "ℍ𝔸" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "EV" w => (Units.map (RingHom.toMonoidHom (AlgHom.toRingHom (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w))))

theorem mem_localBox_meetOrder_iff {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) (g : (ℍ𝔸)ˣ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :
    x ∈ Submodule.localBox (meetOrder R g) v ↔
      x ∈ Submodule.localBox R v ∧
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * x *
            Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (g : ℍ𝔸) ∈ Submodule.localBox R v := by
  have hc : IsOrder (Submodule.conjByFiniteIdele R g) := IsOrder.conjByFiniteIdele R hR g
  rw [show meetOrder R g = R ⊓ Submodule.conjByFiniteIdele R g from rfl,
    Submodule.localBox_inf R (Submodule.conjByFiniteIdele R g) hR.fg hR.spanTop hc.fg hc.spanTop v,
    AddSubgroup.mem_inf, Submodule.mem_localBox_conjByFiniteIdele_iff R hR.fg hR.spanTop g v]
  have i3 : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (g : ℍ𝔸) *
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have i4 : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) *
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (g : ℍ𝔸) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  refine and_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨y, hy, rfl⟩
    rw [← mul_assoc, ← mul_assoc, i4, one_mul, mul_assoc, i4, mul_one]; exact hy
  · intro h
    refine ⟨_, h, ?_⟩
    rw [← mul_assoc, ← mul_assoc, i3, one_mul, mul_assoc, i3, mul_one]

theorem localBox_meetOrder_eq {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) (g : (ℍ𝔸)ˣ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hgv : (EV v) g ∈ Submodule.localBoxUnits R v) :
    Submodule.localBox (meetOrder R g) v = Submodule.localBox R v := by
  ext x
  rw [mem_localBox_meetOrder_iff hR g v]
  refine ⟨And.left, fun hx => ⟨hx, ?_⟩⟩
  exact HL.localBox_mul_mem hR v (HL.localBox_mul_mem hR v hgv.2 hx) hgv.1

theorem primeHeckeSet_meetOrder_subset {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) {q ℓ : ℕ} (hq : q.Prime)
    (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) {n : (ℍ𝔸)ˣ} (hn : n ∈ primeHeckeSet R q) :
    primeHeckeSet (meetOrder R n) ℓ ⊆ primeHeckeSet R ℓ := by
  intro h hh
  have hS : IsOrder (meetOrder R n) := Stab.isOrder_meetOrder hR n
  obtain ⟨v, hv⟩ := Stab.exists_place ℓ hℓ
  have hqv : ((q : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := Stab.not_mem_of_prime_ne hℓ hq (Ne.symm hℓq) hv
  have hnv : (EV v) n ∈ Submodule.localBoxUnits R v := Stab.map_mem_localBoxUnits_of_mem_primeHeckeSet hq.ne_zero hn hqv
  have hoffS : C4T.OffUnit (meetOrder R n) v h := C4T.offUnit_of_mem_primeHeckeSet hℓ hv hh
  have hoffR : C4T.OffUnit R v h := fun w hw => ((Stab.mem_localBoxUnits_meetOrder_iff hR n w _).mp (hoffS w hw)).1
  have hloc := (C4T.mem_primeHeckeSet_iff_local hS hℓ hv hoffS).mp hh
  apply (C4T.mem_primeHeckeSet_iff_local hR hℓ hv hoffR).mpr
  simp only [C4T.locT, Set.mem_setOf_eq] at hloc ⊢
  rw [localBox_meetOrder_eq hR n v hnv] at hloc
  exact hloc

theorem ellHat_comm (ℓ : ℕ) [Fact ℓ.Prime] (y : (ℍ𝔸)ˣ) :
    Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom
        (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))) * y =
      y * Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom
        (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, DC.val_ellHat, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]

theorem ellHat_mul_conj (ℓ : ℕ) [Fact ℓ.Prime] (y z : (ℍ𝔸)ˣ) :
    (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom
        (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))) * y)⁻¹ * z *
      (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom
        (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))) * y) = y⁻¹ * z * y := by
  set T := Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom
        (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))) with hT
  rw [mul_inv_rev]
  simp only [mul_assoc]
  congr 1
  rw [← mul_assoc z T y, ← ellHat_comm ℓ z, mul_assoc T z y, inv_mul_cancel_left]

theorem not_dvd_of_not_dvd_mul3 {ℓ N q q' : ℕ} (hℓ : ¬ ℓ ∣ N * q * q') : ¬ ℓ ∣ N ∧ ℓ ≠ q ∧ ℓ ≠ q' := by
  refine ⟨fun h => hℓ (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h q) q'), ?_, ?_⟩
  · rintro rfl
    exact hℓ (dvd_mul_of_dvd_left (dvd_mul_left ℓ N) q')
  · rintro rfl
    exact hℓ (dvd_mul_left ℓ (N * q))

theorem ellHat_mul_inv_mem {R : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hR : IsEichlerOrder R N) {q : ℕ} [Fact q.Prime]
    {n : (ℍ𝔸)ˣ} (hn : n ∈ primeHeckeSet R q) (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) {s : (ℍ𝔸)ˣ}
    (hs : Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]
        (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom
          (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))) * s⁻¹ ∈
      primeHeckeSet (meetOrder R n) ℓ) :
    Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]
        (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom
          (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))) * s⁻¹ ∈
      primeHeckeSet R ℓ :=
  primeHeckeSet_meetOrder_subset hR.isOrder (Fact.out : q.Prime) (Fact.out : ℓ.Prime) hℓq hn hs

theorem shift_mem {R : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hR : IsEichlerOrder R N) {q : ℕ} [Fact q.Prime]
    {n : (ℍ𝔸)ˣ} (hn : n ∈ primeHeckeSet R q) (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) {s : (ℍ𝔸)ˣ}
    (hs : Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]
        (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom
          (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))) * s⁻¹ ∈
      primeHeckeSet (meetOrder R n) ℓ) :
    s ∈ primeHeckeSet R ℓ :=
  (QuaternionAlgebra.mem_primeHeckeSet_iff_finiteIdeleDiagonal_mul_inv_mem R ℓ s).mpr
    (ellHat_mul_inv_mem hR hn ℓ hℓq hs)

theorem index_forget {q' : ℕ} [Fact q'.Prime] (hdef : IsDefiniteRamifiedExactlyAt a b q')
    {R : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hR : IsEichlerOrder R N) {q : ℕ} [Fact q.Prime]
    {n : (ℍ𝔸)ˣ} (hn : n ∈ primeHeckeSet R q)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ N * q * q') {s : (ℍ𝔸)ˣ}
    (hs : Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]
        (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom
          (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))) * s⁻¹ ∈
      primeHeckeSet (meetOrder R n) ℓ) :
    (Submodule.finiteIdeleStabilizer (meetOrder R s)).relIndex (Submodule.finiteIdeleStabilizer R) = ℓ + 1 := by
  obtain ⟨hℓN, hℓq, hℓq'⟩ := not_dvd_of_not_dvd_mul3 hℓ
  exact CerednikDrinfeld.relIndex_finiteIdeleStabilizer_meetOrder_eq_succ_of_mem_primeHeckeSet hdef hR ℓ hℓN hℓq'
    (shift_mem hR hn ℓ hℓq hs)

theorem index_shift {q' : ℕ} [Fact q'.Prime] (hdef : IsDefiniteRamifiedExactlyAt a b q')
    {R : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hR : IsEichlerOrder R N) {q : ℕ} [Fact q.Prime]
    {n : (ℍ𝔸)ˣ} (hn : n ∈ primeHeckeSet R q)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ N * q * q') {s : (ℍ𝔸)ˣ}
    (hs : Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]
        (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom
          (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))) * s⁻¹ ∈
      primeHeckeSet (meetOrder R n) ℓ) :
    (Submodule.finiteIdeleStabilizer (meetOrder R s)).relIndex
      ((Submodule.finiteIdeleStabilizer R).map (MulAut.conj s).toMonoidHom) = ℓ + 1 := by
  obtain ⟨hℓN, hℓq, hℓq'⟩ := not_dvd_of_not_dvd_mul3 hℓ
  have hRo : IsOrder R := hR.isOrder
  set T := Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom
        (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))) with hT
  have key : Submodule.finiteIdeleStabilizer (meetOrder R s) =
      (Submodule.finiteIdeleStabilizer (meetOrder R (T * s⁻¹))).map (MulAut.conj s).toMonoidHom := by
    ext x
    rw [Stab.mem_finiteIdeleStabilizer_meetOrder_iff hRo, Subgroup.mem_map_equiv,
      Stab.mem_finiteIdeleStabilizer_meetOrder_iff hRo, MulAut.conj_symm_apply, ellHat_mul_conj, inv_inv,
      show s * (s⁻¹ * x * s) * s⁻¹ = x by group]
    exact and_comm
  rw [key, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj s).injective]
  exact CerednikDrinfeld.relIndex_finiteIdeleStabilizer_meetOrder_eq_succ_of_mem_primeHeckeSet hdef hR ℓ hℓN hℓq'
    (ellHat_mul_inv_mem hR hn ℓ hℓq hs)

end CSTowerT21.VC
p2m_reactivate "P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.DoubleCosetFibre P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.CSTower P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.CSTowerT21"
p2m_reactivate "P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.DoubleCosetFibre P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.CSTower P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one.CSTowerT21"

theorem solution

    {a b : ℚ} {N q q' : ℕ} [NeZero N] (hN : Squarefree N) [Fact q.Prime] [Fact q'.Prime]
    (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q) (hq'5 : 5 ≤ q')
    (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn : n ∈ primeHeckeSet R q)
    (hS : IsEichlerOrder (meetOrder R n) (N * q))
    (hnorm : Submodule.conjByFiniteIdele (meetOrder R n) n = meetOrder R n)
    (hsq : ∀ x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)),
      classSetShift _ n (classSetShift _ n x) = x)
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)))]
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer R))]
    [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)))]
    [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer R))]

    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ N * q * q')
    (s : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hs : Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]
        (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom
          (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))) * s⁻¹ ∈
      primeHeckeSet (meetOrder R n) ℓ)
    (hR' : IsEichlerOrder (meetOrder R s) (N * ℓ))
    (n' : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn' : n' ∈ primeHeckeSet (meetOrder R s) q)
    (hS' : IsEichlerOrder (meetOrder (meetOrder R s) n') (N * ℓ * q))
    (hnorm' : Submodule.conjByFiniteIdele (meetOrder (meetOrder R s) n') n' = meetOrder (meetOrder R s) n')
    (hsq' : ∀ x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder (meetOrder R s) n')),
      classSetShift _ n' (classSetShift _ n' x) = x)
    (hnn' : n⁻¹ * n' ∈ Submodule.finiteIdeleStabilizer R) (hsn' : s * n' = n' * s)
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder (meetOrder R s) n')))]
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R s)))]
    [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R s)))] :
    ∃ α β : (classSetDegeneracyData (meetOrder R s) n').FiniteHom (classSetDegeneracyData R n),

      α.mapV = classSetForget _ _ ∧
      α.mapE = classSetForget _ _ ∧
      (∀ e, (α.deg e : ℕ) *
          Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf (Submodule.conjByFiniteIdele (meetOrder (meetOrder R s) n') e.out) u} =
        Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf (Submodule.conjByFiniteIdele (meetOrder R n) e.out) u}) ∧
      (∀ v, (α.degV v : ℕ) *
          Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf (Submodule.conjByFiniteIdele (meetOrder R s) v.out) u} =
        Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf (Submodule.conjByFiniteIdele R v.out) u}) ∧
      (α.degTotal : ℕ) = ℓ + 1 ∧

      (β.mapV = fun v => ClassSet.mk _ (v.out * s)) ∧
      (β.mapE = fun e => ClassSet.mk _ (e.out * s)) ∧
      (∀ e, (β.deg e : ℕ) *
          Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf (Submodule.conjByFiniteIdele (meetOrder (meetOrder R s) n') e.out) u} =
        Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf (Submodule.conjByFiniteIdele (meetOrder R n) (e.out * s)) u}) ∧
      (∀ v, (β.degV v : ℕ) *
          Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf (Submodule.conjByFiniteIdele (meetOrder R s) v.out) u} =
        Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf (Submodule.conjByFiniteIdele R (v.out * s)) u}) ∧
      (β.degTotal : ℕ) = ℓ + 1 := by
  classical
  have hRo : IsOrder R := hR.isOrder
  have hdpos : 0 < ℓ + 1 := Nat.succ_pos ℓ
  have hqP : q.Prime := Fact.out
  have hℓP : ℓ.Prime := Fact.out
  have hℓq : ℓ ≠ q := by
    rintro rfl
    exact hℓ (Dvd.dvd.mul_right (dvd_mul_left ℓ N) q')
  have hqNℓ : ¬ q ∣ N * ℓ := fun h => by
    rcases (Nat.Prime.dvd_mul hqP).mp h with h | h
    · exact hqN h
    · exact hℓq ((Nat.prime_dvd_prime_iff_eq hqP hℓP).mp h).symm

  have hsS : s ∈ primeHeckeSet (meetOrder R n) ℓ :=
    (QuaternionAlgebra.mem_primeHeckeSet_iff_finiteIdeleDiagonal_mul_inv_mem (meetOrder R n) ℓ s).mpr hs

  have IDX : (Submodule.finiteIdeleStabilizer (meetOrder R s)).relIndex (Submodule.finiteIdeleStabilizer R) = ℓ + 1 :=
    CSTowerT21.VC.index_forget hdef hR hn ℓ hℓ hs
  have IDXs : (Submodule.finiteIdeleStabilizer (meetOrder R s)).relIndex
      ((Submodule.finiteIdeleStabilizer R).map (MulAut.conj s).toMonoidHom) = ℓ + 1 :=
    CSTowerT21.VC.index_shift hdef hR hn ℓ hℓ hs

  have F1 : Submodule.finiteIdeleStabilizer (meetOrder R n) ⊓ Submodule.finiteIdeleStabilizer (meetOrder R s) ≤
      Submodule.finiteIdeleStabilizer (meetOrder (meetOrder R s) n') :=
    CSTowerT21.Stab.F1 hRo hqP hℓP hℓq hn hsS hn' hnn'
  have F2 : ∀ k : ↥(Submodule.finiteIdeleStabilizer R), ∃ k₁ : ↥(Submodule.finiteIdeleStabilizer (meetOrder R n)),
      ((k₁ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)⁻¹ * k) ∈ Submodule.finiteIdeleStabilizer (meetOrder R s) :=
    CSTowerT21.Stab.F2 hRo hqP hℓP hℓq hn hsS
  have F1s : (Submodule.finiteIdeleStabilizer (meetOrder R n)).map (MulAut.conj s).toMonoidHom ⊓
      Submodule.finiteIdeleStabilizer (meetOrder R s) ≤ Submodule.finiteIdeleStabilizer (meetOrder (meetOrder R s) n') :=
    CSTowerT21.Stab.F1s hRo hqP hℓP hℓq hn hsS hn' hnn' hsn'
  have F2s : ∀ k : ↥((Submodule.finiteIdeleStabilizer R).map (MulAut.conj s).toMonoidHom),
      ∃ k₁ : ↥((Submodule.finiteIdeleStabilizer (meetOrder R n)).map (MulAut.conj s).toMonoidHom),
        ((k₁ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)⁻¹ * k) ∈ Submodule.finiteIdeleStabilizer (meetOrder R s) :=
    CSTowerT21.Stab.F2s hRo hqP hℓP hℓq hn hsS
  have NS : ∀ u ∈ Submodule.finiteIdeleStabilizer (meetOrder R n),
      n⁻¹ * u * n ∈ Submodule.finiteIdeleStabilizer (meetOrder R n) :=
    CSTowerU9.stab_normal_of_conj_eq (CSTower.isOrder_meetOrder hRo n) hnorm
  have NN'S : n⁻¹ * n' ∈ Submodule.finiteIdeleStabilizer (meetOrder R n) :=
    CSTowerT21.Stab.inv_mul_mem_stabilizer_meetOrder hqq' hdef hR hqN hn hS hnorm hR' hqNℓ hn' hS' hnorm' hnn'
  refine CSTower.assemble hdef hRo hnn' hsn' (ℓ + 1) hdpos ?_ ?_ ?_ ?_ ?_ ?_
  · exact fun v' => CSTowerU9.sumV_forget hdef hRo (ℓ + 1) hdpos IDX v'
  · exact fun v e' h => CSTowerU9.harm_a_forget hdef hRo hnn' hsn' (ℓ + 1) hdpos IDX F1 F2 v e' h
  · exact fun v e' h => CSTowerU9.harm_b_forget hdef hRo hnn' hsn' (ℓ + 1) hdpos IDX F1 F2 NS NN'S hnorm hnorm' hsq hsq' v e' h
  · exact fun v' => CSTowerU9.sumV_shift hdef hRo (ℓ + 1) hdpos IDXs v'
  · exact fun v e' h => CSTowerU9.harm_a_shift hdef hRo hnn' hsn' (ℓ + 1) hdpos IDXs F1s F2s v e' h
  · exact fun v e' h => CSTowerU9.harm_b_shift hdef hRo hnn' hsn' (ℓ + 1) hdpos IDXs F1s F2s NS NN'S hnorm hnorm' hsq hsq' v e' h

end S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one
end P2MW
export P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one (solution)
