-- Prove2me | solution 1 for CerednikDrinfeld.jointDelta_zero_classSetEdgeHecke_mulVecLin_eq_classSetVertexHecke_mulVecLin_sub_of_mem_primeHeckeSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/118c989f-311c-53dc-841e-e8f85dc56534

import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Theorems.Thm_CerednikDrinfeld_uHeckeSet_subset_primeHeckeSet
import Theorems.Thm_CerednikDrinfeld_uHeckeSet_quotient_bijOn_primeHeckeSet_quotient_diff_of_prime
import Theorems.Thm_QuaternionAlgebra_IsOrder_finite_setOf_exists_mem_quotientMk_eq_of_subset_primeHeckeSet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_jointDelta_zero_classSetEdgeHecke_mulVecLin_eq_classSetVertexHecke_mulVecLin_sub_of_mem_primeHeckeSet
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

noncomputable section

namespace HeckeLocal

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

theorem mem_stabilizer_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (u : (ℍ𝔸)ˣ) :
    u ∈ Submodule.finiteIdeleStabilizer Λ ↔
      (u : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ ∧ ((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ :=
  ⟨fun hu => ⟨coe_mem_box_of_mem_stabilizer hΛ hu, coe_inv_mem_box_of_mem_stabilizer hΛ hu⟩,
   fun h => mem_stabilizer_of_coe_mem_of_coe_inv_mem hΛ h.1 h.2⟩

end HeckeLocal

namespace RelBKit

variable {a b : ℚ}

def IncB (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (S : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) {V : Type} (β : ClassSet U → V)
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (v : V) : Type :=
  {c : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ U //
    ∃ h ∈ S, (h : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ U) = c ∧ β (ClassSet.mk U (x * h)) = v}

abbrev cosetSet (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (S : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : Set ((ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ U) :=
  {c | ∃ h ∈ S, (h : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ U) = c}

theorem mk_mul_eq_of_coe_eq (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (x h h' : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hc : (h : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ U) = h') :
    ClassSet.mk U (x * h) = ClassSet.mk U (x * h') := by
  obtain ⟨u, hu, rfl⟩ : ∃ u ∈ U, h' = h * u := by
    have := QuotientGroup.eq.mp hc
    exact ⟨h⁻¹ * h', this, by group⟩
  rw [← mul_assoc, ClassSet.mk_mul_of_mem _ _ hu]

noncomputable def classOf (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (c : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ U) : ClassSet U :=
  ClassSet.mk U (x * c.out)

theorem classOf_coe (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (x h : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    classOf U x (h : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ U) = ClassSet.mk U (x * h) := by
  unfold classOf
  apply mk_mul_eq_of_coe_eq
  exact QuotientGroup.out_eq' _

noncomputable def incBEquivSigma (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (S : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) {V : Type} (β : ClassSet U → V)
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (v : V) :
    IncB U S β x v ≃ Σ y : {y : ClassSet U // β y = v}, HeckeIncidence U S x y.1 where
  toFun c := ⟨⟨classOf U x c.1, by
      obtain ⟨h, hh, hc, hv⟩ := c.2
      rw [← hc, classOf_coe]; exact hv⟩, ⟨c.1, by
      obtain ⟨h, hh, hc, hv⟩ := c.2
      exact ⟨h, hh, hc, by show ClassSet.mk U (x * h) = classOf U x c.1; rw [← hc, classOf_coe]⟩⟩⟩
  invFun s := ⟨s.2.1, by
      obtain ⟨h, hh, hc, hy⟩ := s.2.2
      exact ⟨h, hh, hc, by rw [hy]; exact s.1.2⟩⟩
  left_inv c := by rfl
  right_inv s := by
    obtain ⟨⟨y, hy⟩, ⟨c, hc⟩⟩ := s
    obtain ⟨h, hh, hhc, hyc⟩ := hc
    have : classOf U x c = y := by rw [← hhc, classOf_coe, hyc]
    subst this
    rfl

theorem sum_ite_heckeIncidence_card
    (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) [Fintype (ClassSet U)]
    (S : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hfin : (cosetSet U S).Finite)
    {V : Type} [DecidableEq V] (β : ClassSet U → V)
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (v : V) :
    (∑ y : ClassSet U, (if β y = v then (1 : ℤ) else 0) * (Nat.card (HeckeIncidence U S x y) : ℤ)) =
      Nat.card (IncB U S β x v) := by
  classical

  have hfinI : ∀ y, Finite (HeckeIncidence U S x y) := by
    intro y
    haveI := hfin.to_subtype
    refine Finite.of_injective (fun c => (⟨c.1, by obtain ⟨h, hh, hc, -⟩ := c.2; exact ⟨h, hh, hc⟩⟩ : cosetSet U S)) ?_
    intro c c' h
    exact Subtype.ext (by simpa using congrArg Subtype.val h)
  rw [Nat.card_congr (incBEquivSigma U S β x v)]
  haveI : ∀ y : {y : ClassSet U // β y = v}, Finite (HeckeIncidence U S x y.1) := fun y => hfinI y.1
  haveI : ∀ y : {y : ClassSet U // β y = v}, Fintype (HeckeIncidence U S x y.1) := fun y => Fintype.ofFinite _
  rw [Nat.card_sigma, Nat.cast_sum]
  simp_rw [ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype (Finset.univ.filter fun y => β y = v) (p := fun y => β y = v) (by simp)]

theorem card_incB_of_forall (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (S : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    {V : Type} [DecidableEq V] (β : ClassSet U → V)
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (v₀ v : V)
    (hβ : ∀ h ∈ S, β (ClassSet.mk U (x * h)) = v₀) :
    (Nat.card (IncB U S β x v) : ℤ) = (if v₀ = v then (1 : ℤ) else 0) * (Set.ncard (cosetSet U S) : ℤ) := by
  by_cases hv : v₀ = v
  · subst hv
    rw [if_pos rfl, one_mul, ← Nat.card_coe_set_eq]
    congr 1
    exact Nat.card_congr
      { toFun := fun c => ⟨c.1, by obtain ⟨h, hh, hc, -⟩ := c.2; exact ⟨h, hh, hc⟩⟩
        invFun := fun c => ⟨c.1, by obtain ⟨h, hh, hc⟩ := c.2; exact ⟨h, hh, hc, hβ h hh⟩⟩
        left_inv := fun c => rfl
        right_inv := fun c => rfl }
  · rw [if_neg hv, zero_mul]
    have : IsEmpty (IncB U S β x v) := ⟨fun c => by
      obtain ⟨h, hh, hc, hv'⟩ := c.2
      exact hv ((hβ h hh).symm.trans hv')⟩
    simp

end RelBKit

namespace RelAKit

variable {a b : ℚ}

open RelBKit

local notation "ℍ𝔸" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ

theorem a_mk {R : Submodule ℤ ℍ[ℚ, a, b]} (n : (ℍ𝔸)ˣ)
    (hle : Submodule.finiteIdeleStabilizer (meetOrder R n) ≤ Submodule.finiteIdeleStabilizer R) (y : (ℍ𝔸)ˣ) :
    (classSetDegeneracyData R n).a (ClassSet.mk _ y) = ClassSet.mk (Submodule.finiteIdeleStabilizer R) y := by
  show ClassSet.mk _ ((ClassSet.mk (Submodule.finiteIdeleStabilizer (meetOrder R n)) y).out) = _
  obtain ⟨δ, u, hδ, hu, hout⟩ :=
    DoubleCoset.mk_out_eq_mul (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]).range
      (Submodule.finiteIdeleStabilizer (meetOrder R n)) y
  rw [show (ClassSet.mk (Submodule.finiteIdeleStabilizer (meetOrder R n)) y).out = δ * y * u from hout]
  obtain ⟨δ', rfl⟩ := MonoidHom.mem_range.mp hδ
  rw [mul_assoc, ClassSet.mk_diagonal_mul, ClassSet.mk_mul_of_mem _ _ (hle hu)]

def cosetForget (U U' : Subgroup (ℍ𝔸)ˣ) (c : (ℍ𝔸)ˣ ⧸ U) : (ℍ𝔸)ˣ ⧸ U' :=
  (c.out : (ℍ𝔸)ˣ)

theorem cosetForget_coe {U U' : Subgroup (ℍ𝔸)ˣ} (hle : U ≤ U') (h : (ℍ𝔸)ˣ) :
    cosetForget U U' (h : (ℍ𝔸)ˣ ⧸ U) = (h : (ℍ𝔸)ˣ ⧸ U') := by
  unfold cosetForget
  apply QuotientGroup.eq.mpr
  apply hle
  apply QuotientGroup.eq.mp
  exact QuotientGroup.out_eq' _

theorem finite_heckeIncidence (U : Subgroup (ℍ𝔸)ˣ) (S : Set (ℍ𝔸)ˣ) (hfin : (cosetSet U S).Finite)
    (x : (ℍ𝔸)ˣ) (y : ClassSet U) : Finite (HeckeIncidence U S x y) := by
  haveI := hfin.to_subtype
  refine Finite.of_injective
    (fun c => (⟨c.1, by obtain ⟨h, hh, hc, -⟩ := c.2; exact ⟨h, hh, hc⟩⟩ : cosetSet U S)) ?_
  intro c c' h
  exact Subtype.ext (by simpa using congrArg Subtype.val h)

theorem card_incB_eq_card_sub {U U' : Subgroup (ℍ𝔸)ˣ} (hle : U ≤ U')
    (S T : Set (ℍ𝔸)ˣ) (hST : S ⊆ T) (n : (ℍ𝔸)ˣ) (hnT : n ∈ T)
    (hinj : ∀ h ∈ S, ∀ h' ∈ S, (h : (ℍ𝔸)ˣ ⧸ U') = (h' : (ℍ𝔸)ˣ ⧸ U') → (h : (ℍ𝔸)ˣ ⧸ U) = (h' : (ℍ𝔸)ˣ ⧸ U))
    (hsurj : ∀ g ∈ T, (g : (ℍ𝔸)ˣ ⧸ U') ≠ (n : (ℍ𝔸)ˣ ⧸ U') → ∃ h ∈ S, (h : (ℍ𝔸)ˣ ⧸ U') = (g : (ℍ𝔸)ˣ ⧸ U'))
    (hne : ∀ h ∈ S, (h : (ℍ𝔸)ˣ ⧸ U') ≠ (n : (ℍ𝔸)ˣ ⧸ U'))
    (hfin : (cosetSet U' T).Finite)
    (β : ClassSet U → ClassSet U') (hβ : ∀ z, β (ClassSet.mk U z) = ClassSet.mk U' z)
    [DecidableEq (ClassSet U')] (x : (ℍ𝔸)ˣ) (v : ClassSet U') :
    (Nat.card (IncB U S β x v) : ℤ) =
      Nat.card (HeckeIncidence U' T x v) - (if ClassSet.mk U' (x * n) = v then 1 else 0) := by
  classical

  set P := HeckeIncidence U' T x v with hP
  haveI : Finite P := finite_heckeIncidence U' T hfin x v

  let φ : IncB U S β x v → {c : P // c.1 ≠ (n : (ℍ𝔸)ˣ ⧸ U')} := fun c =>
    ⟨⟨cosetForget U U' c.1, by
        obtain ⟨h, hh, hc, hv⟩ := c.2
        refine ⟨h, hST hh, ?_, ?_⟩
        · rw [← hc, cosetForget_coe hle]
        · rw [hβ] at hv; exact hv⟩, by
        obtain ⟨h, hh, hc, hv⟩ := c.2
        show cosetForget U U' c.1 ≠ _
        rw [← hc, cosetForget_coe hle]
        exact hne h hh⟩
  have hφ : Function.Bijective φ := by
    constructor
    · intro c c' hcc'
      have h1 : cosetForget U U' c.1 = cosetForget U U' c'.1 :=
        congrArg (fun p : {c : P // c.1 ≠ (n : (ℍ𝔸)ˣ ⧸ U')} => p.1.1) hcc'
      obtain ⟨h, hh, hc, -⟩ := c.2
      obtain ⟨h', hh', hc', -⟩ := c'.2
      rw [← hc, ← hc', cosetForget_coe hle, cosetForget_coe hle] at h1
      apply Subtype.ext
      rw [← hc, ← hc']
      exact hinj h hh h' hh' h1
    · rintro ⟨⟨c, hc⟩, hcn⟩
      obtain ⟨g, hg, hgc, hgv⟩ := hc
      have hgn : (g : (ℍ𝔸)ˣ ⧸ U') ≠ (n : (ℍ𝔸)ˣ ⧸ U') := by rw [hgc]; exact hcn
      obtain ⟨h, hh, hhg⟩ := hsurj g hg hgn
      refine ⟨⟨(h : (ℍ𝔸)ˣ ⧸ U), h, hh, rfl, ?_⟩, ?_⟩
      · rw [hβ, mk_mul_eq_of_coe_eq U' x h g hhg, hgv]
      · apply Subtype.ext; apply Subtype.ext
        show cosetForget U U' (h : (ℍ𝔸)ˣ ⧸ U) = c
        rw [cosetForget_coe hle, hhg, hgc]
  have e1 : (Nat.card (IncB U S β x v) : ℤ) = Nat.card {c : P // c.1 ≠ (n : (ℍ𝔸)ˣ ⧸ U')} := by
    rw [Nat.card_congr (Equiv.ofBijective φ hφ)]

  have e2 : (Nat.card P : ℤ) =
      Nat.card {c : P // c.1 ≠ (n : (ℍ𝔸)ˣ ⧸ U')} + Nat.card {c : P // c.1 = (n : (ℍ𝔸)ˣ ⧸ U')} := by
    rw [← Nat.card_congr (Equiv.sumCompl fun c : P => c.1 = (n : (ℍ𝔸)ˣ ⧸ U')), Nat.card_sum]
    push_cast; ring

  have e3 : (Nat.card {c : P // c.1 = (n : (ℍ𝔸)ˣ ⧸ U')} : ℤ) = if ClassSet.mk U' (x * n) = v then 1 else 0 := by
    by_cases hv : ClassSet.mk U' (x * n) = v
    · rw [if_pos hv]
      haveI : Subsingleton {c : P // c.1 = (n : (ℍ𝔸)ˣ ⧸ U')} :=
        ⟨fun c c' => Subtype.ext (Subtype.ext (c.2.trans c'.2.symm))⟩
      have c₀ : {c : P // c.1 = (n : (ℍ𝔸)ˣ ⧸ U')} := ⟨⟨(n : (ℍ𝔸)ˣ ⧸ U'), n, hnT, rfl, hv⟩, rfl⟩
      exact_mod_cast Nat.card_of_subsingleton c₀
    · rw [if_neg hv]
      haveI : IsEmpty {c : P // c.1 = (n : (ℍ𝔸)ˣ ⧸ U')} := ⟨fun c => by
        obtain ⟨g, hg, hgc, hgv⟩ := c.1.2
        apply hv
        rw [← mk_mul_eq_of_coe_eq U' x g n (hgc.trans c.2), hgv]⟩
      simp
  rw [e1, ← e3]
  linarith [e2]

end RelAKit

theorem solution
    (N q q' : ℕ) [NeZero N] [Fact q.Prime] [Fact q'.Prime]
    (hqq' : q' ≠ q) (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N)
    {a b : ℚ} (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)))]
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer R))]
    [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer R))]
    (hn : IsEichlerOrder (meetOrder R n) (N * q)) (hnH : n ∈ primeHeckeSet R q)
    (x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)) → ℤ) :
    jointDelta (classSetDegeneracyData R n) 0 ((classSetEdgeHecke N q Λ R n ⟨q, Fact.out⟩).mulVecLin x) =
      (classSetVertexHecke N Λ R ⟨q, Fact.out⟩).mulVecLin (jointDelta (classSetDegeneracyData R n) 0 x) -
        jointDelta (classSetDegeneracyData R n) 1 x := by
  classical

  have hRo : QuaternionAlgebra.IsOrder R := hR.isOrder
  have hSo : QuaternionAlgebra.IsOrder (meetOrder R n) := hn.isOrder
  have hle : Submodule.finiteIdeleStabilizer (meetOrder R n) ≤ Submodule.finiteIdeleStabilizer R :=
    HeckeLocal.stabilizer_mono hSo hRo inf_le_left
  have C1 : uHeckeSet R n q ⊆ primeHeckeSet R q :=
    CerednikDrinfeld.uHeckeSet_subset_primeHeckeSet R q n hR hn
  obtain ⟨C2i, C2s, C2n⟩ :=
    CerednikDrinfeld.uHeckeSet_quotient_bijOn_primeHeckeSet_quotient_diff_of_prime R q n hR hqN hqq' hdef hnH hn
  have hfinS : (RelBKit.cosetSet (Submodule.finiteIdeleStabilizer (meetOrder R n)) (uHeckeSet R n q)).Finite :=
    QuaternionAlgebra.IsOrder.finite_setOf_exists_mem_quotientMk_eq_of_subset_primeHeckeSet hSo q (uHeckeSet R n q)
      (fun h hh => hh.1)
  have hfinR : (RelBKit.cosetSet (Submodule.finiteIdeleStabilizer R) (primeHeckeSet R q)).Finite :=
    QuaternionAlgebra.IsOrder.finite_setOf_exists_mem_quotientMk_eq_of_subset_primeHeckeSet hRo q (primeHeckeSet R q)
      (fun h hh => hh)
  have Tstab : ∀ u ∈ Submodule.finiteIdeleStabilizer R, ∀ s ∈ primeHeckeSet R q, u * s ∈ primeHeckeSet R q :=
    fun u hu s hs => HeckeLocal.mul_mem_primeHeckeSet_of_mem_stabilizer hRo q hu hs
  have A := RelAKit.a_mk (R := R) n hle

  have hM : classSetEdgeHecke N q Λ R n ⟨q, Fact.out⟩ = classSetHeckeMatrix _ (uHeckeSet R n q) := by
    unfold classSetEdgeHecke
    rw [if_pos rfl]
  have hMv : classSetVertexHecke N Λ R ⟨q, Fact.out⟩ = classSetHeckeMatrix _ (primeHeckeSet R q) := by
    unfold classSetVertexHecke
    rw [if_neg hqN]
  rw [hM, hMv]

  have hentry : ∀ (v : ClassSet (Submodule.finiteIdeleStabilizer R))
      (e : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n))),
      (degeneracyMatrix (classSetDegeneracyData R n).a *
          classSetHeckeMatrix (Submodule.finiteIdeleStabilizer (meetOrder R n)) (uHeckeSet R n q)) v e =
        (classSetHeckeMatrix (Submodule.finiteIdeleStabilizer R) (primeHeckeSet R q) *
            degeneracyMatrix (classSetDegeneracyData R n).a) v e -
          degeneracyMatrix (classSetDegeneracyData R n).b v e := by
    intro v e

    have hL : (degeneracyMatrix (classSetDegeneracyData R n).a *
          classSetHeckeMatrix (Submodule.finiteIdeleStabilizer (meetOrder R n)) (uHeckeSet R n q)) v e =
        Nat.card (RelBKit.IncB (Submodule.finiteIdeleStabilizer (meetOrder R n)) (uHeckeSet R n q)
          (classSetDegeneracyData R n).a e.out v) := by
      simp only [Matrix.mul_apply, degeneracyMatrix, classSetHeckeMatrix, Matrix.of_apply]
      have hrep : ∀ e', heckeKernel (Submodule.finiteIdeleStabilizer (meetOrder R n)) (uHeckeSet R n q) e e' =
          Nat.card (HeckeIncidence _ (uHeckeSet R n q) e.out e') := fun e' => rfl
      simp only [hrep]
      rw [← RelBKit.sum_ite_heckeIncidence_card _ (uHeckeSet R n q) hfinS (classSetDegeneracyData R n).a e.out v]

    have hR' : (classSetHeckeMatrix (Submodule.finiteIdeleStabilizer R) (primeHeckeSet R q) *
          degeneracyMatrix (classSetDegeneracyData R n).a) v e =
        Nat.card (HeckeIncidence (Submodule.finiteIdeleStabilizer R) (primeHeckeSet R q) e.out v) := by
      simp only [Matrix.mul_apply, degeneracyMatrix, classSetHeckeMatrix, Matrix.of_apply, mul_ite, mul_one,
        mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      have ha : (classSetDegeneracyData R n).a e = ClassSet.mk (Submodule.finiteIdeleStabilizer R) e.out := rfl
      rw [ha, heckeKernel_mk _ _ Tstab]
    have hB : degeneracyMatrix (classSetDegeneracyData R n).b v e =
        if ClassSet.mk (Submodule.finiteIdeleStabilizer R) (e.out * n) = v then 1 else 0 := rfl
    rw [hL, hR', hB]
    exact RelAKit.card_incB_eq_card_sub hle (uHeckeSet R n q) (primeHeckeSet R q) C1 n hnH C2i C2s C2n hfinR
      (classSetDegeneracyData R n).a A e.out v
  have hmat : degeneracyMatrix (classSetDegeneracyData R n).a *
        classSetHeckeMatrix (Submodule.finiteIdeleStabilizer (meetOrder R n)) (uHeckeSet R n q) =
      classSetHeckeMatrix (Submodule.finiteIdeleStabilizer R) (primeHeckeSet R q) *
          degeneracyMatrix (classSetDegeneracyData R n).a -
        degeneracyMatrix (classSetDegeneracyData R n).b := by
    ext v e
    rw [Matrix.sub_apply]
    exact hentry v e

  simp only [jointDelta, Matrix.cons_val_one, Matrix.cons_val_zero, pushforward, Matrix.mulVecLin_apply,
    Matrix.mulVec_mulVec]
  rw [hmat, Matrix.sub_mulVec]

end

end S_CerednikDrinfeld_jointDelta_zero_classSetEdgeHecke_mulVecLin_eq_classSetVertexHecke_mulVecLin_sub_of_mem_primeHeckeSet
end P2MW
export P2MW.S_CerednikDrinfeld_jointDelta_zero_classSetEdgeHecke_mulVecLin_eq_classSetVertexHecke_mulVecLin_sub_of_mem_primeHeckeSet (solution)
