-- Prove2me | solution 1 for CerednikDrinfeld.classSetHeckeLaws_of_isEichlerOrder_meetOrder
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/57b27be2-78b4-57ba-a2b8-470a11890add

import Mathlib
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_Order_FiniteIdele
import Definitions.Def_Submodule_FiniteAdeleBox
import Theorems.Thm_QuaternionAlgebra_IsOrder_commute_classSetHeckeMatrix_of_subset_primeHeckeSet_of_coprime
import Theorems.Thm_CerednikDrinfeld_jointDelta_classSetEdgeHecke_mulVecLin_eq_classSetVertexHecke_mulVecLin_jointDelta_of_ne
import Theorems.Thm_CerednikDrinfeld_jointDelta_classSetEdgeHecke_mulVecLin_eq_zero_of_forall_jointDelta_eq_zero_of_mem_primeHeckeSet
import Theorems.Thm_CerednikDrinfeld_mul_mem_uHeckeSet_and_mul_mem_uHeckeSet_of_mem_finiteIdeleStabilizer_meetOrder
import Theorems.Thm_CerednikDrinfeld_mul_mem_levelHeckeUSet_and_mul_mem_levelHeckeUSet_of_mem_finiteIdeleStabilizer
import Theorems.Thm_QuaternionAlgebra_IsOrder_finite_setOf_exists_mem_quotientMk_eq_of_subset_primeHeckeSet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_classSetHeckeLaws_of_isEichlerOrder_meetOrder
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

noncomputable section

namespace ClassSetLawsAssembly

variable {a b : ℚ}

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

structure GoodSet (Λ O : Submodule ℤ ℍ[ℚ, a, b]) (ℓ : ℕ) (T : Set (ℍ𝔸)ˣ) : Prop where
  sub : T ⊆ primeHeckeSet O ℓ
  left : ∀ u ∈ Submodule.finiteIdeleStabilizer O, ∀ s ∈ T, u * s ∈ T
  right : ∀ u ∈ Submodule.finiteIdeleStabilizer O, ∀ s ∈ T, s * u ∈ T

theorem goodSet_primeHeckeSet (Λ O : Submodule ℤ ℍ[ℚ, a, b]) (hO : IsOrder O) (ℓ : ℕ) :
    GoodSet Λ O ℓ (primeHeckeSet O ℓ) :=
  ⟨subset_rfl, fun _ hu _ hs => mul_mem_primeHeckeSet_of_mem_stabilizer hO ℓ hu hs,
    fun _ hu _ hs => mul_mem_primeHeckeSet_of_mem_stabilizer' hO ℓ hu hs⟩

theorem goodSet_levelHeckeUSet (Λ O : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsOrder Λ) (hO : IsOrder O) (hOΛ : O ≤ Λ)
    (ℓ : ℕ) : GoodSet Λ O ℓ (levelHeckeUSet Λ O ℓ) :=
  ⟨fun _ h => h.1,
    fun _ hu _ hs => (mul_mem_levelHeckeUSet_and_mul_mem_levelHeckeUSet_of_mem_finiteIdeleStabilizer Λ O hΛ hO hOΛ ℓ hu hs).1,
    fun _ hu _ hs => (mul_mem_levelHeckeUSet_and_mul_mem_levelHeckeUSet_of_mem_finiteIdeleStabilizer Λ O hΛ hO hOΛ ℓ hu hs).2⟩

theorem goodSet_uHeckeSet (Λ R : Submodule ℤ ℍ[ℚ, a, b]) {N : ℕ} (q : ℕ) [Fact q.Prime]
    (n : (ℍ𝔸)ˣ) (hR : IsEichlerOrder R N) :
    GoodSet Λ (meetOrder R n) q (uHeckeSet R n q) :=
  ⟨fun _ h => h.1,
    fun _ hu _ hs => (mul_mem_uHeckeSet_and_mul_mem_uHeckeSet_of_mem_finiteIdeleStabilizer_meetOrder R hR.isOrder n q hu hs).1,
    fun _ hu _ hs => (mul_mem_uHeckeSet_and_mul_mem_uHeckeSet_of_mem_finiteIdeleStabilizer_meetOrder R hR.isOrder n q hu hs).2⟩

theorem commute_of_goodSet {Λ O : Submodule ℤ ℍ[ℚ, a, b]} (hO : IsOrder O)
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer O))] [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer O))]
    {ℓ ℓ' : ℕ} (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) (hne : ℓ ≠ ℓ')
    {T T' : Set (ℍ𝔸)ˣ} (hT : GoodSet Λ O ℓ T) (hT' : GoodSet Λ O ℓ' T') :
    Commute (classSetHeckeMatrix (Submodule.finiteIdeleStabilizer O) T)
      (classSetHeckeMatrix (Submodule.finiteIdeleStabilizer O) T') :=
  IsOrder.commute_classSetHeckeMatrix_of_subset_primeHeckeSet_of_coprime hO ℓ ℓ'
    ((Nat.coprime_primes hℓ hℓ').mpr hne) T T' hT.sub hT'.sub hT.left hT.right hT'.left hT'.right
    (IsOrder.finite_setOf_exists_mem_quotientMk_eq_of_subset_primeHeckeSet hO ℓ T hT.sub)
    (IsOrder.finite_setOf_exists_mem_quotientMk_eq_of_subset_primeHeckeSet hO ℓ' T' hT'.sub)

theorem main
    (N q q' : ℕ) [NeZero N] [Fact q.Prime] [Fact q'.Prime]
    (hqq' : q' ≠ q) (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N)
    (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (n : (ℍ𝔸)ˣ)
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)))]
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer R))]
    [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer R))]
    (hn : IsEichlerOrder (meetOrder R n) (N * q)) (hnH : n ∈ primeHeckeSet R q) :
    ClassSetHeckeLaws N q Λ R n := by
  classical
  have hRo : IsOrder R := hR.isOrder
  have hSo : IsOrder (meetOrder R n) := hn.isOrder
  have hΛo : IsOrder Λ := hΛ.isOrder
  have hSR : meetOrder R n ≤ R := inf_le_left
  have hSΛ : meetOrder R n ≤ Λ := hSR.trans hRΛ

  have hedge : ∀ ℓ : Nat.Primes, ∃ T, GoodSet Λ (meetOrder R n) ℓ T ∧
      classSetEdgeHecke N q Λ R n ℓ = classSetHeckeMatrix _ T := by
    intro ℓ
    unfold classSetEdgeHecke
    by_cases h1 : (ℓ : ℕ) = q
    · refine ⟨uHeckeSet R n q, ?_, by rw [if_pos h1]⟩
      rw [h1]; exact goodSet_uHeckeSet Λ R q n hR
    · by_cases h2 : (ℓ : ℕ) ∣ N
      · exact ⟨_, goodSet_levelHeckeUSet Λ _ hΛo hSo hSΛ ℓ, by rw [if_neg h1, if_pos h2]⟩
      · exact ⟨_, goodSet_primeHeckeSet Λ _ hSo ℓ, by rw [if_neg h1, if_neg h2]⟩
  have hvert : ∀ ℓ : Nat.Primes, ∃ T, GoodSet Λ R ℓ T ∧
      classSetVertexHecke N Λ R ℓ = classSetHeckeMatrix _ T := by
    intro ℓ
    unfold classSetVertexHecke
    by_cases h2 : (ℓ : ℕ) ∣ N
    · exact ⟨_, goodSet_levelHeckeUSet Λ _ hΛo hRo hRΛ ℓ, by rw [if_pos h2]⟩
    · exact ⟨_, goodSet_primeHeckeSet Λ _ hRo ℓ, by rw [if_neg h2]⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro ℓ ℓ'
    by_cases hℓℓ' : ℓ = ℓ'
    · subst hℓℓ'; exact Commute.refl _
    · obtain ⟨T, hT, hTe⟩ := hedge ℓ
      obtain ⟨T', hT', hTe'⟩ := hedge ℓ'
      rw [hTe, hTe']
      exact commute_of_goodSet hSo ℓ.2 ℓ'.2 (fun h => hℓℓ' (Subtype.ext h)) hT hT'
  ·
    intro ℓ ℓ'
    by_cases hℓℓ' : ℓ = ℓ'
    · subst hℓℓ'; exact Commute.refl _
    · obtain ⟨T, hT, hTe⟩ := hvert ℓ
      obtain ⟨T', hT', hTe'⟩ := hvert ℓ'
      rw [hTe, hTe']
      exact commute_of_goodSet hRo ℓ.2 ℓ'.2 (fun h => hℓℓ' (Subtype.ext h)) hT hT'
  ·
    intro ℓ hℓ i x
    have hℓ' : (ℓ : ℕ) ≠ q := by
      intro h; apply hℓ
      rw [Finset.mem_singleton]
      exact Subtype.ext h
    exact jointDelta_classSetEdgeHecke_mulVecLin_eq_classSetVertexHecke_mulVecLin_jointDelta_of_ne N q q' hqq' hqN hq'N
      hdef Λ R hΛ hR hRΛ n hn hnH ℓ hℓ' i x
  ·
    intro ℓ x hx i
    by_cases hℓ' : (ℓ : ℕ) = q
    · have : ℓ = ⟨q, Fact.out⟩ := Subtype.ext hℓ'
      subst this
      exact jointDelta_classSetEdgeHecke_mulVecLin_eq_zero_of_forall_jointDelta_eq_zero_of_mem_primeHeckeSet N q q' hqq'
        hqN hq'N hdef Λ R hΛ hR hRΛ n hn hnH x hx i
    · rw [jointDelta_classSetEdgeHecke_mulVecLin_eq_classSetVertexHecke_mulVecLin_jointDelta_of_ne N q q' hqq' hqN hq'N
        hdef Λ R hΛ hR hRΛ n hn hnH ℓ hℓ' i x, hx i, map_zero]

end ClassSetLawsAssembly

end

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem solution
    (N q q' : ℕ) [NeZero N] [Fact q.Prime] [Fact q'.Prime]
    (hqq' : q' ≠ q) (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N)
    {a b : ℚ} (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)))]
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer R))]
    [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer R))]
    (hn : IsEichlerOrder (meetOrder R n) (N * q)) (hnH : n ∈ primeHeckeSet R q) :
    ClassSetHeckeLaws N q Λ R n :=
  ClassSetLawsAssembly.main N q q' hqq' hqN hq'N hdef Λ R hΛ hR hRΛ n hn hnH

end S_CerednikDrinfeld_classSetHeckeLaws_of_isEichlerOrder_meetOrder
end P2MW
export P2MW.S_CerednikDrinfeld_classSetHeckeLaws_of_isEichlerOrder_meetOrder (solution)
