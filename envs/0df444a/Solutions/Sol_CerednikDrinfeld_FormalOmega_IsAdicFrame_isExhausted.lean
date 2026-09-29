-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.IsAdicFrame.isExhausted
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/d48d3c9b-d5d2-5a76-84ea-8f1906897749

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFrame
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_isExhausted

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
p2m_open "LT.LatticeTree CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_isExhausted.CerednikDrinfeld CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_isExhausted.CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Omega.IsExhausted Omega.upperHalfPlane"
namespace FormalOmega
p2m_export "CerednikDrinfeld.FormalOmega" "IsAdicFrame AdicPoint Omega"
namespace B2Aux
p2m_open "CerednikDrinfeld.FormalOmega CerednikDrinfeld"

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
  {C : Type} [Field C] [Algebra K C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
  {R : Type} [CommRing R] [Algebra 𝒪 R] [Algebra R C] [Algebra 𝒪 C] [IsScalarTower 𝒪 R C] [IsScalarTower 𝒪 K C]
  {ϖ : PseudoUniformizer K C}

theorem v_pi_eq (hF : IsAdicFrame π ϖ R) :
    Valued.v (algebraMap R C (algebraMap 𝒪 R π)) = Valued.v (algebraMap K C ϖ.ϖ) := by
  rw [← IsScalarTower.algebraMap_apply 𝒪 R C, hF.unif]

theorem exists_pow_le_v (hF : IsAdicFrame π ϖ R) (c : C) (hc : c ≠ 0) :
    ∃ n : ℕ, Valued.v (algebraMap K C ϖ.ϖ) ^ n ≤ Valued.v c := by
  classical
  by_cases h1 : 1 ≤ Valued.v c
  · exact ⟨0, by rw [pow_zero]; exact h1⟩
  push_neg at h1
  obtain ⟨r, hr⟩ := (hF.range_eq c).1 h1.le
  have hr0 : r ≠ 0 := by rintro rfl; exact hc (by rw [← hr, map_zero])
  haveI := hF.complete

  have hex : ∃ n : ℕ, r ∉ Ideal.span {algebraMap 𝒪 R π ^ n} := by
    by_contra hall
    push_neg at hall
    apply hr0
    refine IsHausdorff.haus' (I := Ideal.span {algebraMap 𝒪 R π}) r fun n => ?_
    rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
    exact hall n
  obtain ⟨n, hn⟩ := hex
  refine ⟨n, not_lt.1 fun hlt => hn ?_⟩

  have hπC : algebraMap R C (algebraMap 𝒪 R π) ≠ 0 := by
    intro h; have := hF.v_algebraMap_pos; rw [IsScalarTower.algebraMap_apply 𝒪 R C, h, map_zero] at this
    exact lt_irrefl _ this
  have hle : Valued.v (c / (algebraMap R C (algebraMap 𝒪 R π)) ^ n) ≤ 1 := by
    rw [map_div₀, map_pow, v_pi_eq hF, div_le_one₀ (pow_pos ϖ.pos n)]
    exact hlt.le
  obtain ⟨s, hs⟩ := (hF.range_eq _).1 hle
  have : r = algebraMap 𝒪 R π ^ n * s := hF.injective (by
    rw [map_mul, map_pow, hs, hr, mul_comm, div_mul_cancel₀ _ (pow_ne_zero n hπC)])
  rw [this]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

theorem exists_v_le_inv_pow (hF : IsAdicFrame π ϖ R) (c : C) :
    ∃ n : ℕ, Valued.v c ≤ (Valued.v (algebraMap K C ϖ.ϖ))⁻¹ ^ n := by
  by_cases hc : c = 0
  · exact ⟨0, by rw [hc, map_zero]; exact zero_le'⟩
  obtain ⟨n, hn⟩ := exists_pow_le_v hF c⁻¹ (inv_ne_zero hc)
  refine ⟨n, ?_⟩
  rw [map_inv₀] at hn
  rw [inv_pow, ← inv_inv (Valued.v c)]
  exact (inv_le_inv₀ (inv_pos.2 ((Valued.v).pos_iff.2 hc)) (pow_pos ϖ.pos n)).2 hn

theorem exists_v_le_v_sub (hF : IsAdicFrame π ϖ R) {z : C} (hz : z ∈ Omega.upperHalfPlane K C) :
    ∃ c : C, c ≠ 0 ∧ ∀ a : K, Valued.v c ≤ Valued.v (z - algebraMap K C a) := by
  have hopen : IsOpen (Set.range (algebraMap K C))ᶜ := hF.isClosed_range.isOpen_compl
  have hmem : (Set.range (algebraMap K C))ᶜ ∈ nhds z := hopen.mem_nhds hz
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.1 hmem
  obtain ⟨r, s, hr, hs, hrs⟩ := Valuation.exists_div_eq_of_unit (v := (Valued.v : Valuation C Γ₀)) γ
  have hr0 : r ≠ 0 := (Valued.v).pos_iff.1 hr
  have hs0 : s ≠ 0 := (Valued.v).pos_iff.1 hs
  have hc : Valued.v.restrict (r / s) = γ.1 := by rw [map_div₀, hrs]
  refine ⟨r / s, div_ne_zero hr0 hs0, fun a => ?_⟩
  by_contra hlt
  push_neg at hlt
  have hball : algebraMap K C a ∈ {y : C | Valued.v.restrict (y - z) < γ.1} := by
    show Valued.v.restrict (algebraMap K C a - z) < γ.1
    rw [← hc, Valuation.restrict_lt_iff, Valuation.map_sub_swap]
    exact hlt
  exact hγ hball ⟨a, rfl⟩

end CerednikDrinfeld.FormalOmega.B2Aux

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] {π : 𝒪}
    {C : Type} [Field C] [Algebra K C] [DecidableEq C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
    {R : Type} [CommRing R] [Algebra 𝒪 R] [Algebra R C] [Algebra 𝒪 C] [IsScalarTower 𝒪 R C] [IsScalarTower 𝒪 K C]
    (ϖ : PseudoUniformizer K C) (hF : IsAdicFrame π ϖ R) :
    IsExhausted ϖ := by
  classical
  intro z hz
  have hP1 : Valued.v (algebraMap K C ϖ.ϖ) ≤ 1 := ϖ.lt_one.le
  have hPinv : 1 ≤ (Valued.v (algebraMap K C ϖ.ϖ))⁻¹ := (one_le_inv₀ ϖ.pos).2 hP1
  obtain ⟨n₁, hn₁⟩ := CerednikDrinfeld.FormalOmega.B2Aux.exists_v_le_inv_pow hF z
  obtain ⟨c, hc0, hc⟩ := CerednikDrinfeld.FormalOmega.B2Aux.exists_v_le_v_sub hF hz
  obtain ⟨n₂, hn₂⟩ := CerednikDrinfeld.FormalOmega.B2Aux.exists_pow_le_v hF c hc0
  refine ⟨n₁ + n₂, ?_, fun a _ => ?_⟩
  · exact hn₁.trans (pow_le_pow_right₀ hPinv (Nat.le_add_right n₁ n₂))
  · exact ((pow_le_pow_of_le_one ϖ.pos.le hP1 (Nat.le_add_left n₂ n₁)).trans hn₂).trans (hc a)

end S_CerednikDrinfeld_FormalOmega_IsAdicFrame_isExhausted
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_isExhausted (solution)
