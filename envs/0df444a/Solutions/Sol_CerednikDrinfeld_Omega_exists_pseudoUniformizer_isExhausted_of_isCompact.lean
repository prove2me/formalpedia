-- Prove2me | solution 1 for CerednikDrinfeld.Omega.exists_pseudoUniformizer_isExhausted_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/55e161e2-38e2-5ae2-a255-6b5cb0f40607

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_exists_pseudoUniformizer_isExhausted_of_isCompact

set_option autoImplicit false

p2m_open "CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_exists_pseudoUniformizer_isExhausted_of_isCompact.CerednikDrinfeld.Omega Filter Topology"

namespace CerednikDrinfeld
namespace Omega
p2m_export "CerednikDrinfeld.Omega" "PseudoUniformizer affinoid mem_affinoid_iff' IsExhausted mem_upperHalfPlane_iff"
namespace K0LC
p2m_open "CerednikDrinfeld.Omega CerednikDrinfeld"

variable {K₀ K : Type} [Field K₀] [Field K] [Algebra K₀ K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

theorem v_lt_iff (x y : K) : Valued.v x < Valued.v y ↔ Valued.v.restrict x < Valued.v.restrict y :=
  (Valuation.isEquiv_restrict (Valued.v (R := K))).lt_iff_lt

theorem isOpen_vball (c d : K) : IsOpen {y : K | Valued.v (y - c) < Valued.v d} := by
  have : {y : K | Valued.v (y - c) < Valued.v d} = (fun y => y - c) ⁻¹' {x | Valued.v.restrict x < Valued.v.restrict d} := by
    ext y; simp only [Set.mem_setOf_eq, Set.mem_preimage]; exact v_lt_iff _ _
  rw [this]
  exact (Valued.isOpen_ball K _).preimage (continuous_id.sub continuous_const)

section
variable (ϖ₀ : K₀) (h0 : 0 < Valued.v (algebraMap K₀ K ϖ₀)) (h1 : Valued.v (algebraMap K₀ K ϖ₀) < 1)
  (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)

local notation "𝔭" => Valued.v (algebraMap K₀ K ϖ₀)

include h0 h1 in
theorem P_pow_mono {i j : ℕ} (h : i ≤ j) : 𝔭⁻¹ ^ i ≤ 𝔭⁻¹ ^ j :=
  pow_le_pow_right₀ ((one_le_inv₀ h0).2 h1.le) h

include h1 in
theorem p_pow_anti {i j : ℕ} (h : i ≤ j) : 𝔭 ^ j ≤ 𝔭 ^ i := pow_le_pow_right_of_le_one' h1.le h

include h1 in
theorem p_pow_le_one (n : ℕ) : 𝔭 ^ n ≤ 1 := pow_le_one₀ zero_le' h1.le

include h0 h1 in
theorem one_le_P_pow (n : ℕ) : 1 ≤ 𝔭⁻¹ ^ n := one_le_pow₀ ((one_le_inv₀ h0).2 h1.le)

include h1 hrk in

theorem exists_p_pow_le {y : K} (hy : y ≠ 0) : ∃ n : ℕ, 𝔭 ^ n ≤ Valued.v y := hrk _ y h1 hy

include h0 h1 hrk in

theorem exists_le_P_pow (y : K) : ∃ n : ℕ, Valued.v y ≤ 𝔭⁻¹ ^ n := by
  rcases eq_or_ne y 0 with rfl | hy
  · exact ⟨0, by rw [map_zero]; exact zero_le'⟩
  obtain ⟨n, hn⟩ := hrk _ y⁻¹ h1 (inv_ne_zero hy)
  refine ⟨n, ?_⟩
  rw [map_inv₀] at hn
  rw [inv_pow]
  exact (le_inv_comm₀ ((Valuation.pos_iff _).2 hy) (pow_pos h0 n)).2 hn

include h0 h1 hrk in
theorem scale (a : K₀) (ha : a ≠ 0) :
    ∃ N : ℕ, 𝔭 ^ N ≤ Valued.v (algebraMap K₀ K a) ∧ Valued.v (algebraMap K₀ K a) ≤ 𝔭⁻¹ ^ N := by
  have ha' : algebraMap K₀ K a ≠ 0 := by rwa [ne_eq, map_eq_zero]
  obtain ⟨N₁, h₁⟩ := exists_p_pow_le ϖ₀ h1 hrk ha'
  obtain ⟨N₂, h₂⟩ := exists_le_P_pow ϖ₀ h0 h1 hrk (algebraMap K₀ K a)
  exact ⟨max N₁ N₂, (p_pow_anti ϖ₀ h1 (le_max_left _ _)).trans h₁, h₂.trans (P_pow_mono ϖ₀ h0 h1 (le_max_right _ _))⟩

def pu : PseudoUniformizer K₀ K := ⟨ϖ₀, h0, h1, scale ϖ₀ h0 h1 hrk⟩

@[scoped simp] theorem pu_ϖ : (pu ϖ₀ h0 h1 hrk).ϖ = ϖ₀ := rfl

include h0 in

theorem finite_holes (hK₀ : ∀ r : Γ₀, IsCompact {x : K | x ∈ Set.range (algebraMap K₀ K) ∧ Valued.v x ≤ r}) (n : ℕ) :
    ∃ T : Finset K₀, ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 𝔭⁻¹ ^ n →
      ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < 𝔭 ^ n := by
  have hcov : {x : K | x ∈ Set.range (algebraMap K₀ K) ∧ Valued.v x ≤ 𝔭⁻¹ ^ n} ⊆
      ⋃ t : K₀, {y : K | Valued.v (y - algebraMap K₀ K t) < Valued.v ((algebraMap K₀ K ϖ₀) ^ n)} := by
    rintro x ⟨⟨t, rfl⟩, -⟩
    refine Set.mem_iUnion.2 ⟨t, ?_⟩
    show Valued.v (algebraMap K₀ K t - algebraMap K₀ K t) < Valued.v ((algebraMap K₀ K ϖ₀) ^ n)
    rw [sub_self, map_zero, map_pow]; exact pow_pos h0 n
  obtain ⟨T, hT⟩ := (hK₀ (𝔭⁻¹ ^ n)).elim_finite_subcover _ (fun t => isOpen_vball _ _) hcov
  refine ⟨T, fun a ha => ?_⟩
  have := hT ⟨⟨a, rfl⟩, ha⟩
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at this
  obtain ⟨t, ht, hlt⟩ := this
  exact ⟨t, ht, by rwa [map_pow] at hlt⟩

theorem exhausted (hK₀ : ∀ r : Γ₀, IsCompact {x : K | x ∈ Set.range (algebraMap K₀ K) ∧ Valued.v x ≤ r}) :
    IsExhausted (pu ϖ₀ h0 h1 hrk) := by
  intro z hz
  rw [mem_upperHalfPlane_iff] at hz
  have hz0 : z ≠ 0 := fun h => hz 0 (by rw [map_zero, h])

  obtain ⟨n₀, hn₀⟩ := exists_le_P_pow ϖ₀ h0 h1 hrk z

  set B : Set K := {x : K | x ∈ Set.range (algebraMap K₀ K) ∧ Valued.v x ≤ 𝔭⁻¹ ^ n₀} with hB
  have hzx : ∀ x ∈ B, z - x ≠ 0 := by
    rintro x ⟨⟨t, rfl⟩, -⟩ h
    exact hz t (sub_eq_zero.1 h).symm
  have hcov : B ⊆ ⋃ x : K, {y : K | Valued.v (y - x) < Valued.v (z - x)} := fun x hx =>
    Set.mem_iUnion.2 ⟨x, by
      show Valued.v (x - x) < Valued.v (z - x)
      rw [sub_self, map_zero]; exact (Valuation.pos_iff _).2 (hzx x hx)⟩
  obtain ⟨s, hs⟩ := (hK₀ (𝔭⁻¹ ^ n₀)).elim_finite_subcover _ (fun x => isOpen_vball _ _) hcov
  classical

  let m : K → ℕ := fun x => if h : z - x = 0 then 0 else (exists_p_pow_le ϖ₀ h1 hrk h).choose
  have hm : ∀ x : K, z - x ≠ 0 → 𝔭 ^ m x ≤ Valued.v (z - x) := fun x h => by
    simp only [m, dif_neg h]; exact (exists_p_pow_le ϖ₀ h1 hrk h).choose_spec
  let M : ℕ := s.sup m
  refine ⟨max n₀ M, ?_⟩
  rw [mem_affinoid_iff']
  refine ⟨hn₀.trans (P_pow_mono ϖ₀ h0 h1 (le_max_left _ _)), fun t => ?_⟩
  simp only [pu_ϖ]
  rcases le_or_gt (Valued.v (algebraMap K₀ K t)) (𝔭⁻¹ ^ n₀) with ht | ht
  ·
    have htB : algebraMap K₀ K t ∈ B := ⟨⟨t, rfl⟩, ht⟩
    have := hs htB
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at this
    obtain ⟨x, hxs, hlt⟩ := this
    have hx0 : z - x ≠ 0 := fun h => by
      rw [h, map_zero] at hlt; exact not_lt.2 zero_le' hlt
    have heq : Valued.v (z - algebraMap K₀ K t) = Valued.v (z - x) := by
      have : z - algebraMap K₀ K t = (z - x) + -(algebraMap K₀ K t - x) := by ring
      rw [this, Valuation.map_add_eq_of_lt_left _ (by rwa [Valuation.map_neg])]
    rw [heq]
    calc 𝔭 ^ max n₀ M ≤ 𝔭 ^ m x := p_pow_anti ϖ₀ h1 ((Finset.le_sup hxs).trans (le_max_right _ _))
      _ ≤ Valued.v (z - x) := hm x hx0
  ·
    have hlt : Valued.v z < Valued.v (-(algebraMap K₀ K t)) := by rw [Valuation.map_neg]; exact hn₀.trans_lt ht
    rw [sub_eq_add_neg, Valuation.map_add_eq_of_lt_right _ hlt, Valuation.map_neg]
    exact (p_pow_le_one ϖ₀ h1 _).trans ((one_le_P_pow ϖ₀ h0 h1 _).trans ht.le)

end

end CerednikDrinfeld.Omega.K0LC
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_exists_pseudoUniformizer_isExhausted_of_isCompact.CerednikDrinfeld P2MW.S_CerednikDrinfeld_Omega_exists_pseudoUniformizer_isExhausted_of_isCompact.CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_exists_pseudoUniformizer_isExhausted_of_isCompact.CerednikDrinfeld.Omega.K0LC"
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_exists_pseudoUniformizer_isExhausted_of_isCompact.CerednikDrinfeld P2MW.S_CerednikDrinfeld_Omega_exists_pseudoUniformizer_isExhausted_of_isCompact.CerednikDrinfeld.Omega"
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_exists_pseudoUniformizer_isExhausted_of_isCompact.CerednikDrinfeld"

open CerednikDrinfeld.Omega.K0LC in
theorem solution
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hK₀ : ∀ r : Γ₀, IsCompact {x : K | x ∈ Set.range (algebraMap K₀ K) ∧ Valued.v x ≤ r})
    (ϖ₀ : K₀) (h0 : 0 < Valued.v (algebraMap K₀ K ϖ₀)) (h1 : Valued.v (algebraMap K₀ K ϖ₀) < 1)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y) :
    ∃ ϖ : PseudoUniformizer K₀ K, ϖ.ϖ = ϖ₀ ∧ IsExhausted ϖ ∧
      ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀,
        Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
          ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n :=
  ⟨pu ϖ₀ h0 h1 hrk, rfl, exhausted ϖ₀ h0 h1 hrk hK₀, fun n => finite_holes ϖ₀ h0 hK₀ n⟩

end S_CerednikDrinfeld_Omega_exists_pseudoUniformizer_isExhausted_of_isCompact
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_exists_pseudoUniformizer_isExhausted_of_isCompact (solution)
