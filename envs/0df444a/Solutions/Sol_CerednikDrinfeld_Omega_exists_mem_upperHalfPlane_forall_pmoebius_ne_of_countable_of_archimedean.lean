-- Prove2me | solution 1 for CerednikDrinfeld.Omega.exists_mem_upperHalfPlane_forall_pmoebius_ne_of_countable_of_archimedean
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/5d47e270-738e-56ee-808b-3666cf2456d8

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_exists_mem_upperHalfPlane_forall_pmoebius_ne_of_countable_of_archimedean

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega Filter Topology

namespace AvoidPt

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
  {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

theorem exists_pow_lt (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass (Valued.v (R := K)) : K →*₀ Γ₀))ˣ) :
    ∃ N : ℕ, ∀ n, N ≤ n → vRestrict K (algebraMap K₀ K ϖ.ϖ ^ n) < (γ : MonoidWithZeroHom.ValueGroup₀ _) := by
  obtain ⟨y, hy⟩ := MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective (.ofClass (Valued.v (R := K)) : K →*₀ Γ₀) (γ : MonoidWithZeroHom.ValueGroup₀ _)
  have hy0 : y ≠ 0 := by
    intro h0
    apply γ.ne_zero
    rw [← hy, h0, map_zero]
  obtain ⟨N, hN⟩ := hrk (algebraMap K₀ K ϖ.ϖ) y ϖ.lt_one hy0
  refine ⟨N + 1, fun n hn => ?_⟩
  have hvy : vRestrict K y = (γ : MonoidWithZeroHom.ValueGroup₀ _) := hy
  rw [← hvy, ← v_lt_iff_vRestrict_lt, map_pow]
  calc Valued.v (algebraMap K₀ K ϖ.ϖ) ^ n ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (N + 1) :=
        pow_le_pow_right_of_le_one' ϖ.lt_one.le hn
    _ < Valued.v (algebraMap K₀ K ϖ.ϖ) ^ N := by
        rw [pow_succ]; exact mul_lt_of_lt_one_right (pow_pos ϖ.pos N) ϖ.lt_one
    _ ≤ Valued.v y := hN

noncomputable def u (ϖ : PseudoUniformizer K₀ K) (ε : ℕ → Bool) (n : ℕ) : K :=
  ∑ k ∈ Finset.range n, if ε k then algebraMap K₀ K ϖ.ϖ ^ k else 0

theorem v_term_le (ϖ : PseudoUniformizer K₀ K) (ε ε' : ℕ → Bool) (k : ℕ) :
    Valued.v ((if ε k then algebraMap K₀ K ϖ.ϖ ^ k else 0) - (if ε' k then algebraMap K₀ K ϖ.ϖ ^ k else 0)) ≤
      Valued.v (algebraMap K₀ K ϖ.ϖ) ^ k := by
  split_ifs <;> simp [map_pow]

theorem v_u_sub_u_le (ϖ : PseudoUniformizer K₀ K) (ε ε' : ℕ → Bool) {m n : ℕ} (hmn : m ≤ n)
    (h : ∀ k < m, ε k = ε' k) :
    Valued.v (u ϖ ε n - u ϖ ε' n) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ m := by
  unfold u
  rw [← Finset.sum_sub_distrib, ← Finset.sum_range_add_sum_Ico _ hmn]
  have h0 : ∑ k ∈ Finset.range m, ((if ε k then algebraMap K₀ K ϖ.ϖ ^ k else 0) -
      (if ε' k then algebraMap K₀ K ϖ.ϖ ^ k else 0)) = 0 :=
    Finset.sum_eq_zero fun k hk => by rw [h k (Finset.mem_range.1 hk), sub_self]
  rw [h0, zero_add]
  refine Valuation.map_sum_le _ fun k hk => (v_term_le ϖ ε ε' k).trans ?_
  exact pow_le_pow_right_of_le_one' ϖ.lt_one.le (Finset.mem_Ico.1 hk).1

theorem v_u_sub_u_self_le (ϖ : PseudoUniformizer K₀ K) (ε : ℕ → Bool) {m n : ℕ} (hmn : m ≤ n) :
    Valued.v (u ϖ ε n - u ϖ ε m) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ m := by
  unfold u
  rw [← Finset.sum_range_add_sum_Ico _ hmn, add_sub_cancel_left]
  refine Valuation.map_sum_le _ fun k hk => ?_
  have := v_term_le ϖ ε (fun _ => false) k
  simp only [Bool.false_eq_true, ↓reduceIte, sub_zero] at this
  exact this.trans (pow_le_pow_right_of_le_one' ϖ.lt_one.le (Finset.mem_Ico.1 hk).1)

theorem cauchySeq_u [CompleteSpace K] (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y) (ε : ℕ → Bool) :
    CauchySeq (u ϖ ε) := by
  rw [CauchySeq, Valued.cauchy_iff]
  refine ⟨Filter.map_neBot, fun γ => ?_⟩
  obtain ⟨N, hN⟩ := exists_pow_lt ϖ hrk γ
  refine ⟨u ϖ ε '' Set.Ici N, Filter.image_mem_map (Filter.Ici_mem_atTop N), ?_⟩
  rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩
  change vRestrict K (u ϖ ε b - u ϖ ε a) < _
  rcases le_total a b with hab | hab
  · refine lt_of_le_of_lt ?_ (hN a ha)
    rw [← v_le_iff_vRestrict_le, map_pow]
    exact v_u_sub_u_self_le ϖ ε hab
  · refine lt_of_le_of_lt ?_ (hN b hb)
    rw [← v_le_iff_vRestrict_le, map_pow, Valuation.map_sub_swap]
    exact v_u_sub_u_self_le ϖ ε hab

noncomputable def L [CompleteSpace K] (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y) (ε : ℕ → Bool) : K :=
  (cauchySeq_tendsto_of_complete (cauchySeq_u ϖ hrk ε)).choose

theorem tendsto_L [CompleteSpace K] (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y) (ε : ℕ → Bool) :
    Tendsto (u ϖ ε) atTop (𝓝 (L ϖ hrk ε)) :=
  (cauchySeq_tendsto_of_complete (cauchySeq_u ϖ hrk ε)).choose_spec

theorem L_injective [CompleteSpace K] (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y) :
    Function.Injective (L ϖ hrk) := by
  classical
  intro ε ε' hL
  by_contra hne
  have hex : ∃ k, ε k ≠ ε' k := by
    by_contra h; push_neg at h; exact hne (funext h)
  let k₀ := Nat.find hex
  have hk₀ : ε k₀ ≠ ε' k₀ := Nat.find_spec hex
  have hlt : ∀ k < k₀, ε k = ε' k := fun k hk => by
    have := Nat.find_min hex hk; push_neg at this; exact this
  set π := algebraMap K₀ K ϖ.ϖ with hπ

  have hval : ∀ n, k₀ + 1 ≤ n → Valued.v (u ϖ ε n - u ϖ ε' n) = Valued.v π ^ k₀ := by
    intro n hn
    have hsplit : u ϖ ε n - u ϖ ε' n =
        ((if ε k₀ then π ^ k₀ else 0) - (if ε' k₀ then π ^ k₀ else 0)) +
        ∑ k ∈ Finset.Ico (k₀ + 1) n, ((if ε k then π ^ k else 0) - (if ε' k then π ^ k else 0)) := by
      unfold u
      rw [← Finset.sum_sub_distrib, ← Finset.sum_range_add_sum_Ico _ hn, Finset.sum_range_succ,
        Finset.sum_eq_zero (fun k hk => by rw [hlt k (Finset.mem_range.1 hk), sub_self]), zero_add]
    have hlead : Valued.v ((if ε k₀ then π ^ k₀ else 0) - (if ε' k₀ then π ^ k₀ else 0)) = Valued.v π ^ k₀ := by
      rcases Bool.eq_false_or_eq_true (ε k₀) with h1 | h1 <;>
        rcases Bool.eq_false_or_eq_true (ε' k₀) with h2 | h2 <;>
        simp_all [map_pow]
    have htail : Valued.v (∑ k ∈ Finset.Ico (k₀ + 1) n,
        ((if ε k then π ^ k else 0) - (if ε' k then π ^ k else 0))) < Valued.v π ^ k₀ := by
      refine Valuation.map_sum_lt _ (pow_ne_zero _ ϖ.pos.ne') fun k hk => ?_
      refine lt_of_le_of_lt (v_term_le ϖ ε ε' k) ?_
      calc Valued.v (algebraMap K₀ K ϖ.ϖ) ^ k ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (k₀ + 1) :=
            pow_le_pow_right_of_le_one' ϖ.lt_one.le (Finset.mem_Ico.1 hk).1
        _ < Valued.v π ^ k₀ := by rw [pow_succ]; exact mul_lt_of_lt_one_right (pow_pos ϖ.pos _) ϖ.lt_one
    rw [hsplit, Valuation.map_add_eq_of_lt_left _ (by rwa [hlead]), hlead]

  have hmem : L ϖ hrk ε - L ϖ hrk ε' ∈ {x : K | vRestrict K x = vRestrict K (π ^ k₀)} := by
    refine (Valued.isClosed_sphere K (vRestrict K (π ^ k₀))).mem_of_tendsto
      ((tendsto_L ϖ hrk ε).sub (tendsto_L ϖ hrk ε')) ?_
    rw [Filter.eventually_atTop]
    refine ⟨k₀ + 1, fun n hn => ?_⟩
    show vRestrict K (u ϖ ε n - u ϖ ε' n) = vRestrict K (π ^ k₀)
    exact (Valuation.isEquiv_restrict (Valued.v (R := K))).val_eq.1 (by rw [hval n hn, map_pow])
  have hv : Valued.v (L ϖ hrk ε - L ϖ hrk ε') = Valued.v (π ^ k₀) :=
    (Valuation.isEquiv_restrict (Valued.v (R := K))).val_eq.2 hmem
  have hne0 : Valued.v (L ϖ hrk ε - L ϖ hrk ε') ≠ 0 := by
    rw [hv, map_pow]; exact pow_ne_zero _ ϖ.pos.ne'
  rw [hL, sub_self, map_zero] at hne0
  exact hne0 rfl

theorem not_countable [CompleteSpace K] (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y) : ¬ Countable K := by
  classical
  intro hc
  obtain ⟨f, hf⟩ := Countable.exists_injective_nat K
  refine Function.cantor_injective (fun S : Set ℕ => f (L ϖ hrk (fun n => decide (n ∈ S)))) ?_
  intro S T hST
  have h := L_injective ϖ hrk (hf hST)
  ext n
  have := congrFun h n
  simpa using this

theorem not_countable_upperHalfPlane [CompleteSpace K] (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    {z : K} (hz : z ∈ upperHalfPlane K₀ K) : ¬ (upperHalfPlane K₀ K).Countable := by
  intro hΩ
  apply not_countable ϖ hrk
  have hA : (Set.range (algebraMap K₀ K)).Countable := by
    refine (hΩ.image fun w => w - z).mono ?_
    rintro _ ⟨t, rfl⟩
    refine ⟨z + algebraMap K₀ K t, ?_, by ring⟩
    rw [mem_upperHalfPlane_iff]
    intro s hs
    rw [mem_upperHalfPlane_iff] at hz
    exact hz (s - t) (by rw [map_sub, hs]; ring)
  have huniv : (Set.univ : Set K) = upperHalfPlane K₀ K ∪ Set.range (algebraMap K₀ K) := by
    ext x
    simp only [Set.mem_univ, Set.mem_union, true_iff]
    by_cases hx : x ∈ Set.range (algebraMap K₀ K)
    · exact Or.inr hx
    · exact Or.inl hx
  rw [← Set.countable_univ_iff, huniv]
  exact hΩ.union hA

theorem pmoebius_inv_apply {G : Type} [Group G] [DecidableEq K] (ρ : G →* PGL(2, K₀)) (γ : G) {x y : K}
    (hx : x ∈ upperHalfPlane K₀ K) (h : pmoebius K₀ (ρ γ) x = y) : pmoebius K₀ (ρ γ⁻¹) y = x := by
  rw [← h, map_inv, ← pmoebius_mul K₀ hx, inv_mul_cancel, pmoebius_one]

end AvoidPt

open AvoidPt in
theorem solution_prime
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    {G : Type} [Group G] [Countable G] (ρ : G →* PGL(2, K₀))
    {a b : K} (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K) :
    ∃ z₀ : K, z₀ ∈ upperHalfPlane K₀ K ∧
      (∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) ∧ (∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z₀) := by
  have hS : (Set.range (fun γ : G => pmoebius K₀ (ρ γ) a) ∪ Set.range (fun γ : G => pmoebius K₀ (ρ γ) b)).Countable :=
    (Set.countable_range _).union (Set.countable_range _)
  have hnot : ¬ upperHalfPlane K₀ K ⊆ Set.range (fun γ : G => pmoebius K₀ (ρ γ) a) ∪ Set.range (fun γ : G => pmoebius K₀ (ρ γ) b) :=
    fun h => not_countable_upperHalfPlane ϖ hrk ha (hS.mono h)
  obtain ⟨z₀, hz₀, hnz⟩ := Set.not_subset.1 hnot
  refine ⟨z₀, hz₀, fun γ h => hnz (Or.inl ⟨γ, h⟩), fun γ h => hnz (Or.inr ⟨γ, h⟩)⟩

open AvoidPt in
theorem solution
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    {G : Type} [Group G] [Countable G] (ρ : G →* PGL(2, K₀))
    {z : K} (hz : z ∈ upperHalfPlane K₀ K) :
    ∃ b z₀ : K, b ∈ upperHalfPlane K₀ K ∧ z₀ ∈ upperHalfPlane K₀ K ∧
      (∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z) ∧ (∀ γ : G, pmoebius K₀ (ρ γ) z ≠ z₀) ∧
      (∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z₀) := by

  have hS₁ : (Set.range (fun γ : G => pmoebius K₀ (ρ γ⁻¹) z)).Countable := Set.countable_range _
  obtain ⟨b, hb, hnb⟩ := Set.not_subset.1 (fun h => not_countable_upperHalfPlane ϖ hrk hz (hS₁.mono h))
  have hbz : ∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z := fun γ h => hnb ⟨γ, pmoebius_inv_apply ρ γ hb h⟩
  obtain ⟨z₀, hz₀, h1, h2⟩ := solution_prime K₀ K ϖ hrk ρ hz hb
  exact ⟨b, z₀, hb, hz₀, hbz, h1, h2⟩

end S_CerednikDrinfeld_Omega_exists_mem_upperHalfPlane_forall_pmoebius_ne_of_countable_of_archimedean
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_exists_mem_upperHalfPlane_forall_pmoebius_ne_of_countable_of_archimedean (solution)
