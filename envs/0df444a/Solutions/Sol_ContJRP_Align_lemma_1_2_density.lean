-- Prove2me | solution 1 for ContJRP.Align.lemma_1_2_density
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T22:06:04.382311+00:00
-- url     : https://prove2.me/submissions/1be9eb9b-e173-452e-9cf1-e686ad95515e

import Mathlib
import Definitions.Def_ContJRP_Align_Model

open ContJRP.Align
open Classical

/-- Membership in `M_{t,Δ}` for `t > 0`, `Δ ≥ 0`. -/
theorem jrp12_mem_mult (t Δ x : ℝ) (ht : 0 < t) (hΔ : 0 ≤ Δ) :
    x ∈ multiplesUpTo t Δ ↔ ∃ k : ℕ, x = k * t ∧ x ≤ Δ := by
  unfold multiplesUpTo
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k, rfl, ?_⟩
    have h1 : (k : ℝ) ≤ Δ / t :=
      le_trans (by exact_mod_cast (Nat.lt_succ_iff.mp hk)) (Nat.floor_le (div_nonneg hΔ ht.le))
    rwa [le_div_iff₀ ht] at h1
  · rintro ⟨k, rfl, hk⟩
    refine ⟨k, ?_, rfl⟩
    have : (k : ℝ) ≤ Δ / t := by rwa [le_div_iff₀ ht]
    have := Nat.le_floor this
    omega

/-- The common multiples have a least element when nonempty. -/
theorem jrp12_isLeast {ι : Type*} (N : Finset ι) (T : ι → ℝ) (hT : ∀ i ∈ N, 0 < T i)
    (hN : N.Nonempty) (hne : (commonMultiples N T).Nonempty) :
    ∃ M, IsLeast (commonMultiples N T) M := by
  obtain ⟨i0, hi0⟩ := hN
  have hex : ∃ k : ℕ, (k : ℝ) * T i0 ∈ commonMultiples N T := by
    obtain ⟨c, hc⟩ := hne
    obtain ⟨k, hk⟩ := hc.2 i0 hi0
    exact ⟨k, hk ▸ hc⟩
  refine ⟨(Nat.find hex : ℝ) * T i0, Nat.find_spec hex, ?_⟩
  intro c hc
  obtain ⟨k, hk⟩ := hc.2 i0 hi0
  have hkm : Nat.find hex ≤ k := Nat.find_min' hex (hk ▸ hc)
  rw [hk]
  have : (Nat.find hex : ℝ) ≤ k := by exact_mod_cast hkm
  exact mul_le_mul_of_nonneg_right this (hT i0 hi0).le

/-- Every common multiple is a natural multiple of the least one. -/
theorem jrp12_dvd {ι : Type*} (N : Finset ι) (T : ι → ℝ) (hT : ∀ i ∈ N, 0 < T i)
    (hN : N.Nonempty) (M : ℝ) (hM : IsLeast (commonMultiples N T) M) (x : ℝ)
    (hx : x ∈ commonMultiples N T) : ∃ j : ℕ, x = j * M := by
  have hMpos : 0 < M := hM.1.1
  set j := ⌊x / M⌋₊ with hj
  refine ⟨j, ?_⟩
  by_contra hne
  set r := x - j * M with hr
  have hjle : (j : ℝ) * M ≤ x := by
    have := Nat.floor_le (div_nonneg hx.1.le hMpos.le)
    rw [← hj, le_div_iff₀ hMpos] at this; exact this
  have hrpos : 0 < r := by
    rcases lt_or_eq_of_le hjle with h | h
    · rw [hr]; linarith
    · exact absurd h.symm hne
  have hrlt : r < M := by
    have := Nat.lt_floor_add_one (x / M)
    rw [← hj, div_lt_iff₀ hMpos] at this
    rw [hr]; linarith
  have hrcm : r ∈ commonMultiples N T := by
    refine ⟨hrpos, ?_⟩
    intro i hi
    obtain ⟨a, ha⟩ := hx.2 i hi
    obtain ⟨b, hb⟩ := hM.1.2 i hi
    have hTi := hT i hi
    -- r = (a - j b) T_i with a - j b > 0
    have hreq : r = ((a : ℤ) - (j : ℤ) * b : ℤ) * T i := by
      rw [hr, ha, hb]; push_cast; ring
    have hzpos : (0 : ℤ) < (a : ℤ) - (j : ℤ) * b := by
      have : (0 : ℝ) < (((a : ℤ) - (j : ℤ) * b : ℤ) : ℝ) := by
        rw [hreq] at hrpos
        exact pos_of_mul_pos_left hrpos hTi.le
      exact_mod_cast this
    refine ⟨((a : ℤ) - (j : ℤ) * b).toNat, ?_⟩
    rw [hreq]
    congr 1
    have : (((a : ℤ) - (j : ℤ) * b).toNat : ℤ) = (a : ℤ) - (j : ℤ) * b := Int.toNat_of_nonneg hzpos.le
    exact_mod_cast this.symm
  exact absurd (hM.2 hrcm) (not_le.mpr hrlt)

theorem jrp12_mem_inf {ι : Type*} (N : Finset ι) (hN : N.Nonempty) (S : ι → Finset ℝ) (x : ℝ) :
    x ∈ N.inf' hN S ↔ ∀ i ∈ N, x ∈ S i := by
  rw [← Finset.singleton_subset_iff, ← Finset.le_iff_subset, Finset.le_inf'_iff]
  simp

/-- The count of common multiples in `[0, Δ]` is `Δ / M_N` up to an additive error in `[0, 1]`. -/
theorem jrp12_count {ι : Type*} (N : Finset ι) (T : ι → ℝ) (hT : ∀ i ∈ N, 0 < T i)
    (hN : N.Nonempty) (Δ : ℝ) (hΔ : 0 ≤ Δ) :
    |((N.inf' hN (fun i => multiplesUpTo (T i) Δ)).card : ℝ) - Δ * invLcm N T| ≤ 1 := by
  obtain ⟨i0, hi0⟩ := id hN
  by_cases hne : (commonMultiples N T).Nonempty
  · obtain ⟨M, hM⟩ := jrp12_isLeast N T hT ⟨i0, hi0⟩ hne
    have hMpos : 0 < M := hM.1.1
    have hinv : invLcm N T = M⁻¹ := by
      unfold invLcm; rw [if_pos hne, hM.csInf_eq]
    have hset : N.inf' hN (fun i => multiplesUpTo (T i) Δ) = multiplesUpTo M Δ := by
      ext x
      rw [jrp12_mem_inf, jrp12_mem_mult M Δ x hMpos hΔ]
      constructor
      · intro h
        have h0 := (jrp12_mem_mult _ _ _ (hT i0 hi0) hΔ).mp (h i0 hi0)
        obtain ⟨k0, hk0, hxΔ⟩ := h0
        rcases Nat.eq_zero_or_pos k0 with hk | hk
        · exact ⟨0, by rw [hk0, hk]; simp, hxΔ⟩
        · have hxpos : 0 < x := by
            rw [hk0]; have := hT i0 hi0; positivity
          have hxcm : x ∈ commonMultiples N T := by
            refine ⟨hxpos, fun i hi => ?_⟩
            obtain ⟨k, hk, -⟩ := (jrp12_mem_mult _ _ _ (hT i hi) hΔ).mp (h i hi)
            exact ⟨k, hk⟩
          obtain ⟨j, hj⟩ := jrp12_dvd N T hT ⟨i0, hi0⟩ M hM x hxcm
          exact ⟨j, hj, hxΔ⟩
      · rintro ⟨k, hk, hxΔ⟩ i hi
        rw [jrp12_mem_mult _ _ _ (hT i hi) hΔ]
        obtain ⟨b, hb⟩ := hM.1.2 i hi
        exact ⟨k * b, by rw [hk, hb]; push_cast; ring, hxΔ⟩
    have hcard : (multiplesUpTo M Δ).card = ⌊Δ / M⌋₊ + 1 := by
      unfold multiplesUpTo
      rw [Finset.card_image_of_injective, Finset.card_range]
      intro a b hab
      have := mul_right_cancel₀ (ne_of_gt hMpos) hab
      exact_mod_cast this
    rw [hset, hcard, hinv, ← div_eq_mul_inv]
    push_cast
    have h1 := Nat.floor_le (div_nonneg hΔ hMpos.le)
    have h2 := Nat.lt_floor_add_one (Δ / M)
    rw [abs_le]; constructor <;> linarith
  · have hinv : invLcm N T = 0 := by unfold invLcm; rw [if_neg hne]
    have hset : N.inf' hN (fun i => multiplesUpTo (T i) Δ) = {0} := by
      ext x
      rw [jrp12_mem_inf, Finset.mem_singleton]
      constructor
      · intro h
        by_contra hx0
        apply hne
        obtain ⟨k0, hk0, -⟩ := (jrp12_mem_mult _ _ _ (hT i0 hi0) hΔ).mp (h i0 hi0)
        have hxpos : 0 < x := by
          rcases Nat.eq_zero_or_pos k0 with hk | hk
          · exact absurd (by rw [hk0, hk]; simp) hx0
          · rw [hk0]; have := hT i0 hi0; positivity
        refine ⟨x, hxpos, fun i hi => ?_⟩
        obtain ⟨k, hk, -⟩ := (jrp12_mem_mult _ _ _ (hT i hi) hΔ).mp (h i hi)
        exact ⟨k, hk⟩
      · rintro rfl i hi
        rw [jrp12_mem_mult _ _ _ (hT i hi) hΔ]
        exact ⟨0, by simp, hΔ⟩
    rw [hset, hinv, Finset.card_singleton]
    norm_num

theorem solution {ι : Type*} (s : Finset ι) (T : ι → ℝ) (hT : ∀ i ∈ s, 0 < T i) :
    Filter.Tendsto (fun Δ : ℝ => (numOrders s T Δ : ℝ) / Δ) Filter.atTop
      (nhds (∑ N ∈ s.powerset.filter (fun N => N.Nonempty),
        (-1 : ℝ) ^ (N.card + 1) * invLcm N T)) := by
  set P := s.powerset.filter (fun N => N.Nonempty) with hP
  set L := ∑ N ∈ P, (-1 : ℝ) ^ (N.card + 1) * invLcm N T with hL
  set c : ℝ := (P.card : ℝ) with hc
  -- the key estimate
  have hkey : ∀ Δ : ℝ, 0 ≤ Δ → |(numOrders s T Δ : ℝ) - Δ * L| ≤ c := by
    intro Δ hΔ
    have hie := Finset.inclusion_exclusion_card_biUnion s (fun i => multiplesUpTo (T i) Δ)
    have hnum : (numOrders s T Δ : ℝ) = ∑ t : P, (-1 : ℝ) ^ (t.1.card + 1) *
        ((t.1.inf' (Finset.mem_filter.1 t.2).2 (fun i => multiplesUpTo (T i) Δ)).card : ℝ) := by
      unfold numOrders
      have := congrArg (Int.cast (R := ℝ)) hie
      rw [show ((s.biUnion fun i => multiplesUpTo (T i) Δ).card : ℝ) =
          (((s.biUnion fun i => multiplesUpTo (T i) Δ).card : ℤ) : ℝ) by norm_cast]
      convert this using 1
      push_cast
      rfl
    have hL' : Δ * L = ∑ t : P, (-1 : ℝ) ^ (t.1.card + 1) * (Δ * invLcm t.1 T) := by
      rw [hL, Finset.mul_sum]
      rw [← Finset.sum_coe_sort P]
      apply Finset.sum_congr rfl
      intro t _; ring
    rw [hnum, hL', ← Finset.sum_sub_distrib]
    calc |∑ t : P, ((-1 : ℝ) ^ (t.1.card + 1) *
            ((t.1.inf' (Finset.mem_filter.1 t.2).2 (fun i => multiplesUpTo (T i) Δ)).card : ℝ) -
            (-1 : ℝ) ^ (t.1.card + 1) * (Δ * invLcm t.1 T))|
        ≤ ∑ t : P, |(-1 : ℝ) ^ (t.1.card + 1) *
            ((t.1.inf' (Finset.mem_filter.1 t.2).2 (fun i => multiplesUpTo (T i) Δ)).card : ℝ) -
            (-1 : ℝ) ^ (t.1.card + 1) * (Δ * invLcm t.1 T)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _t : P, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro t _
          rw [← mul_sub, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
          have ht := Finset.mem_filter.1 t.2
          exact jrp12_count t.1 T (fun i hi => hT i (Finset.mem_powerset.1 ht.1 hi)) ht.2 Δ hΔ
      _ = c := by rw [hc]; simp
  -- squeeze
  have hlo : Filter.Tendsto (fun Δ : ℝ => L - c / Δ) Filter.atTop (nhds L) := by
    have := (tendsto_const_nhds (x := c)).div_atTop Filter.tendsto_id
    simpa using (tendsto_const_nhds (x := L)).sub this
  have hhi : Filter.Tendsto (fun Δ : ℝ => L + c / Δ) Filter.atTop (nhds L) := by
    have := (tendsto_const_nhds (x := c)).div_atTop Filter.tendsto_id
    simpa using (tendsto_const_nhds (x := L)).add this
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with Δ hΔ
    have h := (abs_le.mp (hkey Δ hΔ.le)).1
    have e : L - c / Δ = (Δ * L - c) / Δ := by field_simp
    rw [e]
    exact div_le_div_of_nonneg_right (by linarith) hΔ.le
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with Δ hΔ
    have h := (abs_le.mp (hkey Δ hΔ.le)).2
    have e : L + c / Δ = (Δ * L + c) / Δ := by field_simp
    rw [e]
    exact div_le_div_of_nonneg_right (by linarith) hΔ.le
