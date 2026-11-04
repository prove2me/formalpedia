-- Prove2me | solution 1 for ContJRP.Align.lemma_3_2_crossing
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T22:12:02.941712+00:00
-- url     : https://prove2.me/submissions/a350896a-6c58-49e3-8a8c-59a2b421d920

import Mathlib
import Definitions.Def_ContJRP_Align_Model
import Definitions.Def_ContJRP_Align_Alignment
import Definitions.Def_ContJRP_Align_Policy
import Theorems.Thm_ContJRP_Align_observation_2_3_first_segment_active

open ContJRP.Align
open Classical

/-- Membership in `M_{t,Δ}` for `t > 0`, `Δ ≥ 0`. -/
theorem jrp32_mem_mult (t Δ x : ℝ) (ht : 0 < t) (hΔ : 0 ≤ Δ) :
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
theorem jrp32_isLeast {ι : Type*} (N : Finset ι) (T : ι → ℝ) (hT : ∀ i ∈ N, 0 < T i)
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
theorem jrp32_dvd {ι : Type*} (N : Finset ι) (T : ι → ℝ) (hT : ∀ i ∈ N, 0 < T i)
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

theorem jrp32_mem_inf {ι : Type*} (N : Finset ι) (hN : N.Nonempty) (S : ι → Finset ℝ) (x : ℝ) :
    x ∈ N.inf' hN S ↔ ∀ i ∈ N, x ∈ S i := by
  rw [← Finset.singleton_subset_iff, ← Finset.le_iff_subset, Finset.le_inf'_iff]
  simp

/-- The count of common multiples in `[0, Δ]` is `Δ / M_N` up to an additive error in `[0, 1]`. -/
theorem jrp32_count {ι : Type*} (N : Finset ι) (T : ι → ℝ) (hT : ∀ i ∈ N, 0 < T i)
    (hN : N.Nonempty) (Δ : ℝ) (hΔ : 0 ≤ Δ) :
    |((N.inf' hN (fun i => multiplesUpTo (T i) Δ)).card : ℝ) - Δ * invLcm N T| ≤ 1 := by
  obtain ⟨i0, hi0⟩ := id hN
  by_cases hne : (commonMultiples N T).Nonempty
  · obtain ⟨M, hM⟩ := jrp32_isLeast N T hT ⟨i0, hi0⟩ hne
    have hMpos : 0 < M := hM.1.1
    have hinv : invLcm N T = M⁻¹ := by
      unfold invLcm; rw [if_pos hne, hM.csInf_eq]
    have hset : N.inf' hN (fun i => multiplesUpTo (T i) Δ) = multiplesUpTo M Δ := by
      ext x
      rw [jrp32_mem_inf, jrp32_mem_mult M Δ x hMpos hΔ]
      constructor
      · intro h
        have h0 := (jrp32_mem_mult _ _ _ (hT i0 hi0) hΔ).mp (h i0 hi0)
        obtain ⟨k0, hk0, hxΔ⟩ := h0
        rcases Nat.eq_zero_or_pos k0 with hk | hk
        · exact ⟨0, by rw [hk0, hk]; simp, hxΔ⟩
        · have hxpos : 0 < x := by
            rw [hk0]; have := hT i0 hi0; positivity
          have hxcm : x ∈ commonMultiples N T := by
            refine ⟨hxpos, fun i hi => ?_⟩
            obtain ⟨k, hk, -⟩ := (jrp32_mem_mult _ _ _ (hT i hi) hΔ).mp (h i hi)
            exact ⟨k, hk⟩
          obtain ⟨j, hj⟩ := jrp32_dvd N T hT ⟨i0, hi0⟩ M hM x hxcm
          exact ⟨j, hj, hxΔ⟩
      · rintro ⟨k, hk, hxΔ⟩ i hi
        rw [jrp32_mem_mult _ _ _ (hT i hi) hΔ]
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
      rw [jrp32_mem_inf, Finset.mem_singleton]
      constructor
      · intro h
        by_contra hx0
        apply hne
        obtain ⟨k0, hk0, -⟩ := (jrp32_mem_mult _ _ _ (hT i0 hi0) hΔ).mp (h i0 hi0)
        have hxpos : 0 < x := by
          rcases Nat.eq_zero_or_pos k0 with hk | hk
          · exact absurd (by rw [hk0, hk]; simp) hx0
          · rw [hk0]; have := hT i0 hi0; positivity
        refine ⟨x, hxpos, fun i hi => ?_⟩
        obtain ⟨k, hk, -⟩ := (jrp32_mem_mult _ _ _ (hT i hi) hΔ).mp (h i hi)
        exact ⟨k, hk⟩
      · rintro rfl i hi
        rw [jrp32_mem_mult _ _ _ (hT i hi) hΔ]
        exact ⟨0, by simp, hΔ⟩
    rw [hset, hinv, Finset.card_singleton]
    norm_num


/-- The number of common multiples of two misaligned intervals `x, y ≥ m > 0` in `[0, Δ]`. -/
theorem jrp32_pair (R : ℕ → ℝ) (ℓ₁ ℓ₂ : ℕ) (hne : ℓ₁ ≠ ℓ₂) (Ψ m : ℝ) (hΨ : 0 < Ψ) (hm : 0 < m)
    (h1 : m ≤ R ℓ₁) (h2 : m ≤ R ℓ₂) (hmis : Misaligned Ψ (R ℓ₁) (R ℓ₂)) (Δ : ℝ) (hΔ : 0 ≤ Δ) :
    (({ℓ₁, ℓ₂} : Finset ℕ).inf' (Finset.insert_nonempty _ _)
      (fun ℓ => multiplesUpTo (R ℓ) Δ)).card ≤ Δ / (Ψ * m) + 1 := by
  have hpos : ∀ ℓ ∈ ({ℓ₁, ℓ₂} : Finset ℕ), 0 < R ℓ := by
    intro ℓ hℓ
    rcases Finset.mem_insert.1 hℓ with h | h
    · rw [h]; linarith
    · rw [Finset.mem_singleton.1 h]; linarith
  have hc := jrp32_count ({ℓ₁, ℓ₂} : Finset ℕ) R hpos (Finset.insert_nonempty _ _) Δ hΔ
  have hinv : invLcm ({ℓ₁, ℓ₂} : Finset ℕ) R ≤ 1 / (Ψ * m) := by
    by_cases hcm : (commonMultiples ({ℓ₁, ℓ₂} : Finset ℕ) R).Nonempty
    · obtain ⟨M, hM⟩ := jrp32_isLeast _ R hpos (Finset.insert_nonempty _ _) hcm
      have hMpos : 0 < M := hM.1.1
      have hi : invLcm ({ℓ₁, ℓ₂} : Finset ℕ) R = M⁻¹ := by
        unfold invLcm; rw [if_pos hcm, hM.csInf_eq]
      obtain ⟨a, ha⟩ := hM.1.2 ℓ₁ (Finset.mem_insert_self _ _)
      obtain ⟨b, hb⟩ := hM.1.2 ℓ₂ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      have hR1 : 0 < R ℓ₁ := by linarith
      have hR2 : 0 < R ℓ₂ := by linarith
      have ha0 : 0 < a := by
        rcases Nat.eq_zero_or_pos a with h | h
        · rw [h] at ha; simp at ha; linarith
        · exact h
      have hb0 : 0 < b := by
        rcases Nat.eq_zero_or_pos b with h | h
        · rw [h] at hb; simp at hb; linarith
        · exact h
      have hbig : Ψ * m < M := by
        by_contra hcon
        push Not at hcon
        apply hmis a b ha0 _ hb0 _ (by rw [← ha, ← hb])
        · by_contra h; push Not at h
          have : Ψ * m < a * R ℓ₁ := by
            calc Ψ * m ≤ Ψ * R ℓ₁ := mul_le_mul_of_nonneg_left h1 hΨ.le
              _ < a * R ℓ₁ := mul_lt_mul_of_pos_right h hR1
          linarith
        · by_contra h; push Not at h
          have : Ψ * m < b * R ℓ₂ := by
            calc Ψ * m ≤ Ψ * R ℓ₂ := mul_le_mul_of_nonneg_left h2 hΨ.le
              _ < b * R ℓ₂ := mul_lt_mul_of_pos_right h hR2
          linarith
      rw [hi, ← one_div]
      exact one_div_le_one_div_of_le (by positivity) hbig.le
    · have : invLcm ({ℓ₁, ℓ₂} : Finset ℕ) R = 0 := by unfold invLcm; rw [if_neg hcm]
      rw [this]; positivity
  have := (abs_le.mp hc).2
  have h3 : Δ * invLcm ({ℓ₁, ℓ₂} : Finset ℕ) R ≤ Δ / (Ψ * m) := by
    rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hinv hΔ
  linarith

theorem solution (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    {n : ℕ} [NeZero n] (Tstar : Fin n → ℝ) (hTstar : ∀ i, 0 < Tstar i)
    (Tt : ℝ) (hTt1 : (1 - ε / 2) * tmin Tstar ≤ Tt) (hTt2 : Tt ≤ tmin Tstar)
    (Rstar : ℕ → ℝ) (hR : IsRepChoice ε Tt Tstar Rstar)
    (R : ℕ → ℝ) (hfeas : IsLPFeasible ε Tt Tstar Rstar R)
    (hmis : CrossMisaligned ε Tt Tstar Rstar R) :
    ∀ Δ : ℝ, 0 ≤ Δ → ((termII ε Tt Tstar Rstar R Δ : ℤ) : ℝ) ≤
      ε * (numOrders (active ε Tt Tstar) Rstar Δ : ℝ) + 2 ^ (active ε Tt Tstar).card := by
  intro Δ hΔ
  set Aa := active ε Tt Tstar with hAa
  set a := Aa.card with ha
  set Ψ := Psi ε with hΨdef
  have htmin_pos : 0 < tmin Tstar := by
    unfold tmin
    rw [Finset.lt_inf'_iff]
    intro i _; exact hTstar i
  have hTt_pos : 0 < Tt := by
    have : 0 < (1 - ε / 2) * tmin Tstar := mul_pos (by linarith) htmin_pos
    linarith
  have h0 : 0 ∈ Aa := observation_2_3_first_segment_active ε hε0 hε1 Tstar hTstar Tt hTt1 hTt2
  have ha1 : 1 ≤ a := Finset.card_pos.mpr ⟨0, h0⟩
  -- representatives are at least `Tt`
  have hRge : ∀ ℓ ∈ Aa, Tt ≤ R ℓ := by
    intro ℓ hℓ
    have := (hfeas.1 ℓ hℓ).1
    have : Tt ≤ (1 + ε) ^ ℓ * Tt := le_mul_of_one_le_left hTt_pos.le (one_le_pow₀ (by linarith))
    linarith
  -- `Ψ ≥ 2 · 2^a / ε`
  have haL : a ≤ numSegments ε := by
    have : Aa ⊆ Finset.range (numSegments ε) := Finset.filter_subset _ _
    simpa using Finset.card_le_card this
  have hΨ : 2 * 2 ^ a / ε ≤ Ψ := by
    rw [hΨdef]; unfold Psi
    apply div_le_div_of_nonneg_right _ hε0.le
    have hL1 : (1 : ℝ) ≤ (numSegments ε : ℝ) := by exact_mod_cast le_trans ha1 haL
    have hL2 : (1 : ℝ) ≤ (numSegments ε : ℝ) ^ 2 := by nlinarith
    have hp : (2 : ℝ) ^ a ≤ 2 ^ numSegments ε := pow_le_pow_right₀ (by norm_num) haL
    have : (0 : ℝ) < 2 ^ a := by positivity
    nlinarith
  have hΨpos : 0 < Ψ := lt_of_lt_of_le (by positivity) hΨ
  -- `N(R*, Δ) ≥ Δ / (2 Tt)`
  have hNstar : Δ / (2 * Tt) ≤ (numOrders Aa Rstar Δ : ℝ) := by
    obtain ⟨i, hi, hseg⟩ := hR 0 h0
    unfold seg at hseg
    simp only [pow_zero, one_mul, zero_add, pow_one] at hseg
    have hr0 : 0 < Rstar 0 := by rw [hi]; exact hTstar i
    have hr1 : Rstar 0 ≤ 2 * Tt := by rw [hi]; nlinarith [hseg.2]
    have hc1 : (multiplesUpTo (Rstar 0) Δ).card ≤ numOrders Aa Rstar Δ := by
      unfold numOrders
      exact Finset.card_le_card
        (Finset.subset_biUnion_of_mem (fun ℓ => multiplesUpTo (Rstar ℓ) Δ) h0)
    have hc2 : (multiplesUpTo (Rstar 0) Δ).card = ⌊Δ / Rstar 0⌋₊ + 1 := by
      unfold multiplesUpTo
      rw [Finset.card_image_of_injective, Finset.card_range]
      intro p q hpq
      have := mul_right_cancel₀ (ne_of_gt hr0) hpq
      exact_mod_cast this
    rw [hc2] at hc1
    have : Δ / Rstar 0 ≤ (numOrders Aa Rstar Δ : ℝ) := by
      refine le_trans (Nat.lt_floor_add_one _).le ?_
      exact_mod_cast hc1
    refine le_trans ?_ this
    exact div_le_div_of_nonneg_left hΔ hr0 hr1
  -- each crossing term
  set X := Aa.powerset.filter (fun A => A.Nonempty ∧ ¬ IsUncrossing ε Tt Tstar Rstar A) with hX
  have hterm : ∀ A ∈ X, ((interMultiples A R Δ).card : ℝ) ≤ Δ / (Ψ * Tt) + 1 := by
    intro A hA
    rw [hX, Finset.mem_filter, Finset.mem_powerset] at hA
    obtain ⟨hsub, hne, hnu⟩ := hA
    have : ∃ ℓ₁ ∈ A, ∃ ℓ₂ ∈ A, ¬ (alignGraph ε Tt Tstar Rstar).Reachable ℓ₁ ℓ₂ := by
      by_contra h
      push Not at h
      exact hnu ⟨hne, h⟩
    obtain ⟨ℓ₁, h1, ℓ₂, h2, hnr⟩ := this
    have hne12 : ℓ₁ ≠ ℓ₂ := by
      intro e; rw [e] at hnr; exact hnr (SimpleGraph.Reachable.refl _)
    have hmis' := hmis ℓ₁ (hsub h1) ℓ₂ (hsub h2) hnr
    have hpair := jrp32_pair R ℓ₁ ℓ₂ hne12 Ψ Tt hΨpos hTt_pos (hRge ℓ₁ (hsub h1))
      (hRge ℓ₂ (hsub h2)) hmis' Δ hΔ
    refine le_trans ?_ hpair
    have : interMultiples A R Δ ⊆ ({ℓ₁, ℓ₂} : Finset ℕ).inf' (Finset.insert_nonempty _ _)
        (fun ℓ => multiplesUpTo (R ℓ) Δ) := by
      intro x hx
      unfold interMultiples at hx
      rw [Finset.mem_filter] at hx
      rw [jrp32_mem_inf]
      intro ℓ hℓ
      rcases Finset.mem_insert.1 hℓ with h | h
      · rw [h]; exact hx.2 ℓ₁ h1
      · rw [Finset.mem_singleton.1 h]; exact hx.2 ℓ₂ h2
    exact_mod_cast Finset.card_le_card this
  have hXcard : (X.card : ℝ) ≤ 2 ^ a := by
    have : X.card ≤ Aa.powerset.card := Finset.card_filter_le _ _
    rw [Finset.card_powerset] at this
    exact_mod_cast this
  unfold termII
  rw [← hX]
  push_cast
  calc ∑ A ∈ X, (-1 : ℝ) ^ (A.card + 1) * ((interMultiples A R Δ).card : ℝ)
      ≤ ∑ A ∈ X, (Δ / (Ψ * Tt) + 1) := by
        apply Finset.sum_le_sum
        intro A hA
        have h := hterm A hA
        have hc : (0 : ℝ) ≤ ((interMultiples A R Δ).card : ℝ) := Nat.cast_nonneg _
        rcases neg_one_pow_eq_or ℝ (A.card + 1) with e | e <;> rw [e] <;> linarith
    _ = X.card * (Δ / (Ψ * Tt) + 1) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 ^ a * (Δ / (Ψ * Tt) + 1) :=
        mul_le_mul_of_nonneg_right hXcard (by positivity)
    _ ≤ ε * (numOrders Aa Rstar Δ : ℝ) + 2 ^ a := by
        have key : 2 ^ a * (Δ / (Ψ * Tt)) ≤ ε * (Δ / (2 * Tt)) := by
          have hpa : (0 : ℝ) < 2 ^ a := by positivity
          rw [mul_div_assoc', mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
          rw [div_le_iff₀ hε0] at hΨ
          have hD : 0 ≤ Δ * Tt := mul_nonneg hΔ hTt_pos.le
          nlinarith [mul_le_mul_of_nonneg_left hΨ hD]
        have := mul_le_mul_of_nonneg_left hNstar hε0.le
        nlinarith
