-- Prove2me | solution 1 for DriftLinBandit.BOB.theorem_4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T16:53:22.275642+00:00
-- url     : https://prove2.me/submissions/53f70a38-c960-474b-a345-38327c78b306
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DriftLinBandit_BOB_Model
import Definitions.Def_DriftLinBandit_BOB_Bob
import Theorems.Thm_DriftLinBandit_BOB_proposition_1

open MeasureTheory DriftLinBandit.BOB

namespace BOBThm4Aux

/-- Triangle inequality for `l2`. -/
lemma l2_sub_le {d : ℕ} (a b : Fin d → ℝ) : l2 (a - b) ≤ l2 a + l2 b := by
  have key : ∀ x : Fin d → ℝ, l2 x = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖ := by
    intro x
    rw [EuclideanSpace.norm_eq, l2]
    congr 1
    simp [dotProduct, Real.norm_eq_abs, sq]
  rw [key, key, key, WithLp.toLp_sub]
  exact norm_sub_le _ _

lemma variation_le {d : ℕ} (I : Instance d) (L S : ℝ) (hS : 0 ≤ S) (hst : I.Standing L S) :
    variation I ≤ 2 * S * I.T := by
  unfold variation
  calc ∑ t ∈ Finset.Ico 1 I.T, l2 (I.θ (t + 1) - I.θ t)
      ≤ ∑ t ∈ Finset.Ico 1 I.T, 2 * S := by
        apply Finset.sum_le_sum
        intro t ht
        rw [Finset.mem_Ico] at ht
        have h1 := (hst (t + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)).2.2
        have h2 := (hst t (Finset.mem_Icc.2 ⟨by omega, by omega⟩)).2.2
        linarith [l2_sub_le (I.θ (t + 1)) (I.θ t)]
    _ ≤ 2 * S * I.T := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
        have : ((I.T - 1 : ℕ) : ℝ) ≤ I.T := by exact_mod_cast Nat.sub_le _ _
        nlinarith

lemma third_term (R Lg D H T q δd lt : ℝ) (hR : 0 < R) (hH : 1 ≤ H) (hHq : H ≤ δd ^ 2 * q ^ 2)
    (hq : 1 ≤ q) (hδ : 1 ≤ δd) (hD : D + 1 ≤ 2 * Lg) (hD0 : 0 ≤ D) (hLg : 1 ≤ Lg)
    (hlt : lt ≤ Lg) (hT : T = q ^ 4) :
    (2 * H + 4 * R * Real.sqrt (H * lt)) * Real.sqrt ((D + 1) * T / H) ≤
      (4 + 8 * R) * Lg * (δd * q ^ 3) := by
  set s := Real.sqrt H with hs
  set ℓ := Real.sqrt Lg with hℓ
  have hs2 : s ^ 2 = H := Real.sq_sqrt (by linarith)
  have hℓ2 : ℓ ^ 2 = Lg := Real.sq_sqrt (by linarith)
  have hs1 : 1 ≤ s := by rw [hs]; exact Real.one_le_sqrt.2 hH
  have hℓ1 : 1 ≤ ℓ := by rw [hℓ]; exact Real.one_le_sqrt.2 hLg
  have hsle : s ≤ δd * q := by
    rw [hs]
    calc Real.sqrt H ≤ Real.sqrt ((δd * q) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = δd * q := Real.sqrt_sq (by positivity)
  have hℓle : ℓ ≤ Lg := by nlinarith
  have h1 : Real.sqrt (H * lt) ≤ s * ℓ := by
    rw [hs, hℓ, ← Real.sqrt_mul (by linarith)]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have h2 : Real.sqrt ((D + 1) * T / H) ≤ 2 * ℓ * q ^ 2 / s := by
    calc Real.sqrt ((D + 1) * T / H) ≤ Real.sqrt ((2 * ℓ * q ^ 2 / s) ^ 2) := by
          apply Real.sqrt_le_sqrt
          rw [div_pow, mul_pow, mul_pow, hs2, hℓ2, hT]
          apply div_le_div_of_nonneg_right _ (by linarith)
          have : 0 ≤ q ^ 4 := by positivity
          nlinarith
      _ = 2 * ℓ * q ^ 2 / s := Real.sqrt_sq (by positivity)
  have hsq : 0 ≤ Real.sqrt (H * lt) := Real.sqrt_nonneg _
  calc (2 * H + 4 * R * Real.sqrt (H * lt)) * Real.sqrt ((D + 1) * T / H)
      ≤ (2 * H + 4 * R * (s * ℓ)) * (2 * ℓ * q ^ 2 / s) := by
        apply mul_le_mul _ h2 (Real.sqrt_nonneg _) (by positivity)
        nlinarith
    _ = 4 * s * ℓ * q ^ 2 + 8 * R * ℓ ^ 2 * q ^ 2 := by
        rw [← hs2]; field_simp; ring
    _ ≤ 4 * (δd * q) * Lg * q ^ 2 + 8 * R * Lg * (δd * q * q ^ 2) := by
        rw [hℓ2]
        have hq2 : 0 ≤ q ^ 2 := by positivity
        have : 1 * q ^ 2 ≤ δd * q * q ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ hq2; nlinarith
        have h4 : s * ℓ ≤ (δd * q) * Lg :=
          mul_le_mul hsle hℓle (by linarith) (by nlinarith)
        have h5 : 0 ≤ 8 * R * Lg := by positivity
        nlinarith [mul_le_mul_of_nonneg_left this h5, mul_le_mul_of_nonneg_right h4 hq2]
    _ = (4 + 8 * R) * Lg * (δd * q ^ 3) := by ring

lemma case_b (n β J : ℝ) (hn : 0 < n) (hβ : 0 ≤ β) (hJ : 1 ≤ J) (h1 : J * β ^ 2 ≤ n ^ 2)
    (h2 : n ^ 2 ≤ 6 * J * β ^ 2) :
    J * β ^ 3 + n ^ 3 / Real.sqrt J ≤ 4 * (n ^ 2 * β) := by
  have hJs : 0 < Real.sqrt J := Real.sqrt_pos.2 (by linarith)
  have hJs2 : Real.sqrt J ^ 2 = J := Real.sq_sqrt (by linarith)
  have hA : J * β ^ 3 ≤ n ^ 2 * β := by
    have : J * β ^ 3 = (J * β ^ 2) * β := by ring
    rw [this]; exact mul_le_mul_of_nonneg_right h1 hβ
  have hn3 : n ≤ 3 * β * Real.sqrt J := by
    have : n ^ 2 ≤ (3 * β * Real.sqrt J) ^ 2 := by
      rw [mul_pow, hJs2]; nlinarith
    exact (pow_le_pow_iff_left₀ hn.le (by positivity) two_ne_zero).1 this
  have hB : n ^ 3 / Real.sqrt J ≤ 3 * (n ^ 2 * β) := by
    rw [div_le_iff₀ hJs]
    have : n ^ 3 = n ^ 2 * n := by ring
    rw [this]
    calc n ^ 2 * n ≤ n ^ 2 * (3 * β * Real.sqrt J) :=
          mul_le_mul_of_nonneg_left hn3 (by positivity)
      _ = 3 * (n ^ 2 * β) * Real.sqrt J := by ring
  linarith

lemma case_a (n β H δd q : ℝ) (hβ : 0 ≤ β) (hH : 1 ≤ H) (h1 : H * β ^ 2 ≤ n ^ 2)
    (hn3 : n ^ 3 = δd ^ 2 * q ^ 4) (hHq : δd ^ 2 * q ^ 2 ≤ 2 * H) (hδ : 0 < δd) (hq : 0 < q) :
    H * β ^ 3 + n ^ 3 / Real.sqrt H ≤ n ^ 2 * β + 2 * (δd * q ^ 3) := by
  have hJs : 0 < Real.sqrt H := Real.sqrt_pos.2 (by linarith)
  have hJs2 : Real.sqrt H ^ 2 = H := Real.sq_sqrt (by linarith)
  have hA : H * β ^ 3 ≤ n ^ 2 * β := by
    have : H * β ^ 3 = (H * β ^ 2) * β := by ring
    rw [this]; exact mul_le_mul_of_nonneg_right h1 hβ
  have hdq : δd * q ≤ 2 * Real.sqrt H := by
    have : (δd * q) ^ 2 ≤ (2 * Real.sqrt H) ^ 2 := by
      rw [mul_pow, mul_pow, hJs2]; nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 this
  have hB : n ^ 3 / Real.sqrt H ≤ 2 * (δd * q ^ 3) := by
    rw [div_le_iff₀ hJs, hn3]
    have hp : 0 ≤ δd * q ^ 3 := by positivity
    calc δd ^ 2 * q ^ 4 = (δd * q ^ 3) * (δd * q) := by ring
      _ ≤ (δd * q ^ 3) * (2 * Real.sqrt H) := mul_le_mul_of_nonneg_left hdq hp
      _ = 2 * (δd * q ^ 3) * Real.sqrt H := by ring
  linarith

end BOBThm4Aux

namespace BOBThm4Aux

lemma rpow_frac (x : ℝ) (hx : 0 ≤ x) (a b : ℕ) :
    x ^ ((a : ℝ) / b) = (x ^ ((1 : ℝ) / b)) ^ a := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; ring_nf

lemma rpow_inv_pow (x : ℝ) (hx : 0 ≤ x) (b : ℕ) (hb : b ≠ 0) :
    (x ^ ((1 : ℝ) / b)) ^ b = x := by
  rw [← rpow_frac x hx b b, div_self (by exact_mod_cast hb), Real.rpow_one]

lemma bobJ_last (d T : ℕ) (hH : 1 ≤ bobH d T) :
    (bobJ d T ⟨bobDelta d T, Nat.lt_succ_self _⟩ : ℝ) = bobH d T := by
  unfold bobJ
  simp only
  by_cases h0 : bobDelta d T = 0
  · have hl : Real.log (bobH d T) ≤ 0 := by
      have := Nat.le_ceil (Real.log (bobH d T))
      unfold bobDelta at h0
      rw [h0] at this; exact_mod_cast this
    have hH1 : (bobH d T : ℝ) ≤ 1 := by
      have hpos : (0 : ℝ) < bobH d T := by exact_mod_cast hH
      by_contra hc
      push_neg at hc
      linarith [Real.log_pos hc]
    have : bobH d T = 1 := by
      have : bobH d T ≤ 1 := by exact_mod_cast hH1
      omega
    rw [h0, this]; simp
  · rw [div_self (by exact_mod_cast h0), Real.rpow_one]
    simp

lemma bobJ_zero (d T : ℕ) :
    (bobJ d T ⟨0, Nat.succ_pos _⟩ : ℝ) = 1 := by
  unfold bobJ; simp

end BOBThm4Aux

set_option maxHeartbeats 2000000 in
open BOBThm4Aux in
theorem solution (R L S lam : ℝ) (hR : 0 < R) (hL : 0 < L) (hS : 0 < S) (hlam : 0 < lam)
    (hlamS : 1 ≤ lam * S ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ,
      ∀ (d : ℕ), 1 ≤ d → ∀ (I : Instance d), 1 ≤ I.T → I.Standing L S → Assumption1 I →
      ∀ (B : ℝ), 0 ≤ B → variation I ≤ B →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (η : ℕ → Ω → ℝ), IsSubGNoise P η R →
        Integrable (bobRegretMix I R L S lam η) P ∧
        ∫ ω, bobRegretMix I R L S lam η ω ∂P ≤
          C * (1 + Real.log ((d : ℝ) * I.T)) ^ k *
            ((d : ℝ) ^ ((2 : ℝ) / 3) * B ^ ((1 : ℝ) / 3) * (I.T : ℝ) ^ ((2 : ℝ) / 3) +
              (d : ℝ) ^ ((1 : ℝ) / 2) * (I.T : ℝ) ^ ((3 : ℝ) / 4)) := by
  obtain ⟨C₁, hC₁, k₁, hP⟩ := proposition_1 R L S lam hR hL hS hlam hlamS
  refine ⟨C₁ * (8 + 2 * S + 8 * R), by positivity, k₁ + 1, ?_⟩
  intro d hd I hT hst hA B hB hvar Ω _ P _ η hη
  have hvar0 : 0 ≤ variation I := Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)
  refine ⟨(hP d hd I hT hst hA B hB hvar P η hη).1, ?_⟩
  -- basic real facts
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hT1 : (1 : ℝ) ≤ I.T := by exact_mod_cast hT
  have hdT1 : (1 : ℝ) ≤ (d : ℝ) * I.T := by nlinarith
  have hlogdT : 0 ≤ Real.log ((d : ℝ) * I.T) := Real.log_nonneg hdT1
  set Lg := 1 + Real.log ((d : ℝ) * I.T) with hLg
  have hLg1 : 1 ≤ Lg := by linarith
  set q := (I.T : ℝ) ^ ((1 : ℝ) / 4) with hqdef
  set δd := (d : ℝ) ^ ((1 : ℝ) / 2) with hδdef
  set n := ((d : ℝ) * I.T) ^ ((1 : ℝ) / 3) with hndef
  set β := B ^ ((1 : ℝ) / 3) with hβdef
  have hq1 : 1 ≤ q := Real.one_le_rpow hT1 (by norm_num)
  have hδ1 : 1 ≤ δd := Real.one_le_rpow hd1 (by norm_num)
  have hn1 : 1 ≤ n := Real.one_le_rpow hdT1 (by norm_num)
  have hβ0 : 0 ≤ β := Real.rpow_nonneg hB _
  have hq4 : q ^ 4 = I.T := by
    have := rpow_inv_pow (I.T : ℝ) (by positivity) 4 (by norm_num)
    simp only [Nat.cast_ofNat] at this; exact this
  have hδ2 : δd ^ 2 = d := by
    have := rpow_inv_pow (d : ℝ) (by positivity) 2 (by norm_num)
    simp only [Nat.cast_ofNat] at this; exact this
  have hn3 : n ^ 3 = (d : ℝ) * I.T := by
    have := rpow_inv_pow ((d : ℝ) * I.T) (by positivity) 3 (by norm_num)
    simp only [Nat.cast_ofNat] at this; exact this
  have hβ3 : β ^ 3 = B := by
    have := rpow_inv_pow B hB 3 (by norm_num)
    simp only [Nat.cast_ofNat] at this; exact this
  have hsqrtT : Real.sqrt (I.T : ℝ) = q ^ 2 := by
    rw [← hq4, show q ^ 4 = (q ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hD1 : (d : ℝ) ^ ((2 : ℝ) / 3) * B ^ ((1 : ℝ) / 3) * (I.T : ℝ) ^ ((2 : ℝ) / 3) =
      n ^ 2 * β := by
    rw [mul_comm ((d : ℝ) ^ ((2 : ℝ) / 3)), mul_assoc, ← Real.mul_rpow (by positivity)
      (by positivity), mul_comm (B ^ _)]
    have := rpow_frac ((d : ℝ) * I.T) (by positivity) 2 3
    norm_num at this
    rw [this]
  have hD2 : (d : ℝ) ^ ((1 : ℝ) / 2) * (I.T : ℝ) ^ ((3 : ℝ) / 4) = δd * q ^ 3 := by
    have := rpow_frac (I.T : ℝ) (by positivity) 3 4
    norm_num at this
    rw [this]
  rw [hD1, hD2]
  have hD1n : 0 ≤ n ^ 2 * β := by positivity
  have hD2n : 0 ≤ δd * q ^ 3 := by positivity
  -- facts on H and Δ
  have hx1 : (1 : ℝ) ≤ (d : ℝ) * Real.sqrt I.T := by
    rw [hsqrtT]; nlinarith
  have hH1 : 1 ≤ bobH d I.T := Nat.le_floor (by simpa using hx1)
  have hH1r : (1 : ℝ) ≤ bobH d I.T := by exact_mod_cast hH1
  have hHle : (bobH d I.T : ℝ) ≤ (d : ℝ) * Real.sqrt I.T := Nat.floor_le (by linarith)
  have hHge : (d : ℝ) * Real.sqrt I.T ≤ 2 * bobH d I.T := by
    have := Nat.lt_floor_add_one ((d : ℝ) * Real.sqrt I.T)
    have h' := hH1r
    unfold bobH at h' ⊢; linarith
  have hHq : (bobH d I.T : ℝ) ≤ δd ^ 2 * q ^ 2 := by rw [hδ2, ← hsqrtT]; exact hHle
  have hHq' : δd ^ 2 * q ^ 2 ≤ 2 * bobH d I.T := by rw [hδ2, ← hsqrtT]; exact hHge
  have hlogH : Real.log (bobH d I.T) ≤ Real.log ((d : ℝ) * I.T) := by
    apply Real.log_le_log (by linarith)
    have : Real.sqrt I.T ≤ I.T := by rw [hsqrtT, ← hq4]; nlinarith
    nlinarith
  have hΔ1 : Real.log (bobH d I.T) ≤ bobDelta d I.T := Nat.le_ceil _
  have hΔ2 : (bobDelta d I.T : ℝ) < Real.log (bobH d I.T) + 1 :=
    Nat.ceil_lt_add_one (Real.log_nonneg hH1r)
  -- third term
  have h3 : bobQ R d I.T * Real.sqrt (((bobDelta d I.T : ℝ) + 1) * I.T / (bobH d I.T : ℝ)) ≤
      (4 + 8 * R) * Lg * (δd * q ^ 3) := by
    unfold bobQ
    apply third_term R Lg (bobDelta d I.T) (bobH d I.T) I.T q δd _ hR hH1r hHq hq1 hδ1
      (by linarith) (by positivity) hLg1 _ hq4.symm
    have hsH : 1 ≤ Real.sqrt (bobH d I.T : ℝ) := Real.one_le_sqrt.2 hH1r
    calc Real.log ((I.T : ℝ) / Real.sqrt (bobH d I.T)) ≤ Real.log (I.T) := by
          apply Real.log_le_log (by positivity)
          exact div_le_self (by positivity) hsH
      _ ≤ Real.log ((d : ℝ) * I.T) :=
          Real.log_le_log (by positivity) (le_mul_of_one_le_left (by positivity) hd1)
      _ ≤ Lg := by linarith
  -- first two terms
  have h12 : ∃ (B' : ℝ) (j : Fin (bobDelta d I.T + 1)), 0 ≤ B' ∧ variation I ≤ B' ∧
      (bobJ d I.T j : ℝ) * B' + (d : ℝ) * I.T / Real.sqrt (bobJ d I.T j) ≤
        (4 + 2 * S) * (n ^ 2 * β + δd * q ^ 3) := by
    by_cases hBn : B ≤ (d : ℝ) * I.T
    · have hβn : β ≤ n := by
        have : β ^ 3 ≤ n ^ 3 := by rw [hn3, hβ3]; exact hBn
        exact (pow_le_pow_iff_left₀ hβ0 (by positivity) (by norm_num)).1 this
      have hHpos : (0 : ℝ) < bobH d I.T := by linarith
      let x : Fin (bobDelta d I.T + 1) → ℝ :=
        fun j => (bobH d I.T : ℝ) ^ ((j : ℝ) / (bobDelta d I.T : ℝ))
      have hxJ : ∀ j, (bobJ d I.T j : ℝ) = (⌊x j⌋₊ : ℝ) := fun j => rfl
      have hx1 : ∀ j, 1 ≤ x j := fun j => Real.one_le_rpow hH1r (by positivity)
      let Sset := (Finset.univ : Finset (Fin (bobDelta d I.T + 1))).filter
        (fun j => x j * β ^ 2 ≤ n ^ 2)
      have h0 : (⟨0, Nat.succ_pos _⟩ : Fin (bobDelta d I.T + 1)) ∈ Sset := by
        simp only [Sset, Finset.mem_filter, Finset.mem_univ, true_and, x]
        simp only [Nat.cast_zero, zero_div, Real.rpow_zero, one_mul]
        exact pow_le_pow_left₀ hβ0 hβn 2
      have hjsS : Sset.max' ⟨_, h0⟩ ∈ Sset := Finset.max'_mem _ _
      set js := Sset.max' ⟨_, h0⟩ with hjs
      have hjx : x js * β ^ 2 ≤ n ^ 2 := (Finset.mem_filter.1 hjsS).2
      have hJle : (bobJ d I.T js : ℝ) ≤ x js := by
        rw [hxJ]; exact Nat.floor_le (by linarith [hx1 js])
      have hJ1n : 1 ≤ bobJ d I.T js := Nat.le_floor (by simpa using hx1 js)
      have hJ1 : (1 : ℝ) ≤ bobJ d I.T js := by exact_mod_cast hJ1n
      have hJβ : (bobJ d I.T js : ℝ) * β ^ 2 ≤ n ^ 2 :=
        le_trans (mul_le_mul_of_nonneg_right hJle (by positivity)) hjx
      refine ⟨B, js, hB, hvar, ?_⟩
      rw [← hβ3, ← hn3]
      by_cases hjΔ : (js : ℕ) = bobDelta d I.T
      · have hjeq : js = ⟨bobDelta d I.T, Nat.lt_succ_self _⟩ := Fin.ext hjΔ
        have hJH : (bobJ d I.T js : ℝ) = bobH d I.T := by rw [hjeq]; exact bobJ_last d I.T hH1
        rw [hJH]; rw [hJH] at hJβ
        have hA := case_a n β (bobH d I.T) δd q hβ0 hH1r hJβ (by rw [hn3, hδ2, ← hq4])
          hHq' (by positivity) (by positivity)
        have h7 : n ^ 2 * β + 2 * (δd * q ^ 3) ≤ (4 + 2 * S) * (n ^ 2 * β + δd * q ^ 3) := by
          have : 0 ≤ S * (n ^ 2 * β + δd * q ^ 3) := by positivity
          linarith
        exact hA.trans h7
      · have hjlt : (js : ℕ) + 1 < bobDelta d I.T + 1 := by
          have := js.isLt; omega
        have hj'n : (⟨(js : ℕ) + 1, hjlt⟩ : Fin (bobDelta d I.T + 1)) ∉ Sset := by
          intro hm
          have := Finset.le_max' Sset _ hm
          rw [← hjs, Fin.le_def] at this
          simp at this
        have hj'x : n ^ 2 < x ⟨(js : ℕ) + 1, hjlt⟩ * β ^ 2 := by
          simp only [Sset, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hj'n
          exact hj'n
        have hΔpos : (0 : ℝ) < bobDelta d I.T := by
          have : 0 < bobDelta d I.T := by have := js.isLt; omega
          exact_mod_cast this
        have hstep : x ⟨(js : ℕ) + 1, hjlt⟩ ≤ 3 * x js := by
          show (bobH d I.T : ℝ) ^ ((((js : ℕ) + 1 : ℕ) : ℝ) / (bobDelta d I.T : ℝ)) ≤
            3 * (bobH d I.T : ℝ) ^ (((js : ℕ) : ℝ) / (bobDelta d I.T : ℝ))
          push_cast
          rw [add_div, Real.rpow_add hHpos]
          have h3' : (bobH d I.T : ℝ) ^ ((1 : ℝ) / bobDelta d I.T) ≤ 3 := by
            rw [Real.rpow_def_of_pos hHpos]
            calc Real.exp (Real.log (bobH d I.T) * (1 / bobDelta d I.T)) ≤ Real.exp 1 := by
                  apply Real.exp_le_exp.2
                  rw [mul_one_div, div_le_one hΔpos]; exact hΔ1
              _ ≤ 3 := (Real.exp_one_lt_d9).le.trans (by norm_num)
          rw [mul_comm 3]
          exact mul_le_mul_of_nonneg_left h3' (by positivity)
        have hJge : x js ≤ 2 * (bobJ d I.T js : ℝ) := by
          have := Nat.lt_floor_add_one (x js)
          rw [hxJ]; rw [hxJ] at hJ1; linarith
        have h6 : n ^ 2 ≤ 6 * (bobJ d I.T js : ℝ) * β ^ 2 := by
          have hb2 : 0 ≤ β ^ 2 := by positivity
          have e1 := mul_le_mul_of_nonneg_right hstep hb2
          have e2 := mul_le_mul_of_nonneg_right hJge hb2
          linarith
        have hB := case_b n β _ (by linarith) hβ0 hJ1 hJβ h6
        have h7 : 4 * (n ^ 2 * β) ≤ (4 + 2 * S) * (n ^ 2 * β + δd * q ^ 3) := by
          have : 0 ≤ S * (n ^ 2 * β + δd * q ^ 3) := by positivity
          linarith
        exact hB.trans h7
    · push Not at hBn
      refine ⟨variation I, ⟨0, Nat.succ_pos _⟩, hvar0, le_rfl, ?_⟩
      rw [bobJ_zero, Real.sqrt_one, div_one, one_mul]
      have hβn : n ≤ β := by
        have : n ^ 3 ≤ β ^ 3 := by rw [hn3, hβ3]; linarith
        exact (pow_le_pow_iff_left₀ (by positivity) hβ0 (by norm_num)).1 this
      have h1 : n ^ 3 ≤ n ^ 2 * β := by
        rw [show n ^ 3 = n ^ 2 * n by ring]
        exact mul_le_mul_of_nonneg_left hβn (by positivity)
      have h2 := variation_le I L S hS.le hst
      have h4 : (I.T : ℝ) ≤ (d : ℝ) * I.T := le_mul_of_one_le_left (by positivity) hd1
      rw [← hn3]
      rw [← hn3] at h4
      have h5 : 2 * S * (I.T : ℝ) ≤ 2 * S * n ^ 3 := mul_le_mul_of_nonneg_left h4 (by positivity)
      have h6 : (2 * S + 1) * n ^ 3 ≤ (2 * S + 1) * (n ^ 2 * β) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have h7 : (2 * S + 1) * (n ^ 2 * β) ≤ (4 + 2 * S) * (n ^ 2 * β + δd * q ^ 3) :=
        mul_le_mul (by linarith) (by linarith) hD1n (by positivity)
      linarith
  obtain ⟨B', j, hB'0, hB', hbd⟩ := h12
  have hmain := (hP d hd I hT hst hA B' hB'0 hB' P η hη).2 j
  refine hmain.trans ?_
  have hLgk : 0 ≤ Lg ^ k₁ := by positivity
  have hsum : (bobJ d I.T j : ℝ) * B' + (d : ℝ) * I.T / Real.sqrt (bobJ d I.T j) +
      bobQ R d I.T * Real.sqrt (((bobDelta d I.T : ℝ) + 1) * I.T / (bobH d I.T : ℝ)) ≤
      (8 + 2 * S + 8 * R) * Lg * (n ^ 2 * β + δd * q ^ 3) := by
    have e1 : (4 + 2 * S) * (n ^ 2 * β + δd * q ^ 3) ≤
        (4 + 2 * S) * Lg * (n ^ 2 * β + δd * q ^ 3) := by
      have hnn : 0 ≤ (4 + 2 * S) * (n ^ 2 * β + δd * q ^ 3) := by positivity
      have h := le_mul_of_one_le_left hnn hLg1
      linarith [h, show Lg * ((4 + 2 * S) * (n ^ 2 * β + δd * q ^ 3)) =
        (4 + 2 * S) * Lg * (n ^ 2 * β + δd * q ^ 3) by ring]
    have e2 : (4 + 8 * R) * Lg * (δd * q ^ 3) ≤
        (4 + 8 * R) * Lg * (n ^ 2 * β + δd * q ^ 3) := by
      exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hD1n) (by positivity)
    refine (add_le_add hbd h3).trans ((add_le_add e1 e2).trans (le_of_eq (by ring)))
  calc C₁ * (1 + Real.log ((d : ℝ) * I.T)) ^ k₁ *
        ((bobJ d I.T j : ℝ) * B' + (d : ℝ) * I.T / Real.sqrt (bobJ d I.T j) +
          bobQ R d I.T * Real.sqrt (((bobDelta d I.T : ℝ) + 1) * I.T / (bobH d I.T : ℝ)))
      ≤ C₁ * Lg ^ k₁ * ((8 + 2 * S + 8 * R) * Lg * (n ^ 2 * β + δd * q ^ 3)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = C₁ * (8 + 2 * S + 8 * R) * Lg ^ (k₁ + 1) * (n ^ 2 * β + δd * q ^ 3) := by ring
