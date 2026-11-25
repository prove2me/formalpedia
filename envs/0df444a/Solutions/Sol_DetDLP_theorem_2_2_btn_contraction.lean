-- Prove2me | solution 1 for DetDLP.theorem_2_2_btn_contraction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T10:11:05.972968+00:00
-- url     : https://prove2.me/submissions/f1974c50-20b8-447d-bf19-7cbb78776a32
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_DetDLP_lemma_5_2_degree_sensitive_contraction
import Definitions.Def_DetDLP_BTN

set_option autoImplicit false

open DetDLP

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation

private theorem scale_bounds {x : ℝ} (hx : 2 ≤ x) :
    let L := Real.logb 2 x
    let D := Nat.ceil (x ^ ((9 : ℝ) / 10))
    let r := max 1 (Nat.floor (Real.logb 2 (x / (D : ℝ))))
    x ^ ((9 : ℝ) / 10) * Real.sqrt L ≤ 20 * x ∧
      Real.sqrt L ≤ 6 * Real.sqrt (r : ℝ) := by
  let L := Real.logb 2 x
  let D := Nat.ceil (x ^ ((9 : ℝ) / 10))
  let r := max 1 (Nat.floor (Real.logb 2 (x / (D : ℝ))))
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hL : 1 ≤ L := by
    simpa only [Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2)] using
      Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2) (by norm_num) hx
  have hpow : 1 ≤ x ^ ((9 : ℝ) / 10) := Real.one_le_rpow hx1 (by norm_num)
  have hD1 : 1 ≤ (D : ℝ) := hpow.trans (Nat.le_ceil _)
  have hD0 : (0 : ℝ) < D := by linarith
  have hD : (D : ℝ) ≤ 2 * x ^ ((9 : ℝ) / 10) := by
    have h := Nat.ceil_lt_add_one (by linarith : 0 ≤ x ^ ((9 : ℝ) / 10))
    change (D : ℝ) < _ at h
    linarith
  have hr : (1 : ℝ) ≤ r := by exact_mod_cast (le_max_left 1 _)
  constructor
  · have hlog := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx0 ((1 : ℝ) / 10))
    rw [Real.log_rpow hx0] at hlog
    have hbase : (1 : ℝ) / 2 ≤ Real.log 2 := by
      simpa only [one_div] using (show (2 : ℝ)⁻¹ ≤ Real.log 2 by
        linarith [Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < 2),
          (by norm_num : (2:ℝ)⁻¹ = 1/2)])
    have hLlog : L * Real.log 2 = Real.log x := by
      dsimp [L, Real.logb]
      field_simp [ne_of_gt (Real.log_pos (by norm_num : (1:ℝ) < 2))]
    have hLs : Real.sqrt L ≤ 20 * x ^ ((1 : ℝ) / 10) := by
      have hs := Real.sqrt_le_self_iff.mpr (Or.inr hL)
      nlinarith [mul_nonneg (by linarith : 0 ≤ L) (sub_nonneg.mpr hbase)]
    have hsum : x ^ ((9 : ℝ) / 10) * x ^ ((1 : ℝ) / 10) = x := by
      rw [← Real.rpow_add hx0]
      norm_num
    nlinarith only [mul_le_mul_of_nonneg_left hLs (hpow.trans' zero_le_one), hsum]
  · have hlogD := Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2) hD0 hD
    rw [Real.logb_mul (by norm_num) (by positivity),
        Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2), Real.logb_rpow_eq_mul_logb_of_pos hx0] at hlogD
    have hf := Nat.lt_floor_add_one (Real.logb 2 (x / (D : ℝ)))
    have hfr : (Nat.floor (Real.logb 2 (x / (D : ℝ))) : ℝ) ≤ r := by
      exact_mod_cast (le_max_right 1 _)
    rw [Real.logb_div hx0.ne' hD0.ne'] at hf hfr
    change Real.sqrt L ≤ 6 * Real.sqrt (r : ℝ)
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    change Real.logb 2 x ≤ _
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ r by positivity)]

theorem solution :
    ∀ (C A c0 : ℕ), 0 < C → 0 < A → 0 < c0 →
      ∀ (E : PrimitiveMachine) (outE : Fin E.tapeCount),
        ∃ (M : PrimitiveMachine) (outM : Fin M.tapeCount) (K : ℕ),
          ∀ (s P0 ℓ : ℕ) (desc : List Bool) (G : BipartiteMultigraph)
            (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → TruncPoly P0 ℓ),
            2 ≤ s →
            G.nE ≤ C * s →
            G.nV ≤ s ^ c0 →
            G.maxDeg ≤ Nat.ceil ((s : ℝ) ^ ((9 : ℝ) / 10)) →
            1 ≤ P0 → P0 ≤ C * s →
            1 ≤ ℓ → ℓ ≤ C * s →
            BTNEntryEvaluable desc G P0 ℓ T E outE
              (((s + desc.length : ℕ) : ℝ) ^ c0 * (2 : ℝ) ^ ((A : ℝ) * (s : ℝ) ^ ((9 : ℝ) / 10)))
              (((s + desc.length : ℕ) : ℝ) ^ c0) →
            ∃ w : List Bool,
              EncodesTruncPoly P0 ℓ w (BTNContract G T) ∧
              RunsWithin M outM (encodeBTNInstance desc G s P0 ℓ) w
                (btnTimeBound K (s + desc.length) s)
                (polyBound K (s + desc.length)) := by
  intro C A c0 hC hA hc0 E outE
  obtain ⟨M, outM, k, run⟩ := lemma_5_2_degree_sensitive_contraction C c0 hC hc0 E outE
  let K := k + c0 + 20 * A + 6 * k + 1
  refine ⟨M, outM, K, ?_⟩
  intro s P ℓ desc G T hs he hv hdeg hP hPC hℓ hℓC hentry
  let u := s + desc.length
  let z := (s : ℝ) ^ ((9 : ℝ) / 10)
  let f := (u : ℝ) ^ c0 * (2 : ℝ) ^ ((A : ℝ) * z)
  let D := Nat.ceil z
  let r := max 1 (Nat.floor (Real.logb 2 ((s : ℝ) / (D : ℝ))))
  have hs2 : (2 : ℝ) ≤ s := by exact_mod_cast hs
  have hu : (1 : ℝ) ≤ u := by exact_mod_cast (show 1 ≤ u by dsimp [u]; omega)
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have h1f : 1 ≤ f := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hu)
    (Real.one_le_rpow (by norm_num) (mul_nonneg (Nat.cast_nonneg _) hz))
  have hfloor : 1 ≤ Nat.floor f := Nat.le_floor (by simpa using h1f)
  have inner : BTNEntryEvaluable desc G P ℓ T E outE (Nat.floor f : ℝ) ((u : ℝ) ^ c0) := by
    intro v α
    obtain ⟨w, hw, time, final, trace, halt, output, htime, space⟩ := hentry v α
    refine ⟨w, hw, time, final, trace, halt, output, ?_, space⟩
    exact_mod_cast (show time ≤ Nat.floor f from Nat.le_floor htime)
  obtain ⟨w, hw, time, final, trace, halt, output, htime, space⟩ :=
    run s P ℓ (Nat.floor f) desc G T hs hfloor he hv hP hPC hℓ hℓC inner
  rw [max_eq_right hdeg] at htime
  change (time : ℝ) ≤ polyBound k u * (Nat.floor f : ℝ) *
    (2 : ℝ) ^ ((k : ℝ) * s / Real.sqrt (r : ℝ)) at htime
  have hL1 : 1 ≤ Real.logb 2 s := by
    simpa only [Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2)] using
      Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2) (by norm_num) hs2
  have hsafe : logSafe (s : ℝ) = Real.logb 2 s := by
    simp only [logSafe, max_eq_right hs2, max_eq_right hL1]
  let L := Real.logb 2 s
  have hLpos : 0 < Real.sqrt L := Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one hL1)
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (le_max_left 1 _)
  have hrpos : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.mpr (by linarith)
  obtain ⟨hzL, hLr⟩ := scale_bounds hs2
  change z * Real.sqrt L ≤ 20 * s at hzL
  change Real.sqrt L ≤ 6 * Real.sqrt (r : ℝ) at hLr
  have hAs : (A : ℝ) * z ≤ 20 * A * s / Real.sqrt L := by
    apply (le_div_iff₀ hLpos).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hzL (Nat.cast_nonneg A)]
  have hks : (k : ℝ) * s / Real.sqrt (r : ℝ) ≤ 6 * k * s / Real.sqrt L := by
    apply (div_le_div_iff₀ hrpos hLpos).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hLr (mul_nonneg (Nat.cast_nonneg k) (Nat.cast_nonneg s))]
  have hexp : (A : ℝ) * z + k * s / Real.sqrt (r : ℝ) ≤ K * s / Real.sqrt L := by
    calc
      _ ≤ 20 * A * s / Real.sqrt L + 6 * k * s / Real.sqrt L := add_le_add hAs hks
      _ = (20 * A + 6 * k : ℝ) * s / Real.sqrt L := by ring
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ hLpos.le
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg s)
        exact_mod_cast (show 20 * A + 6 * k ≤ K by dsimp [K]; omega)
  have hk : k ≤ K := by dsimp [K]; omega
  have hkc : k + c0 ≤ K := by dsimp [K]; omega
  have hbase : 1 ≤ (u : ℝ) + 1 := by linarith
  have hpoly : polyBound k u * (u : ℝ) ^ c0 ≤ polyBound K u := by
    unfold polyBound
    calc
      _ ≤ (k : ℝ) * ((u : ℝ) + 1)^k * ((u : ℝ) + 1)^c0 := by gcongr <;> linarith
      _ = (k : ℝ) * ((u : ℝ) + 1)^(k + c0) := by rw [pow_add]; ring
      _ ≤ _ := mul_le_mul (by exact_mod_cast hk) (pow_le_pow_right₀ hbase hkc)
        (by positivity) (by positivity)
  refine ⟨w, hw, time, final, trace, halt, output, htime.trans ?_, ?_⟩
  · unfold btnTimeBound
    rw [hsafe]
    change _ ≤ polyBound K u * (2 : ℝ) ^ ((K : ℝ) * s / Real.sqrt L)
    calc
      _ ≤ polyBound k u * f * (2 : ℝ) ^ ((k : ℝ) * s / Real.sqrt (r : ℝ)) := by
        have hf := Nat.floor_le (show 0 ≤ f by linarith)
        have hpoly0 : 0 ≤ polyBound k u := by unfold polyBound; positivity
        gcongr
      _ = (polyBound k u * (u : ℝ)^c0) *
            (2 : ℝ) ^ ((A : ℝ) * z + k * s / Real.sqrt (r : ℝ)) := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        dsimp only [f]
        ring
      _ ≤ _ := mul_le_mul hpoly (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp)
        (by positivity) (by unfold polyBound; positivity)
  · intro j c hj hjc
    apply (space j c hj hjc).trans
    unfold polyBound
    exact mul_le_mul (by exact_mod_cast hk) (pow_le_pow_right₀ hbase hk) (by positivity) (by positivity)
