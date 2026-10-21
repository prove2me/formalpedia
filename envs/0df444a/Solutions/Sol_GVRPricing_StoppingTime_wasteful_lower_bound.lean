-- Prove2me | solution 1 for GVRPricing.StoppingTime.wasteful_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:10:22.979984+00:00
-- url     : https://prove2.me/submissions/196b2233-a243-4d19-9e7b-78e066944c5c

import Mathlib
import Definitions.Def_GVRPricing_StoppingTime_DetLP
import Definitions.Def_GVRPricing_StoppingTime_STHeuristic
import Definitions.Def_GVRPricing_StoppingTime_Wasteful

set_option autoImplicit false
open GVRPricing.StoppingTime

lemma gvr_lamN {K : ℕ} (M : Menu K) {k : ℕ} (hk : k < K) : M.lamN k = M.lam ⟨k, hk⟩ := by
  simp [Menu.lamN, hk]

lemma gvr_pN {K : ℕ} (M : Menu K) {k : ℕ} (hk : k < K) : M.pN k = M.p ⟨k, hk⟩ := by
  simp [Menu.pN, hk]

lemma gvr_rN {K : ℕ} (M : Menu K) {k : ℕ} (hk : k < K) : M.rN k = M.r ⟨k, hk⟩ := by
  simp [Menu.rN, Menu.r, gvr_lamN M hk, gvr_pN M hk]

/-- The chord certificate: with `a = λ_{k+1} < b = λ_k`, the line `α + β x` through the points
`(a, r_{k+1})`, `(b, r_k)` dominates every `r_j` at `λ_j`, `α ≥ 0`, `β ≥ 0`. -/
lemma gvr_cert {K : ℕ} (M : Menu K) (k : ℕ) (hk : k + 1 < K) :
    ∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ (∀ j : Fin K, M.r j ≤ α + β * M.lam j) ∧
      M.r ⟨k, by omega⟩ = α + β * M.lam ⟨k, by omega⟩ ∧
      M.r ⟨k + 1, hk⟩ = α + β * M.lam ⟨k + 1, hk⟩ ∧
      α = (M.lamN k * M.rN (k + 1) - M.lamN (k + 1) * M.rN k) / (M.lamN k - M.lamN (k + 1)) ∧
      β = (M.rN k - M.rN (k + 1)) / (M.lamN k - M.lamN (k + 1)) := by
  obtain ⟨f, hf, hf0, hfr⟩ := M.concave
  have hk0 : k < K := by omega
  set ik : Fin K := ⟨k, hk0⟩ with hik
  set ik1 : Fin K := ⟨k + 1, hk⟩ with hik1
  set a : ℝ := M.lam ik1 with ha
  set b : ℝ := M.lam ik with hb
  have hapos : 0 < a := M.lam_pos _
  have hab : a < b := M.lam_strictAnti (show ik < ik1 from by simp [hik, hik1])
  have hra : f a = M.r ik1 := by simp only [Menu.r]; exact hfr ik1
  have hrb : f b = M.r ik := by simp only [Menu.r]; exact hfr ik
  have hrr : M.r ik1 < M.r ik := M.r_strictAnti (show ik < ik1 from by simp [hik, hik1])
  set ra := M.r ik1 with hra'
  set rb := M.r ik with hrb'
  set β : ℝ := (rb - ra) / (b - a) with hβ
  set α : ℝ := (b * ra - a * rb) / (b - a) with hα
  have hba : 0 < b - a := by linarith
  have hβb : β * (b - a) = rb - ra := by rw [hβ]; field_simp
  have hαe : α = ra - β * a := by
    rw [hα, hβ]; field_simp; ring
  have hβpos : 0 ≤ β := by rw [hβ]; exact div_nonneg (by linarith) hba.le
  have hrk : rb = α + β * b := by rw [hαe]; nlinarith
  have hrk1 : ra = α + β * a := by rw [hαe]; ring
  -- slope inequalities
  have hs_hi : ∀ x : ℝ, b < x → f x ≤ rb + β * (x - b) := by
    intro x hx
    have := hf.slope_anti_adjacent (x := a) (y := b) (z := x) (by simp; linarith) (by simp; linarith) hab hx
    rw [hra, hrb] at this
    have h2 : (f x - rb) ≤ β * (x - b) := by
      rw [div_le_iff₀ (by linarith)] at this
      linarith
    linarith
  have hs_lo : ∀ x : ℝ, 0 ≤ x → x < a → f x ≤ ra + β * (x - a) := by
    intro x hx0 hx
    have := hf.slope_anti_adjacent (x := x) (y := a) (z := b) (by simpa using hx0) (by simp; linarith) hx hab
    rw [hra, hrb] at this
    have h1 : β ≤ (ra - f x) / (a - x) := by rw [hβ]; exact this
    rw [le_div_iff₀ (by linarith)] at h1
    linarith
  refine ⟨α, β, ?_, hβpos, ?_, hrk, hrk1, ?_, ?_⟩
  · have := hs_lo 0 le_rfl hapos
    rw [hf0] at this
    rw [hαe]; nlinarith
  · intro j
    rcases lt_trichotomy j.val k with hj | hj | hj
    · have hjk : j < ik := by simpa [hik, Fin.lt_def] using hj
      have hx : b < M.lam j := M.lam_strictAnti hjk
      have h1 := hs_hi (M.lam j) hx
      have : f (M.lam j) = M.r j := by simp only [Menu.r]; exact hfr j
      rw [this] at h1
      nlinarith
    · have : j = ik := Fin.ext hj
      subst this; exact le_of_eq hrk
    · rcases Nat.lt_or_ge (k + 1) j.val with hj2 | hj2
      · have hjk : ik1 < j := by simpa [hik1, Fin.lt_def] using hj2
        have hx : M.lam j < a := M.lam_strictAnti hjk
        have h1 := hs_lo (M.lam j) (M.lam_pos j).le hx
        have : f (M.lam j) = M.r j := by simp only [Menu.r]; exact hfr j
        rw [this] at h1
        nlinarith
      · have : j = ik1 := Fin.ext (by simp [hik1]; omega)
        subst this; exact le_of_eq hrk1
  · rw [gvr_lamN M hk0, gvr_lamN M hk, gvr_rN M hk0, gvr_rN M hk]
  · rw [gvr_lamN M hk0, gvr_lamN M hk, gvr_rN M hk0, gvr_rN M hk]

lemma gvr_sum_two {K : ℕ} (k : ℕ) (hk : k + 1 < K) (g : Fin K → ℝ) (A B : ℝ) :
    ∑ j : Fin K, g j * (if j.val = k then A else if j.val = k + 1 then B else 0) =
      g ⟨k, by omega⟩ * A + g ⟨k + 1, hk⟩ * B := by
  rw [Finset.sum_eq_add (⟨k, by omega⟩ : Fin K) ⟨k + 1, hk⟩ (by simp [Fin.ext_iff])]
  · simp
  · intro j _ hj
    have h1 : j.val ≠ k := fun h => hj.1 (Fin.ext h)
    have h2 : j.val ≠ k + 1 := fun h => hj.2 (Fin.ext h)
    simp [h1, h2]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro h; exact absurd (Finset.mem_univ _) h

lemma gvr_prop4 {K : ℕ} (M : Menu K) (n t : ℝ) (hn : 0 ≤ n) (ht : 0 < t) :
    (∀ k : ℕ, k + 1 < K → n ≤ M.lamN k * t → M.lamN (k + 1) * t < n →
        IsLPSolution M n t (twoPriceAlloc M k n t)) ∧
    (M.lamN 0 * t < n →
        IsLPSolution M n t (fun j => if j.val = 0 then t else 0)) ∧
    (n ≤ M.lamN (K - 1) * t →
        IsLPSolution M n t (fun j => if j.val = K - 1 then n / M.lamN (K - 1) else 0)) := by
  have hK2 := M.two_le
  refine ⟨?_, ?_, ?_⟩
  · intro k hk hup hlow
    obtain ⟨α, β, hα, hβ, hdom, hrk, hrk1, hαe, hβe⟩ := gvr_cert M k hk
    have hk0 : k < K := by omega
    have hlk := gvr_lamN M hk0
    have hlk1 := gvr_lamN M hk
    have hab : M.lam ⟨k + 1, hk⟩ < M.lam ⟨k, hk0⟩ :=
      M.lam_strictAnti (show (⟨k, hk0⟩ : Fin K) < ⟨k + 1, hk⟩ from by simp)
    set a := M.lam ⟨k + 1, hk⟩ with ha
    set b := M.lam ⟨k, hk0⟩ with hb
    rw [hlk] at hup
    rw [hlk1] at hlow
    have hΔ : 0 < b - a := by linarith
    have hτ : twoPriceAlloc M k n t = fun j => if j.val = k then (n - a * t) / (b - a)
        else if j.val = k + 1 then (b * t - n) / (b - a) else 0 := by
      funext j; simp only [twoPriceAlloc, hlk, hlk1]
    have hτk : 0 ≤ (n - a * t) / (b - a) := div_nonneg (by linarith) hΔ.le
    have hτk1 : 0 ≤ (b * t - n) / (b - a) := div_nonneg (by linarith) hΔ.le
    have hsumτ : (n - a * t) / (b - a) + (b * t - n) / (b - a) = t := by field_simp; ring
    have hsumL : b * ((n - a * t) / (b - a)) + a * ((b * t - n) / (b - a)) = n := by
      field_simp; ring
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · intro j; rw [hτ]; beta_reduce; split_ifs <;> first | exact hτk | exact hτk1 | exact le_rfl
    · have := gvr_sum_two k hk (fun _ => 1) ((n - a * t) / (b - a)) ((b * t - n) / (b - a))
      simp only [one_mul] at this
      rw [hτ, this]; linarith
    · have := gvr_sum_two k hk (fun j => M.lam j) ((n - a * t) / (b - a)) ((b * t - n) / (b - a))
      rw [hτ]
      have h2 : ∑ j : Fin K, M.lam j * (if j.val = k then (n - a * t) / (b - a)
        else if j.val = k + 1 then (b * t - n) / (b - a) else 0) =
          ∑ j : Fin K, (fun j : Fin K => M.lam j) j * (if j.val = k then (n - a * t) / (b - a)
        else if j.val = k + 1 then (b * t - n) / (b - a) else 0) := rfl
      beta_reduce at this
      rw [this]; linarith
    · intro τ' ⟨hτ0, hτs, hτl⟩
      have hrev : lpRevenue M (twoPriceAlloc M k n t) = α * t + β * n := by
        unfold lpRevenue
        rw [hτ]
        have := gvr_sum_two k hk (fun j => M.r j) ((n - a * t) / (b - a)) ((b * t - n) / (b - a))
        beta_reduce at this
        rw [this, hrk, hrk1]
        nlinarith
      rw [hrev]
      unfold lpRevenue
      calc ∑ j, M.r j * τ' j ≤ ∑ j, (α * τ' j + β * (M.lam j * τ' j)) :=
            Finset.sum_le_sum (fun j _ => by nlinarith [hdom j, hτ0 j])
        _ = α * ∑ j, τ' j + β * ∑ j, M.lam j * τ' j := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
        _ ≤ α * t + β * n := by nlinarith
  · intro hn0
    have hK0 : 0 < K := by omega
    have hl0 := gvr_lamN M hK0
    set i0 : Fin K := ⟨0, hK0⟩ with hi0
    have hr0 : 0 ≤ M.r i0 := mul_nonneg (M.p_nonneg _) (M.lam_pos _).le
    have hsum : ∀ g : Fin K → ℝ, ∑ j : Fin K, g j * (if j.val = 0 then t else 0) = g i0 * t := by
      intro g
      rw [Finset.sum_eq_single i0]
      · simp [hi0]
      · intro j _ hj
        have : j.val ≠ 0 := fun h => hj (Fin.ext h)
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · intro j; beta_reduce; split_ifs <;> linarith
    · have := hsum (fun _ => 1); simp only [one_mul] at this; rw [this]
    · have := hsum (fun j => M.lam j)
      rw [hl0] at hn0
      beta_reduce at this
      rw [this]; exact hn0.le
    · intro τ' ⟨hτ0, hτs, hτl⟩
      have hrev : lpRevenue M (fun j => if j.val = 0 then t else 0) = M.r i0 * t := by
        unfold lpRevenue; rw [hsum (fun j => M.r j)]
      rw [hrev]
      unfold lpRevenue
      have hmono : ∀ j : Fin K, M.r j ≤ M.r i0 := by
        intro j
        exact M.r_strictAnti.antitone (show i0 ≤ j from Nat.zero_le _)
      calc ∑ j, M.r j * τ' j ≤ ∑ j, M.r i0 * τ' j :=
            Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hmono j) (hτ0 j))
        _ = M.r i0 * ∑ j, τ' j := by rw [Finset.mul_sum]
        _ ≤ M.r i0 * t := mul_le_mul_of_nonneg_left hτs hr0
  · intro hn1
    have hK1 : K - 1 < K := by omega
    have hl := gvr_lamN M hK1
    set il : Fin K := ⟨K - 1, hK1⟩ with hil
    have hlpos : 0 < M.lam il := M.lam_pos _
    rw [hl] at hn1 ⊢
    have hsum : ∀ g : Fin K → ℝ, ∑ j : Fin K, g j * (if j.val = K - 1 then n / M.lam il else 0) =
        g il * (n / M.lam il) := by
      intro g
      rw [Finset.sum_eq_single il]
      · simp [hil]
      · intro j _ hj
        have : j.val ≠ K - 1 := fun h => hj (Fin.ext h)
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hnl : 0 ≤ n / M.lam il := div_nonneg hn hlpos.le
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · intro j; beta_reduce; split_ifs
      · exact hnl
      · exact le_rfl
    · have := hsum (fun _ => 1); simp only [one_mul] at this
      rw [this, div_le_iff₀ hlpos]; linarith
    · have := hsum (fun j => M.lam j)
      beta_reduce at this
      rw [this]; field_simp; exact le_rfl
    · intro τ' ⟨hτ0, hτs, hτl⟩
      have hrev : lpRevenue M (fun j => if j.val = K - 1 then n / M.lam il else 0) =
          M.p il * n := by
        unfold lpRevenue; rw [hsum (fun j => M.r j)]
        simp only [Menu.r]; field_simp
      rw [hrev]
      unfold lpRevenue
      have hpm : ∀ j : Fin K, M.p j ≤ M.p il := fun j =>
        M.p_strictMono.monotone (by simp [hil, Fin.le_def]; omega)
      calc ∑ j, M.r j * τ' j = ∑ j, M.p j * (M.lam j * τ' j) := by
            refine Finset.sum_congr rfl (fun j _ => ?_); simp only [Menu.r]; ring
        _ ≤ ∑ j, M.p il * (M.lam j * τ' j) :=
            Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hpm j)
              (mul_nonneg (M.lam_pos j).le (hτ0 j)))
        _ = M.p il * ∑ j, M.lam j * τ' j := by rw [Finset.mul_sum]
        _ ≤ M.p il * n := mul_le_mul_of_nonneg_left hτl (M.p_nonneg _)


lemma gvr_det_eq {K : ℕ} (M : Menu K) (n t : ℝ) (τ : Fin K → ℝ) (h : IsLPSolution M n t τ) :
    detValue M n t = lpRevenue M τ := by
  unfold detValue
  have : IsGreatest (lpRevenue M '' {τ | Feasible M n t τ}) (lpRevenue M τ) :=
    ⟨⟨τ, h.1, rfl⟩, by rintro _ ⟨τ', hτ', rfl⟩; exact h.2 τ' hτ'⟩
  exact this.csSup_eq

lemma gvr_det_closed {K : ℕ} (M : Menu K) (k : ℕ) (hk : k + 1 < K) (n t : ℝ) (hn : 0 ≤ n)
    (ht : 0 < t) (hup : n ≤ M.lamN k * t) (hlow : M.lamN (k + 1) * t < n) :
    detValue M n t =
        (M.rN k - M.rN (k + 1)) / (M.lamN k - M.lamN (k + 1)) * n
          + (M.lamN k * M.rN (k + 1) - M.lamN (k + 1) * M.rN k) / (M.lamN k - M.lamN (k + 1)) * t := by
  have hk0 : k < K := by omega
  have hsol := (gvr_prop4 M n t hn ht).1 k hk hup hlow
  rw [gvr_det_eq M n t _ hsol]
  have hrev : lpRevenue M (twoPriceAlloc M k n t) =
      M.r ⟨k, hk0⟩ * ((n - M.lamN (k + 1) * t) / (M.lamN k - M.lamN (k + 1))) +
        M.r ⟨k + 1, hk⟩ * ((M.lamN k * t - n) / (M.lamN k - M.lamN (k + 1))) := by
    unfold lpRevenue twoPriceAlloc
    exact gvr_sum_two k hk (fun j => M.r j) _ _
  rw [hrev, ← gvr_rN M hk0, ← gvr_rN M hk]
  have hab : M.lamN (k + 1) < M.lamN k := by
    rw [gvr_lamN M hk0, gvr_lamN M hk]
    exact M.lam_strictAnti (show (⟨k, hk0⟩ : Fin K) < ⟨k + 1, hk⟩ from by simp)
  have : M.lamN k - M.lamN (k + 1) ≠ 0 := by linarith
  field_simp
  ring

lemma gvr_alg (a b t tK m n p0 p1 : ℝ) (ha : 0 < a) (hab : a < b)
    (hΔ : tK * (b - a) = n - a * t) :
    (b * (p1 * a) - a * (p0 * b)) / (b - a) * (t - (m / b + (n - m) / a)) =
      (p1 - p0) * (m - b * tK) := by
  have hΔ0 : b - a ≠ 0 := by linarith
  have hb : 0 < b := by linarith
  have ha0 : a ≠ 0 := ha.ne'
  have hb0 : b ≠ 0 := hb.ne'
  have ht : t = (n - tK * (b - a)) / a := by
    field_simp; linarith
  subst ht
  field_simp
  ring

lemma gvr_pois0 (c : ℝ) (hc : 0 ≤ c) :
    HasSum (fun i : ℕ => Real.exp (-c) * c ^ i / (i.factorial : ℝ)) 1 := by
  have := ProbabilityTheory.hasSum_one_poissonMeasure c.toNNReal
  simpa [Real.coe_toNNReal c hc] using this

lemma gvr_pois1 (c : ℝ) (hc : 0 ≤ c) :
    HasSum (fun i : ℕ => (i : ℝ) * (Real.exp (-c) * c ^ i / (i.factorial : ℝ))) c := by
  have h0 := gvr_pois0 c hc
  have h1 : HasSum (fun i : ℕ => c * (Real.exp (-c) * c ^ i / (i.factorial : ℝ))) c := by
    simpa using h0.mul_left c
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_mul, sub_zero]
  convert h1 using 1
  all_goals try rfl
  funext i
  rw [Nat.factorial_succ]
  push_cast
  have h1' : ((i : ℝ) + 1) ≠ 0 := by positivity
  have h2' : (i.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

lemma gvr_pois2 (c : ℝ) (hc : 0 ≤ c) :
    HasSum (fun i : ℕ => ((i : ℝ) * ((i : ℝ) - 1)) * (Real.exp (-c) * c ^ i / (i.factorial : ℝ)))
      (c ^ 2) := by
  have h0 := gvr_pois0 c hc
  have h1 : HasSum (fun i : ℕ => c ^ 2 * (Real.exp (-c) * c ^ i / (i.factorial : ℝ))) (c ^ 2) := by
    simpa using h0.mul_left (c ^ 2)
  rw [← hasSum_nat_add_iff' 2]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num
  convert h1 using 1
  all_goals try rfl
  funext i
  rw [Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  have h1' : ((i : ℝ) + 1) ≠ 0 := by positivity
  have h2' : ((i : ℝ) + 2) ≠ 0 := by positivity
  have h3' : (i.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

lemma gvr_pois_min (c : ℝ) (hc : 0 ≤ c) :
    c - 1 / 2 * Real.sqrt c ≤ expMinPoisson c c := by
  set q : ℕ → ℝ := fun i => Real.exp (-c) * c ^ i / (i.factorial : ℝ) with hq
  have hq0 : ∀ i, 0 ≤ q i := fun i => by positivity
  have hemp : expMinPoisson c c = ∑' i : ℕ, min (i : ℝ) c * q i := by
    unfold expMinPoisson
    rw [max_eq_left hc]
  have h0 : HasSum q 1 := gvr_pois0 c hc
  have h1 : HasSum (fun i : ℕ => (i : ℝ) * q i) c := gvr_pois1 c hc
  have h2 : HasSum (fun i : ℕ => ((i : ℝ) * ((i : ℝ) - 1)) * q i) (c ^ 2) := gvr_pois2 c hc
  have hminnn : ∀ i : ℕ, 0 ≤ min (i : ℝ) c := fun i => le_min (Nat.cast_nonneg i) hc
  have hsumm : Summable (fun i : ℕ => min (i : ℝ) c * q i) :=
    Summable.of_nonneg_of_le (fun i => mul_nonneg (hminnn i) (hq0 i))
      (fun i => mul_le_mul_of_nonneg_right (min_le_left _ _) (hq0 i)) h1.summable
  rw [hemp]
  rcases hc.eq_or_lt with h | hpos
  · subst h
    have : ∀ i : ℕ, min (i : ℝ) 0 * q i = 0 := fun i => by
      rw [min_eq_right (Nat.cast_nonneg i)]; ring
    simp [this]
  · set s : ℝ := Real.sqrt c with hs
    have hspos : 0 < s := Real.sqrt_pos.mpr hpos
    have hss : s * s = c := Real.mul_self_sqrt hc
    have amgm : ∀ z : ℝ, z ≤ z ^ 2 / (2 * s) + s / 2 := by
      intro z
      have : 0 ≤ (z - s) ^ 2 / (2 * s) := by positivity
      have e : z ^ 2 / (2 * s) + s / 2 - z = (z - s) ^ 2 / (2 * s) := by
        field_simp; ring
      linarith
    set g : ℕ → ℝ := fun i => c - (((i : ℝ) - c) ^ 2 / (2 * s) + s / 2) / 2 - (c - i) / 2 with hg
    have hgle : ∀ i : ℕ, g i ≤ min (i : ℝ) c := by
      intro i
      have e : ((i : ℝ) - c) ^ 2 = (c - i) ^ 2 := by ring
      by_cases hi : (i : ℝ) ≤ c
      · rw [min_eq_left hi]
        have := amgm (c - i)
        simp only [hg]; rw [e]; linarith
      · push Not at hi
        rw [min_eq_right hi.le]
        have := amgm ((i : ℝ) - c)
        simp only [hg]; linarith
    have hsumg : HasSum (fun i : ℕ => g i * q i) (c - s / 2) := by
      have h := ((h0.mul_left (c - c ^ 2 / (4 * s) - s / 4 - c / 2)).add
        (h1.mul_left (-(1 - 2 * c) / (4 * s) + 1 / 2))).add (h2.mul_left (-1 / (4 * s)))
      have hval : (c - c ^ 2 / (4 * s) - s / 4 - c / 2) * 1 + (-(1 - 2 * c) / (4 * s) + 1 / 2) * c
          + (-1 / (4 * s)) * c ^ 2 = c - s / 2 := by
        rw [← hss]; field_simp; ring
      have hfun : (fun i : ℕ => g i * q i) = (fun i : ℕ => (c - c ^ 2 / (4 * s) - s / 4 - c / 2) * q i +
          (-(1 - 2 * c) / (4 * s) + 1 / 2) * ((i : ℝ) * q i) +
          (-1 / (4 * s)) * (((i : ℝ) * ((i : ℝ) - 1)) * q i)) := by
        funext i
        simp only [hg]
        ring
      rw [hfun, ← hval]
      exact h
    exact le_trans (by linarith) (hasSum_le (fun i => mul_le_mul_of_nonneg_right (hgle i) (hq0 i))
      hsumg hsumm.hasSum)

lemma gvr_regime {K : ℕ} (M : Menu K) (k : ℕ) (hk : k + 1 < K) (n : ℕ) (t : ℝ)
    (hup : (n : ℝ) ≤ M.lamN k * t) (hlow : M.lamN (k + 1) * t < n) :
    1 ≤ stM M k n t ∧ stM M k n t ≤ n ∧ 0 < shrunkHorizon M k n t ∧
    (n : ℝ) ≤ M.lamN k * shrunkHorizon M k n t ∧
    M.lamN (k + 1) * shrunkHorizon M k n t < n ∧
    stM M k n (shrunkHorizon M k n t) = stM M k n t := by
  have hk0 : k < K := by omega
  have hab : M.lamN (k + 1) < M.lamN k := by
    rw [gvr_lamN M hk0, gvr_lamN M hk]
    exact M.lam_strictAnti (show (⟨k, hk0⟩ : Fin K) < ⟨k + 1, hk⟩ from by simp)
  have hapos : 0 < M.lamN (k + 1) := by rw [gvr_lamN M hk]; exact M.lam_pos _
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  set a := M.lamN (k + 1) with ha
  set b := M.lamN k with hb
  have hbpos : 0 < b := by linarith
  have htK : tK M k n t = (n - a * t) / (b - a) := rfl
  have hx0 : 0 < b * tK M k n t := by
    rw [htK]; exact mul_pos hbpos (div_pos (by linarith) (by linarith))
  have hxn : b * tK M k n t ≤ n := by
    rw [htK, ← mul_div_assoc, div_le_iff₀ (by linarith)]
    nlinarith
  have hm : stM M k n t = ⌈b * tK M k n t⌉₊ := rfl
  have hm1 : 0 < stM M k n t := by rw [hm]; exact Nat.ceil_pos.2 hx0
  have hmn : stM M k n t ≤ n := by rw [hm]; exact Nat.ceil_le.2 hxn
  set m : ℕ := stM M k n t with hmdef
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
  have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have ht' : shrunkHorizon M k n t = (m : ℝ) / b + ((n : ℝ) - m) / a := rfl
  set t' := shrunkHorizon M k n t with ht'def
  have ht'pos : 0 < t' := by
    rw [ht']
    have : 0 ≤ ((n : ℝ) - m) / a := div_nonneg (by linarith) hapos.le
    have : 0 < (m : ℝ) / b := by positivity
    linarith
  have hup' : (n : ℝ) ≤ b * t' := by
    rw [ht']
    have : b * ((m : ℝ) / b + ((n : ℝ) - m) / a) = m + b * (((n : ℝ) - m) / a) := by
      field_simp
    rw [this]
    have h1 : ((n : ℝ) - m) ≤ b * (((n : ℝ) - m) / a) := by
      rw [← mul_div_assoc, le_div_iff₀ hapos]
      nlinarith
    linarith
  have hlow' : a * t' < n := by
    rw [ht']
    have : a * ((m : ℝ) / b + ((n : ℝ) - m) / a) = a * m / b + ((n : ℝ) - m) := by
      field_simp
    rw [this]
    have h1 : a * m / b < m := by
      rw [div_lt_iff₀ hbpos]; nlinarith
    linarith
  refine ⟨hm1, hmn, ht'pos, hup', hlow', ?_⟩
  -- stM at t'
  have e : b * tK M k n t' = m := by
    have : tK M k n t' = (n - a * t') / (b - a) := rfl
    rw [this, ht']
    have hba : b - a ≠ 0 := by linarith
    have ha0 : a ≠ 0 := hapos.ne'
    have hb0 : b ≠ 0 := hbpos.ne'
    field_simp
    ring
  show ⌈b * tK M k n t'⌉₊ = m
  rw [e, Nat.ceil_natCast]

lemma gvr_ratio (pk pk1 u v : ℝ) (hpk : 0 ≤ pk) (hpk1 : 0 < pk1) (hu : 0 < u) (hv : 0 < v) :
    1 - 1 / 2 * (1 / u + 1 / v) ≤
      (pk * (u * u - 1 / 2 * u) + pk1 * (v * v - 1 / 2 * v)) / (pk * (u * u) + pk1 * (v * v)) := by
  have hD : 0 < pk * (u * u) + pk1 * (v * v) := by positivity
  rw [le_div_iff₀ hD]
  have e : (pk * (u * u - 1 / 2 * u) + pk1 * (v * v - 1 / 2 * v)) -
      (1 - 1 / 2 * (1 / u + 1 / v)) * (pk * (u * u) + pk1 * (v * v)) =
      1 / 2 * (pk * (u * u) / v + pk1 * (v * v) / u) := by
    field_simp
    ring
  have : 0 ≤ 1 / 2 * (pk * (u * u) / v + pk1 * (v * v) / u) := by positivity
  linarith

theorem solution {K : ℕ} (M : Menu K) (k : ℕ) (hk : k + 1 < K) (n : ℕ) (t : ℝ)
    (hup : (n : ℝ) ≤ M.lamN k * t) (hlow : M.lamN (k + 1) * t < n) :
    M.pN k * ((stM M k n t : ℝ) - 1 / 2 * Real.sqrt (stM M k n t))
        + M.pN (k + 1) * (((n : ℝ) - stM M k n t) - 1 / 2 * Real.sqrt ((n : ℝ) - stM M k n t))
      ≤ jW M k n (shrunkHorizon M k n t) ∧
    detValue M n (shrunkHorizon M k n t)
      = M.pN k * stM M k n t + M.pN (k + 1) * ((n : ℝ) - stM M k n t) ∧
    (stM M k n t < n →
      1 - 1 / 2 * (1 / Real.sqrt (stM M k n t) + 1 / Real.sqrt ((n : ℝ) - stM M k n t))
        ≤ jW M k n (shrunkHorizon M k n t) / detValue M n (shrunkHorizon M k n t)) := by
  have hk0 : k < K := by omega
  obtain ⟨hm1, hmn, ht'pos, hup', hlow', hst⟩ := gvr_regime M k hk n t hup hlow
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hab : M.lamN (k + 1) < M.lamN k := by
    rw [gvr_lamN M hk0, gvr_lamN M hk]
    exact M.lam_strictAnti (show (⟨k, hk0⟩ : Fin K) < ⟨k + 1, hk⟩ from by simp)
  have hapos : 0 < M.lamN (k + 1) := by rw [gvr_lamN M hk]; exact M.lam_pos _
  have hpp : M.pN k < M.pN (k + 1) := by
    rw [gvr_pN M hk0, gvr_pN M hk]
    exact M.p_strictMono (show (⟨k, hk0⟩ : Fin K) < ⟨k + 1, hk⟩ from by simp)
  have hpk0 : 0 ≤ M.pN k := by rw [gvr_pN M hk0]; exact M.p_nonneg _
  set a := M.lamN (k + 1) with ha
  set b := M.lamN k with hb
  have hbpos : 0 < b := by linarith
  set m : ℕ := stM M k n t with hmdef
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
  have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have ht' : shrunkHorizon M k n t = (m : ℝ) / b + ((n : ℝ) - m) / a := rfl
  set t' := shrunkHorizon M k n t with ht'def
  -- part 2
  have hdet : detValue M n t' = M.pN k * m + M.pN (k + 1) * ((n : ℝ) - m) := by
    rw [gvr_det_closed M k hk n t' hn0 ht'pos hup' hlow']
    rw [← ha, ← hb]
    have hrN0 : M.rN k = M.pN k * b := rfl
    have hrN1 : M.rN (k + 1) = M.pN (k + 1) * a := rfl
    rw [hrN0, hrN1, ht']
    have hba : b - a ≠ 0 := by linarith
    have ha0 : a ≠ 0 := hapos.ne'
    have hb0 : b ≠ 0 := hbpos.ne'
    field_simp
    ring
  -- part 1
  have hjW : jW M k n t' = M.pN k * expMinPoisson (m : ℝ) (m : ℝ) +
      M.pN (k + 1) * expMinPoisson (((n : ℝ) - m)) (((n : ℝ) - m)) := by
    unfold jW
    have hst' : stM M k n t' = m := hst
    have htm : tm M k n t' = (m : ℝ) / b := by unfold tm; rw [hst']
    rw [hst', htm]
    have e1 : b * ((m : ℝ) / b) = m := by field_simp
    have e2 : a * (t' - (m : ℝ) / b) = (n : ℝ) - m := by
      rw [ht']; field_simp; ring
    rw [e1, e2]
  have hE1 := gvr_pois_min (m : ℝ) hmpos.le
  have hE2 := gvr_pois_min ((n : ℝ) - m) (by linarith)
  have hpk1 : 0 ≤ M.pN (k + 1) := by linarith
  have hlow1 : M.pN k * ((m : ℝ) - 1 / 2 * Real.sqrt m) +
      M.pN (k + 1) * (((n : ℝ) - m) - 1 / 2 * Real.sqrt ((n : ℝ) - m)) ≤ jW M k n t' := by
    rw [hjW]
    exact add_le_add (mul_le_mul_of_nonneg_left hE1 hpk0) (mul_le_mul_of_nonneg_left hE2 hpk1)
  refine ⟨hlow1, hdet, ?_⟩
  intro hmlt
  have hmltR : (m : ℝ) < n := by exact_mod_cast hmlt
  have hnm : 0 < (n : ℝ) - m := by linarith
  have hu : 0 < Real.sqrt m := Real.sqrt_pos.mpr hmpos
  have hv : 0 < Real.sqrt ((n : ℝ) - m) := Real.sqrt_pos.mpr hnm
  have hr := gvr_ratio (M.pN k) (M.pN (k + 1)) (Real.sqrt m) (Real.sqrt ((n : ℝ) - m)) hpk0
    (by linarith) hu hv
  rw [Real.mul_self_sqrt hmpos.le, Real.mul_self_sqrt hnm.le] at hr
  rw [hdet]
  have hD : 0 < M.pN k * m + M.pN (k + 1) * ((n : ℝ) - m) := by
    have : 0 < M.pN (k + 1) * ((n : ℝ) - m) := mul_pos (by linarith) hnm
    nlinarith
  exact le_trans hr (div_le_div_of_nonneg_right hlow1 hD.le)
