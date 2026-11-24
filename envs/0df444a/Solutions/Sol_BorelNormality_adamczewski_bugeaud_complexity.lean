-- Prove2me | solution 1 for BorelNormality.adamczewski_bugeaud_complexity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T22:04:11.360163+00:00
-- url     : https://prove2.me/submissions/ce932ce5-a67a-4998-9a00-92a15308b6a4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Normal_Core
import Definitions.Def_BorelNormality_Complexity
import Theorems.Thm_LefebvreVariations_algebraic_mul_pow_sub_pow_finite

set_option autoImplicit false

open scoped Classical

open BorelNormality


/-- A list of length `n` with entries `< b` belongs to `strs b n`. -/
private lemma mem_strs_of {b : ℕ} : ∀ (n : ℕ) (l : List ℕ), l.length = n →
    (∀ d ∈ l, d < b) → l ∈ Normal.strs b n
  | 0, l, hl, _ => by
    rw [List.length_eq_zero_iff] at hl
    subst hl; simp [Normal.strs]
  | n + 1, [], hl, _ => by simp at hl
  | n + 1, d :: l, hl, hd => by
    simp only [Normal.strs, Finset.mem_image, Finset.mem_product, Finset.mem_range]
    refine ⟨(d, l), ⟨hd d (by simp), mem_strs_of n l (by simpa using hl)
      (fun e he => hd e (by simp [he]))⟩, rfl⟩

/-- `D d b i n = d i b^(n-1) + ⋯ + d (i+n-1)`, the integer written by `n` digits from `i`. -/
private def Dv (d : ℕ → ℕ) (b i : ℕ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => (b : ℤ) * Dv d b i n + d (i + n)

private lemma Dv_congr (d : ℕ → ℕ) (b i j : ℕ) :
    ∀ n, (∀ t < n, d (i + t) = d (j + t)) → Dv d b i n = Dv d b j n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [Dv]
    rw [Dv_congr d b i j n (fun t ht => h t (by omega)), h n (by omega)]

/-- `⌊ξ b^(m+1)⌋ = b ⌊ξ b^m⌋ + digit m`. -/
private lemma floor_succ (ξ : ℝ) {b : ℕ} (hb : 2 ≤ b) (m : ℕ) :
    ⌊ξ * (b : ℝ) ^ (m + 1)⌋ = (b : ℤ) * ⌊ξ * (b : ℝ) ^ m⌋ + (Normal.digit b ξ m : ℤ) := by
  set a := ⌊ξ * (b : ℝ) ^ m⌋ with ha
  set c := ⌊ξ * (b : ℝ) ^ (m + 1)⌋ with hc
  have hbpos : (0 : ℝ) < b := by positivity
  have h1 : (a : ℝ) ≤ ξ * (b : ℝ) ^ m := Int.floor_le _
  have h2 : ξ * (b : ℝ) ^ m < a + 1 := Int.lt_floor_add_one _
  have e : ξ * (b : ℝ) ^ (m + 1) = (ξ * (b : ℝ) ^ m) * b := by ring
  have hlo : (b : ℤ) * a ≤ c := by
    rw [hc, Int.le_floor, e]; push_cast; nlinarith
  have hhi : c < (b : ℤ) * a + b := by
    have : (c : ℝ) < (b : ℝ) * a + b := by
      calc (c : ℝ) ≤ ξ * (b : ℝ) ^ (m + 1) := Int.floor_le _
        _ < (b : ℝ) * a + b := by rw [e]; nlinarith
    exact_mod_cast this
  have hdig : (Normal.digit b ξ m : ℤ) = c % (b : ℤ) := by
    unfold Normal.digit
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))]
  rw [hdig]
  have hr : c = (c - b * a) + b * a := by ring
  have hmod : c % (b : ℤ) = c - b * a := by
    rw [hr, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
    ring
  rw [hmod]; ring

private lemma floor_add (ξ : ℝ) {b : ℕ} (hb : 2 ≤ b) (i : ℕ) :
    ∀ n, ⌊ξ * (b : ℝ) ^ (i + n)⌋ =
      (b : ℤ) ^ n * ⌊ξ * (b : ℝ) ^ i⌋ + Dv (Normal.digit b ξ) b i n
  | 0 => by simp [Dv]
  | n + 1 => by
    rw [show i + (n + 1) = (i + n) + 1 by omega, floor_succ ξ hb, floor_add ξ hb i n, Dv]
    ring

/-- Two equal blocks of `n` digits at positions `i` and `j` give
`|ξ (b^j - b^i) - (⌊ξ b^j⌋ - ⌊ξ b^i⌋)| < b^(-n)`. -/
private lemma approx (ξ : ℝ) {b : ℕ} (hb : 2 ≤ b) (i j n : ℕ)
    (h : ∀ t < n, Normal.digit b ξ (i + t) = Normal.digit b ξ (j + t)) :
    |ξ * ((b : ℝ) ^ j - (b : ℝ) ^ i) - ((⌊ξ * (b : ℝ) ^ j⌋ - ⌊ξ * (b : ℝ) ^ i⌋ : ℤ) : ℝ)| <
      ((b : ℝ) ^ n)⁻¹ := by
  have hD := Dv_congr (Normal.digit b ξ) b i j n h
  have fi := floor_add ξ hb i n
  have fj := floor_add ξ hb j n
  have hbn : (0 : ℝ) < (b : ℝ) ^ n := by positivity
  have li : ((⌊ξ * (b : ℝ) ^ (i + n)⌋ : ℤ) : ℝ) ≤ ξ * (b : ℝ) ^ (i + n) := Int.floor_le _
  have ui : ξ * (b : ℝ) ^ (i + n) < ((⌊ξ * (b : ℝ) ^ (i + n)⌋ : ℤ) : ℝ) + 1 :=
    Int.lt_floor_add_one _
  have lj : ((⌊ξ * (b : ℝ) ^ (j + n)⌋ : ℤ) : ℝ) ≤ ξ * (b : ℝ) ^ (j + n) := Int.floor_le _
  have uj : ξ * (b : ℝ) ^ (j + n) < ((⌊ξ * (b : ℝ) ^ (j + n)⌋ : ℤ) : ℝ) + 1 :=
    Int.lt_floor_add_one _
  rw [fi] at li ui
  rw [fj, ← hD] at lj uj
  push_cast at li ui lj uj
  rw [pow_add] at li ui lj uj
  set D : ℝ := (Dv (Normal.digit b ξ) b i n : ℝ)
  set Ai : ℝ := ((⌊ξ * (b : ℝ) ^ i⌋ : ℤ) : ℝ)
  set Aj : ℝ := ((⌊ξ * (b : ℝ) ^ j⌋ : ℤ) : ℝ)
  set B : ℝ := (b : ℝ) ^ n
  push_cast
  rw [abs_lt]; constructor
  · rw [neg_lt, ← one_div, lt_div_iff₀ hbn]; nlinarith
  · rw [← one_div, lt_div_iff₀ hbn]; nlinarith

/-- The digit word of length `n` at position `i`. -/
private noncomputable def dw (b : ℕ) (x : ℝ) (n i : ℕ) : List ℕ := List.ofFn (fun t : Fin n => Normal.digit b x (i + t))

private lemma digit_lt (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (m : ℕ) : Normal.digit b x m < b := by
  unfold Normal.digit
  have h0 := Int.emod_nonneg ⌊x * (b : ℝ) ^ (m + 1)⌋ (show (b : ℤ) ≠ 0 by omega)
  have h1 := Int.emod_lt_of_pos ⌊x * (b : ℝ) ^ (m + 1)⌋ (show (0 : ℤ) < b by omega)
  omega

/-- Values of `ξ (b^(r+s) - b^r) - p` on the triples are nonzero. -/
private lemma ne_zero_of_irr (ξ : ℝ) (hi : Irrational ξ) {b : ℕ} (hb : 2 ≤ b) (r s : ℕ)
    (hs : 1 ≤ s) (p : ℤ) : ξ * ((b : ℝ) ^ (r + s) - (b : ℝ) ^ r) - p ≠ 0 := by
  have hlt : (b : ℝ) ^ r < (b : ℝ) ^ (r + s) :=
    pow_lt_pow_right₀ (by exact_mod_cast (show 1 < b by omega)) (by omega)
  set q : ℚ := (b : ℚ) ^ (r + s) - (b : ℚ) ^ r
  have hq : q ≠ 0 := by
    intro h
    have : ((q : ℚ) : ℝ) = 0 := by rw [h]; simp
    simp only [q] at this; push_cast at this; linarith
  have hirr := hi.mul_ratCast hq
  intro h
  apply hirr.ne_int p
  simp only [q]; push_cast; linarith

theorem solution (x : ℝ) (hx : IsAlgebraic ℚ x) (hi : Irrational x)
    (b : ℕ) (hb : 2 ≤ b) :
    Filter.liminf (fun n : ℕ => (complexity b x n : ENNReal) / (n : ENNReal)) Filter.atTop = ⊤ := by
  by_contra hne
  obtain ⟨K, hK⟩ := ENNReal.exists_nat_gt hne
  have hfreq : ∃ᶠ n in Filter.atTop, (complexity b x n : ENNReal) / (n : ENNReal) < K :=
    Filter.frequently_lt_of_liminf_lt (by isBoundedDefault) hK
  have hKpos : 0 < K := by
    rcases Nat.eq_zero_or_pos K with h | h
    · subst h; simp at hK
    · exact h
  have hKr : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hfin := LefebvreVariations.algebraic_mul_pow_sub_pow_finite x hx hi b hb (1 / K)
    (by positivity)
  set S := {t : ℕ × ℕ × ℤ | 1 ≤ t.2.1 ∧
      |x * ((b : ℝ) ^ (t.1 + t.2.1) - (b : ℝ) ^ t.1) - t.2.2| <
        (b : ℝ) ^ (-((1 / (K : ℝ)) * ((t.1 + t.2.1 : ℕ) : ℝ)))} with hSdef
  set f : ℕ × ℕ × ℤ → ℝ := fun t => |x * ((b : ℝ) ^ (t.1 + t.2.1) - (b : ℝ) ^ t.1) - t.2.2|
  obtain ⟨δ, hδ, hδS⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ S, δ ≤ f t := by
    rcases S.eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · obtain ⟨t0, ht0, hmin⟩ := hfin.toFinset.exists_min_image f (by simpa using h)
      rw [Set.Finite.mem_toFinset] at ht0
      exact ⟨f t0, abs_pos.2 (ne_zero_of_irr x hi hb _ _ ht0.1 _),
        fun t ht => hmin t (by simpa using ht)⟩
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (show 1 < b by omega)
  have hev : ∀ᶠ n in Filter.atTop, 1 ≤ n ∧ ((b : ℝ) ^ n)⁻¹ < δ := by
    have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (r := ((b : ℝ))⁻¹) (by positivity)
      (inv_lt_one_of_one_lt₀ hb1)
    filter_upwards [(tendsto_order.1 ht).2 δ hδ, Filter.eventually_ge_atTop 1] with n hn h1
    exact ⟨h1, by rwa [← inv_pow]⟩
  obtain ⟨n, hn, hn1, hnδ⟩ := (hfreq.and_eventually hev).exists
  -- `p(n) < K n`
  have hpn : complexity b x n < K * n := by
    have hn0 : (n : ENNReal) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    rw [ENNReal.div_lt_iff (Or.inl hn0) (Or.inl (ENNReal.natCast_ne_top n))] at hn
    exact_mod_cast hn
  -- pigeonhole on the `p(n) + 1` positions `0, …, p(n)`
  have hc : complexity b x n = ((Normal.strs b n).filter
      (fun w => ∃ N : ℕ, 0 < Normal.count (Normal.digit b x) w N)).card := rfl
  have hmaps : ∀ i ∈ Finset.range (complexity b x n + 1), dw b x n i ∈ (Normal.strs b n).filter
      (fun w => ∃ N : ℕ, 0 < Normal.count (Normal.digit b x) w N) := by
    intro i _
    rw [Finset.mem_filter]
    refine ⟨mem_strs_of n _ (by simp [dw]) ?_, ⟨i + 1, ?_⟩⟩
    · intro d hd
      simp only [dw, List.mem_ofFn] at hd
      obtain ⟨t, rfl⟩ := hd
      exact digit_lt b hb x _
    · unfold Normal.count
      apply Finset.card_pos.2
      refine ⟨i, Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_succ_self i), ?_⟩⟩
      rintro ⟨j, hj⟩
      simp only [List.get_eq_getElem]
      simp [dw]
  obtain ⟨i, hi', j, hj', hij, hwij⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (by rw [Finset.card_range, ← hc]; omega) hmaps
  rw [Finset.mem_range] at hi' hj'
  -- the key step, for an ordered pair
  have key : ∀ i j, i < j → j ≤ complexity b x n → dw b x n i = dw b x n j → False := by
    intro i j hlt hj hw
    have hdig : ∀ t < n, Normal.digit b x (i + t) = Normal.digit b x (j + t) := by
      intro t ht
      have := congrArg (fun l => l.getD t 0) hw
      simpa [dw, List.getD_eq_getElem?_getD, List.getElem?_ofFn, ht] using this
    have hap := approx x hb i j n hdig
    have hmem : (i, j - i, ⌊x * (b : ℝ) ^ j⌋ - ⌊x * (b : ℝ) ^ i⌋) ∈ S := by
      refine ⟨by simp; omega, ?_⟩
      simp only [show i + (j - i) = j by omega]
      refine lt_of_lt_of_le hap ?_
      rw [← Real.rpow_natCast, ← Real.rpow_neg (by positivity)]
      apply Real.rpow_le_rpow_of_exponent_le hb1.le
      have hjK : (j : ℝ) ≤ K * n := by exact_mod_cast (show j ≤ K * n by omega)
      rw [neg_le_neg_iff, one_div, inv_mul_le_iff₀ hKr]
      exact hjK
    have := hδS _ hmem
    simp only [f, show i + (j - i) = j by omega] at this
    linarith
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h (by omega) hwij
  · exact key j i h (by omega) hwij.symm
