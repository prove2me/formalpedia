-- Prove2me | solution 1 for BudgetClock.Subadditive.theorem_8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T13:13:29.832819+00:00
-- url     : https://prove2.me/submissions/1fb7453a-3fbb-4500-81ac-162ce2dfcc16

import Mathlib
import Definitions.Def_BudgetClock_Subadditive_Mechanism
import Theorems.Thm_BudgetClock_Subadditive_z_bound
import Theorems.Thm_BudgetClock_Subadditive_value_monotone

open BudgetClock.Subadditive

/-- Budget invariant: both maintained solutions are paid at most `B`. -/
private lemma bc8_phase_inv {n : ℕ} (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) (hB : 0 < B)
    (alg : ℕ → Finset (Fin n) → Finset (Fin n)) (halg : IsTwoApproxOracle v alg)
    (s : State n) (h1 : ∑ i ∈ s.Sprev, s.p i ≤ B) (h2 : ∑ i ∈ s.Scurr, s.p i ≤ B) :
    (∑ i ∈ (phase v c B alg s).Sprev, (phase v c B alg s).p i ≤ B) ∧
      (∑ i ∈ (phase v c B alg s).Scurr, (phase v c B alg s).p i ≤ B) := by
  constructor
  · simp only [phase]
    have hb : ∀ i ∈ better v s.Sprev s.Scurr,
        (if i ∈ s.A \ better v s.Sprev s.Scurr then B / ((s.t + 1 : ℕ) : ℝ) else s.p i) = s.p i := by
      intro i hi
      rw [if_neg]
      simp [hi]
    rw [Finset.sum_congr rfl hb]
    unfold better
    split_ifs
    · exact h2
    · exact h1
  · simp only [phase]
    set t : ℕ := s.t + 1 with ht
    set Sp := better v s.Sprev s.Scurr
    set A' := s.A \ (s.A \ Sp).filter (fun i => B / (t : ℝ) < c i)
    obtain ⟨hsub, hcard, -⟩ := halg t (A' \ Sp)
    have hR : ∀ i ∈ alg t (A' \ Sp),
        (if i ∈ s.A \ Sp then B / (t : ℝ) else s.p i) = B / (t : ℝ) := by
      intro i hi
      have := hsub hi
      rw [if_pos]
      simp only [Finset.mem_sdiff, A'] at this ⊢
      exact ⟨this.1.1, this.2⟩
    rw [Finset.sum_congr rfl hR, Finset.sum_const, nsmul_eq_mul]
    have htpos : (0 : ℝ) < t := by rw [ht]; positivity
    rw [mul_div_assoc', div_le_iff₀ htpos]
    have : ((alg t (A' \ Sp)).card : ℝ) ≤ t := by exact_mod_cast hcard
    nlinarith

private lemma bc8_run_inv {n : ℕ} (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) (hB : 0 < B)
    (alg : ℕ → Finset (Fin n) → Finset (Fin n)) (halg : IsTwoApproxOracle v alg) :
    ∀ (F : ℕ) (s : State n), ∑ i ∈ s.Sprev, s.p i ≤ B → ∑ i ∈ s.Scurr, s.p i ≤ B →
      (∑ i ∈ (run v c B alg F s).Sprev, (run v c B alg F s).p i ≤ B) ∧
        (∑ i ∈ (run v c B alg F s).Scurr, (run v c B alg F s).p i ≤ B) := by
  intro F
  induction F with
  | zero => intro s h1 h2; exact ⟨h1, h2⟩
  | succ F ih =>
    intro s h1 h2
    simp only [run]
    split_ifs
    · obtain ⟨k1, k2⟩ := bc8_phase_inv v c B hB alg halg s h1 h2
      exact ih _ k1 k2
    · exact ⟨h1, h2⟩

private lemma bc8_budget {n : ℕ} (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ) (hB : 0 < B)
    (alg : ℕ → Finset (Fin n) → Finset (Fin n)) (halg : IsTwoApproxOracle v alg) (F : ℕ) :
    ∑ i ∈ (mechanism4 v c B alg F).1, (mechanism4 v c B alg F).2 i ≤ B := by
  have h0 : ∑ i ∈ (initState n B).Sprev, (initState n B).p i ≤ B := by
    simp [initState]; exact hB.le
  have h0' : ∑ i ∈ (initState n B).Scurr, (initState n B).p i ≤ B := by
    simp [initState]; exact hB.le
  obtain ⟨k1, k2⟩ := bc8_run_inv v c B hB alg halg F _ h0 h0'
  simp only [mechanism4, better]
  split_ifs
  · exact k2
  · exact k1

/-- Splitting a block whose costs are at most `B / q` into pieces of size at most `q`. -/
private lemma bc8_split {n : ℕ} (v : Finset (Fin n) → ℝ) (hsub : IsSubadditive v)
    (c : Fin n → ℝ) (B : ℝ) (hB : 0 < B) (V : ℝ)
    (hG : ∀ Z : Finset (Fin n), (∀ i ∈ Z, c i ≤ B / (Z.card : ℝ)) → v Z ≤ 4 * V)
    (hV : 0 ≤ V) (q : ℕ) (hq : 1 ≤ q) :
    ∀ (k : ℕ) (X : Finset (Fin n)), X.card = k → (∀ i ∈ X, c i ≤ B / (q : ℝ)) →
      v X ≤ ((X.card : ℝ) / q + 1) * (4 * V) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro X hXk hX
    by_cases hk : X.card ≤ q
    · have h4 : v X ≤ 4 * V := by
        apply hG
        intro i hi
        have hcpos : (0 : ℝ) < X.card := by
          exact_mod_cast Finset.card_pos.mpr ⟨i, hi⟩
        calc c i ≤ B / q := hX i hi
          _ ≤ B / X.card := by
            apply div_le_div_of_nonneg_left hB.le hcpos
            exact_mod_cast hk
      have : 0 ≤ (X.card : ℝ) / q * (4 * V) := by positivity
      nlinarith
    · push_neg at hk
      obtain ⟨Y, hYX, hYc⟩ := Finset.exists_subset_card_eq (s := X) (n := q) hk.le
      have hY : v Y ≤ 4 * V := by
        apply hG
        intro i hi
        rw [hYc]
        exact hX i (hYX hi)
      have hcd : (X \ Y).card = X.card - q := by rw [Finset.card_sdiff_of_subset hYX, hYc]
      have hlt : X.card - q < k := by omega
      have hXY := ih (X.card - q) hlt (X \ Y) hcd (fun i hi => hX i (Finset.mem_sdiff.mp hi).1)
      have hU : X = Y ∪ (X \ Y) := (Finset.union_sdiff_of_subset hYX).symm
      have h1 : v X ≤ v Y + v (X \ Y) := by
        conv_lhs => rw [hU]
        exact hsub _ _
      rw [hcd] at hXY
      have hcast : ((X.card - q : ℕ) : ℝ) = (X.card : ℝ) - q := by
        rw [Nat.cast_sub hk.le]
      rw [hcast] at hXY
      have e : ((X.card : ℝ) - q) / q + 1 = (X.card : ℝ) / q := by
        field_simp; ring
      rw [e] at hXY
      have e2 : ((X.card : ℝ) / q + 1) * (4 * V) = 4 * V + (X.card : ℝ) / q * (4 * V) := by ring
      rw [e2]
      linarith

/-- Telescoping over the cost classes `T j = {i ∈ O : c i ≤ B / ρ^j}`. -/
private lemma bc8_tele {n : ℕ} (v : Finset (Fin n) → ℝ) (hsub : IsSubadditive v)
    (c : Fin n → ℝ) (B : ℝ) (hB : 0 < B) (V : ℝ)
    (hG : ∀ Z : Finset (Fin n), (∀ i ∈ Z, c i ≤ B / (Z.card : ℝ)) → v Z ≤ 4 * V)
    (hV : 0 ≤ V) (ρ : ℕ) (hρ : 1 ≤ ρ) (O : Finset (Fin n)) (hOB : ∀ i ∈ O, c i ≤ B) :
    ∀ J : ℕ, v O ≤ 4 * V * (J + (ρ / B) * (∑ i ∈ O, c i -
        ∑ i ∈ O.filter (fun i => c i ≤ B / (ρ : ℝ) ^ J), c i)) +
        v (O.filter (fun i => c i ≤ B / (ρ : ℝ) ^ J)) := by
  have hρpos : (0 : ℝ) < ρ := by exact_mod_cast hρ
  have hρ1 : (1 : ℝ) ≤ ρ := by exact_mod_cast hρ
  intro J
  induction J with
  | zero =>
    have : O.filter (fun i => c i ≤ B / (ρ : ℝ) ^ 0) = O := by
      apply Finset.filter_true_of_mem
      intro i hi; simpa using hOB i hi
    rw [this]; simp
  | succ J ih =>
    set T := O.filter (fun i => c i ≤ B / (ρ : ℝ) ^ J)
    set T' := O.filter (fun i => c i ≤ B / (ρ : ℝ) ^ (J + 1))
    have hpJ : (0 : ℝ) < (ρ : ℝ) ^ J := by positivity
    have hmono : B / (ρ : ℝ) ^ (J + 1) ≤ B / (ρ : ℝ) ^ J := by
      apply div_le_div_of_nonneg_left hB.le hpJ
      rw [pow_succ]; nlinarith
    have hsubT : T' ⊆ T := by
      intro i hi
      simp only [T', T, Finset.mem_filter] at hi ⊢
      exact ⟨hi.1, hi.2.trans hmono⟩
    set D := T \ T'
    have hU : T = D ∪ T' := (Finset.sdiff_union_of_subset hsubT).symm
    have h1 : v T ≤ v D + v T' := by
      conv_lhs => rw [hU]
      exact hsub _ _
    have hsum : ∑ i ∈ T, c i = ∑ i ∈ D, c i + ∑ i ∈ T', c i :=
      (Finset.sum_sdiff hsubT).symm
    have hDc : ∀ i ∈ D, c i ≤ B / (((ρ ^ J : ℕ) : ℕ) : ℝ) := by
      intro i hi
      simp only [D, T, Finset.mem_sdiff, Finset.mem_filter] at hi
      push_cast; exact hi.1.2
    have hq : 1 ≤ ρ ^ J := Nat.one_le_pow _ _ hρ
    have hD := bc8_split v hsub c B hB V hG hV (ρ ^ J) hq D.card D rfl hDc
    push_cast at hD
    -- `|D| / ρ^J ≤ (ρ / B) * ∑_D c`
    have hlow : ∀ i ∈ D, B / (ρ : ℝ) ^ (J + 1) ≤ c i := by
      intro i hi
      simp only [D, T, T', Finset.mem_sdiff, Finset.mem_filter, not_and, not_le] at hi
      exact (hi.2 hi.1.1).le
    have hcard : (D.card : ℝ) * (B / (ρ : ℝ) ^ (J + 1)) ≤ ∑ i ∈ D, c i := by
      have := Finset.card_nsmul_le_sum D c (B / (ρ : ℝ) ^ (J + 1)) hlow
      rw [nsmul_eq_mul] at this; exact this
    have hkey : (D.card : ℝ) / (ρ : ℝ) ^ J ≤ (ρ / B) * ∑ i ∈ D, c i := by
      have e : (D.card : ℝ) / (ρ : ℝ) ^ J =
          (ρ / B) * ((D.card : ℝ) * (B / (ρ : ℝ) ^ (J + 1))) := by
        generalize (D.card : ℝ) = d
        have h1 := hB.ne'
        have h2 := hpJ.ne'
        have h3 := hρpos.ne'
        rw [pow_succ]
        field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_left hcard (by positivity)
    have h4V : 0 ≤ 4 * V := by linarith
    have hD' : v D ≤ ((ρ / B) * ∑ i ∈ D, c i + 1) * (4 * V) :=
      hD.trans (mul_le_mul_of_nonneg_right (by linarith) h4V)
    have e : 4 * V * (((J + 1 : ℕ) : ℝ) + (ρ / B) * (∑ i ∈ O, c i - ∑ i ∈ T', c i)) =
        4 * V * (J + (ρ / B) * (∑ i ∈ O, c i - ∑ i ∈ T, c i)) +
          ((ρ / B) * ∑ i ∈ D, c i + 1) * (4 * V) := by
      rw [hsum]; push_cast; ring
    rw [e]
    linarith [ih, h1, hD']

/-- Choice of the number of cost classes: with `x = log n > 1`, `ρ = ⌈√x⌉` and
`J = ⌈x / log ρ⌉` satisfy `n ≤ ρ^J` and `J + ρ + 2 ≤ 8 x / log x`. -/
private lemma bc8_numbers (n : ℕ) (hn : 3 ≤ n) :
    ∃ ρ J : ℕ, 1 ≤ ρ ∧ (n : ℝ) ≤ (ρ : ℝ) ^ J ∧
      (J : ℝ) + ρ + 2 ≤ 8 * (Real.log n / Real.log (Real.log n)) := by
  set x := Real.log n with hxdef
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hx1 : 1 < x := by
    have h3 : (1 : ℝ) < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      have := Real.exp_one_lt_d9
      linarith
    exact h3.trans_le (Real.log_le_log (by norm_num) hn3)
  have hxpos : 0 < x := by linarith
  set lx := Real.log x with hlxdef
  have hlx : 0 < lx := Real.log_pos hx1
  have hlxx : lx < x := by
    have := Real.log_le_sub_one_of_pos hxpos
    linarith
  set s := Real.sqrt x with hsdef
  have hs1 : 1 < s := by
    rw [hsdef, Real.lt_sqrt (by norm_num)]; linarith
  have hspos : 0 < s := by linarith
  have hss : s * s = x := Real.mul_self_sqrt hxpos.le
  have hls : Real.log s = lx / 2 := by
    rw [hsdef, Real.log_sqrt hxpos.le]
  -- `lx ≤ 2 (s - 1)`
  have hlxs : lx ≤ 2 * (s - 1) := by
    have := Real.log_le_sub_one_of_pos hspos
    linarith
  set ρ := ⌈s⌉₊ with hρdef
  have hρs : s ≤ (ρ : ℝ) := Nat.le_ceil s
  have hρlt : (ρ : ℝ) < s + 1 := Nat.ceil_lt_add_one hspos.le
  have hρpos : (0 : ℝ) < ρ := by linarith
  have hρ1 : 1 ≤ ρ := by exact_mod_cast (show (1 : ℝ) ≤ ρ by linarith)
  have hlρ : lx / 2 ≤ Real.log ρ := by
    rw [← hls]; exact Real.log_le_log hspos hρs
  have hlρpos : 0 < Real.log ρ := by linarith
  set J := ⌈x / Real.log ρ⌉₊ with hJdef
  have hJ1 : x / Real.log ρ ≤ (J : ℝ) := Nat.le_ceil _
  have hJ2 : (J : ℝ) < x / Real.log ρ + 1 :=
    Nat.ceil_lt_add_one (div_nonneg hxpos.le hlρpos.le)
  refine ⟨ρ, J, hρ1, ?_, ?_⟩
  · have hpow : (0 : ℝ) < (ρ : ℝ) ^ J := by positivity
    rw [← Real.log_le_log_iff hnpos hpow, Real.log_pow]
    rw [div_le_iff₀ hlρpos] at hJ1
    rw [← hxdef]; linarith
  · -- `x / log ρ ≤ 2 x / lx`
    have h1 : x / Real.log ρ ≤ 2 * (x / lx) := by
      rw [div_le_iff₀ hlρpos]
      have : 2 * (x / lx) * Real.log ρ ≥ 2 * (x / lx) * (lx / 2) :=
        mul_le_mul_of_nonneg_left hlρ (by positivity)
      have e : 2 * (x / lx) * (lx / 2) = x := by field_simp
      linarith
    -- `s ≤ 2 x / lx`
    have h2 : s ≤ 2 * (x / lx) := by
      rw [show 2 * (x / lx) = 2 * x / lx by ring, le_div_iff₀ hlx]
      nlinarith
    have h3 : 1 < x / lx := by rw [lt_div_iff₀ hlx]; linarith
    show (J : ℝ) + ρ + 2 ≤ 8 * (x / lx)
    linarith

theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ), 3 ≤ n →
      ∀ (v : Finset (Fin n) → ℝ), (∀ S, 0 ≤ v S) → IsSubadditive v →
      ∀ (c : Fin n → ℝ), (∀ i, 0 ≤ c i) →
      ∀ (B : ℝ), 0 < B →
      ∀ (alg : ℕ → Finset (Fin n) → Finset (Fin n)), IsTwoApproxOracle v alg →
      ∀ (F : ℕ), n ≤ F →
        (∑ i ∈ (mechanism4 v c B alg F).1, (mechanism4 v c B alg F).2 i ≤ B) ∧
        ∀ O : Finset (Fin n), ∑ i ∈ O, c i ≤ B →
          v O ≤ C * (Real.log n / Real.log (Real.log n)) *
            v (mechanism4 v c B alg F).1 := by
  refine ⟨32, by norm_num, ?_⟩
  intro n hn v hv hsub c hc B hB alg halg F hnF
  refine ⟨bc8_budget v c B hB alg halg F, ?_⟩
  intro O hO
  set V := v (mechanism4 v c B alg F).1 with hVdef
  have hV : 0 ≤ V := hv _
  -- every admissible block is worth at most `4 V`
  have hG : ∀ Z : Finset (Fin n), (∀ i ∈ Z, c i ≤ B / (Z.card : ℝ)) → v Z ≤ 4 * V := by
    intro Z hZ
    rcases Z.eq_empty_or_nonempty with h | h
    · subst h
      have hm := value_monotone v c B alg 0 F (Nat.zero_le F)
      have e : (mechanism4 v c B alg 0).1 = ∅ := by
        simp [mechanism4, run, initState, better]
      rw [e] at hm
      linarith
    · have hcard : 1 ≤ Z.card := Finset.card_pos.mpr h
      have hZF : Z.card ≤ F := by
        have := Finset.card_le_univ Z
        simp only [Fintype.card_fin] at this
        omega
      exact z_bound v hv hsub c hc B hB alg halg F Z hcard hZF hZ
  have hOB : ∀ i ∈ O, c i ≤ B := fun i hi =>
    (Finset.single_le_sum (fun j _ => hc j) hi).trans hO
  obtain ⟨ρ, J, hρ1, hnρ, hnum⟩ := bc8_numbers n hn
  have htele := bc8_tele v hsub c B hB V hG hV ρ hρ1 O hOB J
  set T := O.filter (fun i => c i ≤ B / (ρ : ℝ) ^ J)
  have hq : 1 ≤ ρ ^ J := Nat.one_le_pow _ _ hρ1
  have hTc : ∀ i ∈ T, c i ≤ B / (((ρ ^ J : ℕ) : ℕ) : ℝ) := by
    intro i hi
    simp only [T, Finset.mem_filter] at hi
    push_cast; exact hi.2
  have hT := bc8_split v hsub c B hB V hG hV (ρ ^ J) hq T.card T rfl hTc
  push_cast at hT
  have hpJ : (0 : ℝ) < (ρ : ℝ) ^ J := by positivity
  have hTcard : (T.card : ℝ) / (ρ : ℝ) ^ J ≤ 1 := by
    rw [div_le_one hpJ]
    have : T.card ≤ n := by
      have := Finset.card_le_univ T
      simpa using this
    have : (T.card : ℝ) ≤ n := by exact_mod_cast this
    linarith
  have hT8 : v T ≤ 8 * V := by nlinarith
  have hsumT : 0 ≤ ∑ i ∈ T, c i := Finset.sum_nonneg (fun i _ => hc i)
  have hρB : (ρ : ℝ) / B * (∑ i ∈ O, c i - ∑ i ∈ T, c i) ≤ ρ := by
    have h0 : ∑ i ∈ O, c i - ∑ i ∈ T, c i ≤ B := by linarith
    calc (ρ : ℝ) / B * (∑ i ∈ O, c i - ∑ i ∈ T, c i) ≤ (ρ : ℝ) / B * B :=
          mul_le_mul_of_nonneg_left h0 (by positivity)
      _ = ρ := by field_simp
  have h4V : 0 ≤ 4 * V := by linarith
  have hstep : v O ≤ 4 * V * ((J : ℝ) + ρ + 2) := by
    have := mul_le_mul_of_nonneg_left hρB h4V
    nlinarith
  have := mul_le_mul_of_nonneg_left hnum h4V
  nlinarith
