-- Prove2me | solution 1 for BuckPassing.Det.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T18:05:48.66744+00:00
-- url     : https://prove2.me/submissions/637b6e60-4581-4e3f-b8eb-f0bef8a07806

import Mathlib
import Definitions.Def_BuckPassing_Det_Model
set_option autoImplicit false
open Classical Finset Filter BuckPassing.Det

section bpL1
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem bp_mem_cycleOf (f : V → V) (i j : V) : j ∈ cycleOf f i ↔ ∃ t : ℕ, f^[t] i = j := by
  simp [cycleOf]

theorem bp_mem_basin (f : V → V) (C : Finset V) (j : V) : j ∈ basin f C ↔ ∃ t : ℕ, f^[t] j ∈ C := by
  simp [basin]

theorem bp_iter_period (f : V → V) (k : V) (n : ℕ) (hk : f^[n] k = k) (m s : ℕ) :
    f^[s + n * m] k = f^[s] k := by
  induction m with
  | zero => simp
  | succ m ih =>
    have : s + n * (m + 1) = (s + n * m) + n := by ring
    rw [this, Function.iterate_add_apply, hk, ih]

/-- a point on the orbit of a periodic point `i` that is periodic-hitting -/
theorem bp_basin_iff_hits (f : V → V) (i : V) (hi : i ∈ Function.periodicPts f) (j : V) :
    j ∈ basin f (cycleOf f i) ↔ ∃ t : ℕ, f^[t] j = i := by
  rw [bp_mem_basin]
  constructor
  · rintro ⟨t, ht⟩
    rw [bp_mem_cycleOf] at ht
    obtain ⟨s, hs⟩ := ht
    obtain ⟨n, hn, hper⟩ := Function.mem_periodicPts.mp hi
    have hper' : f^[n] i = i := hper
    refine ⟨(n * s - s) + t, ?_⟩
    rw [Function.iterate_add_apply, ← hs, ← Function.iterate_add_apply]
    have : n * s - s + s = 0 + n * s := by
      have : s ≤ n * s := Nat.le_mul_of_pos_left s hn
      omega
    rw [this, bp_iter_period f i n hper']
    simp
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [ht, bp_mem_cycleOf]
    exact ⟨0, rfl⟩

theorem bp_card_cycleOf (f : V → V) (i : V) (hi : i ∈ Function.periodicPts f) :
    (cycleOf f i).card = Function.minimalPeriod f i := by
  have hp := Function.minimalPeriod_pos_of_mem_periodicPts hi
  have : cycleOf f i = (Finset.range (Function.minimalPeriod f i)).image (fun t => f^[t] i) := by
    ext j
    rw [bp_mem_cycleOf]
    simp only [Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t % Function.minimalPeriod f i, Nat.mod_lt _ hp, Function.iterate_mod_minimalPeriod_eq⟩
    · rintro ⟨t, -, rfl⟩
      exact ⟨t, rfl⟩
  rw [this, Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb hab
  exact Function.iterate_injOn_Iio_minimalPeriod (f := f) (x := i) (by simpa using ha) (by simpa using hb) hab

theorem bp_cycleOf_eq (f : V → V) (k i : V) (hk : k ∈ Function.periodicPts f) (t : ℕ)
    (hki : f^[t] k = i) : cycleOf f k = cycleOf f i := by
  obtain ⟨n, hn, hper⟩ := Function.mem_periodicPts.mp hk
  have hper' : f^[n] k = k := hper
  ext j
  rw [bp_mem_cycleOf, bp_mem_cycleOf]
  constructor
  · rintro ⟨s, rfl⟩
    refine ⟨n * t + s - t, ?_⟩
    rw [← hki, ← Function.iterate_add_apply]
    have h1 : t ≤ n * t := Nat.le_mul_of_pos_left t hn
    have : n * t + s - t + t = s + n * t := by omega
    rw [this, bp_iter_period f k n hper']
  · rintro ⟨s, rfl⟩
    refine ⟨s + t, ?_⟩
    rw [← hki, ← Function.iterate_add_apply]


/-- visit set -/
theorem bp_visits_le_one (f : V → V) (j i : V)
    (h : ¬ (i ∈ Function.periodicPts f ∧ j ∈ basin f (cycleOf f i))) (T : ℕ) :
    ((Finset.Icc 1 T).filter (fun t => f^[t] j = i)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter] at ha hb
  by_contra hne
  apply h
  have key : ∀ a b : ℕ, f^[a] j = i → f^[b] j = i → a < b →
      (i ∈ Function.periodicPts f ∧ j ∈ basin f (cycleOf f i)) := by
    intro a b ha hb hab
    refine ⟨Function.mk_mem_periodicPts (n := b - a) (by omega) ?_, ?_⟩
    · show f^[b - a] i = i
      conv_lhs => rw [← ha]
      rw [← Function.iterate_add_apply, show b - a + a = b by omega, hb]
    · rw [bp_mem_basin]
      exact ⟨a, by rw [ha, bp_mem_cycleOf]; exact ⟨0, rfl⟩⟩
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact key a b ha.2 hb.2 hlt
  · exact key b a hb.2 ha.2 hlt

theorem bp_freq_tendsto_pos (f : V → V) (j i : V) (hi : i ∈ Function.periodicPts f)
    (hj : j ∈ basin f (cycleOf f i)) :
    Tendsto (fun T : ℕ =>
        (((Finset.Icc 1 T).filter (fun t => f^[t] j = i)).card : ℝ) / T) atTop
      (nhds ((1 : ℝ) / (cycleOf f i).card)) := by
  rw [bp_card_cycleOf f i hi]
  have hp : 0 < Function.minimalPeriod f i := Function.minimalPeriod_pos_of_mem_periodicPts hi
  have hper : f^[Function.minimalPeriod f i] i = i := Function.iterate_minimalPeriod
  have hdvd : ∀ m : ℕ, f^[m] i = i → Function.minimalPeriod f i ∣ m := fun m hm =>
    Function.isPeriodicPt_iff_minimalPeriod_dvd.mp hm
  generalize Function.minimalPeriod f i = p at *
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  obtain ⟨n0, hn0⟩ := (bp_basin_iff_hits f i hi j).mp hj
  -- shift so that N ≥ 1
  obtain ⟨N, hN1, hN⟩ : ∃ N : ℕ, 1 ≤ N ∧ f^[N] j = i := by
    refine ⟨p + n0, by omega, ?_⟩
    rw [Function.iterate_add_apply, hn0]
    exact hper
  have hvis : ∀ m : ℕ, f^[N + p * m] j = i := by
    intro m
    rw [add_comm, Function.iterate_add_apply, hN]
    have := bp_iter_period f i p hper m 0
    simpa using this
  have hlow : ∀ T : ℕ, N ≤ T → (T - N) / p + 1 ≤
      ((Finset.Icc 1 T).filter (fun t => f^[t] j = i)).card := by
    intro T hT
    have hsub : (Finset.range ((T - N) / p + 1)).image (fun m => N + p * m) ⊆
        (Finset.Icc 1 T).filter (fun t => f^[t] j = i) := by
      intro t ht
      simp only [Finset.mem_image, Finset.mem_range] at ht
      obtain ⟨m, hm, rfl⟩ := ht
      have hm' : m ≤ (T - N) / p := by omega
      have : m * p ≤ T - N := (Nat.le_div_iff_mul_le hp).mp hm'
      simp only [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by omega, ?_⟩, hvis m⟩
      rw [Nat.mul_comm] at this
      omega
    calc (T - N) / p + 1 = ((Finset.range ((T - N) / p + 1)).image (fun m => N + p * m)).card := by
          rw [Finset.card_image_of_injective, Finset.card_range]
          intro a b hab
          simp only at hab
          have : p * a = p * b := by omega
          exact Nat.eq_of_mul_eq_mul_left hp this
      _ ≤ _ := Finset.card_le_card hsub
  have hup : ∀ T : ℕ, ((Finset.Icc 1 T).filter (fun t => f^[t] j = i)).card ≤ N + (T / p + 1) := by
    intro T
    have hsub : (Finset.Icc 1 T).filter (fun t => f^[t] j = i) ⊆
        Finset.range N ∪ (Finset.range (T / p + 1)).image (fun m => N + p * m) := by
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_Icc] at ht
      obtain ⟨⟨h1, h2⟩, h3⟩ := ht
      simp only [Finset.mem_union, Finset.mem_range, Finset.mem_image]
      by_cases htN : t < N
      · exact Or.inl htN
      · right
        have h4 : f^[t - N] i = i := by
          have : f^[t] j = f^[t - N] i := by
            rw [← hN, ← Function.iterate_add_apply, show t - N + N = t by omega]
          rw [← this, h3]
        obtain ⟨m, hm⟩ := hdvd _ h4
        refine ⟨m, ?_, by omega⟩
        have : m ≤ T / p := by
          rw [Nat.le_div_iff_mul_le hp, Nat.mul_comm]
          omega
        omega
    calc _ ≤ (Finset.range N ∪ (Finset.range (T / p + 1)).image (fun m => N + p * m)).card :=
          Finset.card_le_card hsub
      _ ≤ (Finset.range N).card + ((Finset.range (T / p + 1)).image (fun m => N + p * m)).card :=
          Finset.card_union_le _ _
      _ ≤ N + (T / p + 1) := by
          rw [Finset.card_range]
          exact Nat.add_le_add_left (Finset.card_image_le.trans (by simp)) _
  have hlowR : ∀ T : ℕ, N ≤ T →
      ((T : ℝ) - N) / p ≤ (((Finset.Icc 1 T).filter (fun t => f^[t] j = i)).card : ℝ) := by
    intro T hT
    have h1 := hlow T hT
    have h2 : ((T - N : ℕ) : ℝ) < p * (((T - N) / p : ℕ) + 1 : ℕ) := by
      exact_mod_cast Nat.lt_mul_div_succ (T - N) hp
    have h3 : (((T - N) / p + 1 : ℕ) : ℝ) ≤ (((Finset.Icc 1 T).filter (fun t => f^[t] j = i)).card : ℝ) := by exact_mod_cast h1
    rw [Nat.cast_sub hT] at h2
    rw [div_le_iff₀ hpR]
    push_cast at h2 h3
    nlinarith
  have hupR : ∀ T : ℕ,
      (((Finset.Icc 1 T).filter (fun t => f^[t] j = i)).card : ℝ) ≤ N + 1 + (T : ℝ) / p := by
    intro T
    have h1 := hup T
    have h2 : ((T / p : ℕ) : ℝ) ≤ (T : ℝ) / p := Nat.cast_div_le
    have h3 : (((Finset.Icc 1 T).filter (fun t => f^[t] j = i)).card : ℝ) ≤ ((N + (T / p + 1) : ℕ) : ℝ) := by
      exact_mod_cast h1
    push_cast at h3
    linarith
  have hlim0 : ∀ C : ℝ, Tendsto (fun T : ℕ => C / (T : ℝ)) atTop (nhds 0) :=
    fun C => tendsto_const_div_atTop_nhds_zero_nat C
  have hL : Tendsto (fun T : ℕ => (1 : ℝ) / p - (N / p) / (T : ℝ)) atTop (nhds ((1 : ℝ) / p)) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ) / p)).sub (hlim0 ((N : ℝ) / p))
  have hU : Tendsto (fun T : ℕ => (1 : ℝ) / p + (N + 1 : ℝ) / (T : ℝ)) atTop (nhds ((1 : ℝ) / p)) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ) / p)).add (hlim0 ((N + 1 : ℝ)))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hU ?_ ?_
  · filter_upwards [eventually_ge_atTop (max N 1)] with T hT
    have hT1 : N ≤ T := le_trans (le_max_left _ _) hT
    have hT2 : (0 : ℝ) < T := by exact_mod_cast lt_of_lt_of_le (by omega : 0 < max N 1) hT
    rw [le_div_iff₀ hT2]
    have := hlowR T hT1
    have e : ((1 : ℝ) / p - (N / p) / (T : ℝ)) * T = ((T : ℝ) - N) / p := by
      field_simp
    rw [e]; exact this
  · filter_upwards [eventually_ge_atTop (max N 1)] with T hT
    have hT2 : (0 : ℝ) < T := by exact_mod_cast lt_of_lt_of_le (by omega : 0 < max N 1) hT
    rw [div_le_iff₀ hT2]
    have := hupR T
    have e : ((1 : ℝ) / p + (N + 1 : ℝ) / (T : ℝ)) * T = (T : ℝ) / p + (N + 1) := by
      field_simp
    rw [e]; linarith

theorem bp_freq_tendsto (f : V → V) (j i : V) :
    Tendsto (fun T : ℕ =>
        (((Finset.Icc 1 T).filter (fun t => f^[t] j = i)).card : ℝ) / T) atTop
      (nhds (if i ∈ Function.periodicPts f ∧ j ∈ basin f (cycleOf f i)
               then (1 : ℝ) / (cycleOf f i).card else 0)) := by
  by_cases h : i ∈ Function.periodicPts f ∧ j ∈ basin f (cycleOf f i)
  · rw [if_pos h]; exact bp_freq_tendsto_pos f j i h.1 h.2
  · rw [if_neg h]
    have hlim0 : Tendsto (fun T : ℕ => (1 : ℝ) / (T : ℝ)) atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat 1
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim0 ?_ ?_
    · exact Eventually.of_forall fun T => by positivity
    · exact Eventually.of_forall fun T => by
        have := bp_visits_le_one f j i h T
        have h1 : ((((Finset.Icc 1 T).filter (fun t => f^[t] j = i)).card : ℕ) : ℝ) ≤ 1 := by
          exact_mod_cast this
        exact div_le_div_of_nonneg_right h1 (by positivity)


theorem bp_freq_eq (f : V → V) (j i : V) :
    freq f j i = (if i ∈ Function.periodicPts f ∧ j ∈ basin f (cycleOf f i)
               then (1 : ℝ) / (cycleOf f i).card else 0) :=
  (bp_freq_tendsto f j i).limUnder_eq

theorem bp_cost_eq (G : BPGraph V) (mu : V → ℝ) (s : ∀ i, Strat G i) (i : V) :
    cost G mu i s =
      if i ∈ Function.periodicPts (toMap s) then
        basinMass mu (toMap s) (cycleOf (toMap s) i) / (cycleOf (toMap s) i).card
      else 0 := by
  simp only [cost, bp_freq_eq]
  by_cases hi : i ∈ Function.periodicPts (toMap s)
  · rw [if_pos hi]
    simp only [hi, true_and]
    unfold basinMass
    rw [Finset.sum_div, ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun x => x ∈ basin (toMap s) (cycleOf (toMap s) i))]
    have h1 : (Finset.univ.filter (fun x => x ∈ basin (toMap s) (cycleOf (toMap s) i))) =
        basin (toMap s) (cycleOf (toMap s) i) := by ext; simp
    rw [h1]
    have h2 : ∑ x ∈ Finset.univ.filter (fun x => ¬ x ∈ basin (toMap s) (cycleOf (toMap s) i)),
        mu x * (if x ∈ basin (toMap s) (cycleOf (toMap s) i) then 1 / ((cycleOf (toMap s) i).card : ℝ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      simp only [Finset.mem_filter] at hx
      simp [hx.2]
    rw [h2, add_zero]
    apply Finset.sum_congr rfl
    intro x hx
    rw [if_pos hx]; ring
  · rw [if_neg hi]
    simp [hi]

end bpL1

section bpL2
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem bp_upd_iter (f : V → V) (i x j : V) (n : ℕ) (h : ∀ s < n, f^[s] j ≠ i) :
    ∀ s ≤ n, (Function.update f i x)^[s] j = f^[s] j := by
  intro s
  induction s with
  | zero => intro _; rfl
  | succ s ih =>
    intro hs
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih (by omega)]
    exact Function.update_of_ne (h s (by omega)) _ _

theorem bp_upd_iter' (f : V → V) (i x j : V) (n : ℕ)
    (h : ∀ s < n, (Function.update f i x)^[s] j ≠ i) :
    ∀ s ≤ n, (Function.update f i x)^[s] j = f^[s] j := by
  intro s
  induction s with
  | zero => intro _; rfl
  | succ s ih =>
    intro hs
    have h1 := h s (by omega)
    have h2 := ih (by omega)
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', h2]
    rw [h2] at h1
    exact Function.update_of_ne h1 _ _

theorem bp_upd_nohit (f : V → V) (i x j : V) (hj : ∀ s, f^[s] j ≠ i) (s : ℕ) :
    (Function.update f i x)^[s] j = f^[s] j :=
  bp_upd_iter f i x j s (fun r _ => hj r) s le_rfl

/-- first hit time, simultaneously for `f` and `f'` -/
theorem bp_first_hit (f : V → V) (i x k : V) (hk : ∃ t, f^[t] k = i) :
    ∃ t, f^[t] k = i ∧ (Function.update f i x)^[t] k = i := by
  classical
  let t0 := Nat.find hk
  have h0 : f^[t0] k = i := Nat.find_spec hk
  have hmin : ∀ s < t0, f^[s] k ≠ i := fun s hs => Nat.find_min hk hs
  refine ⟨t0, h0, ?_⟩
  rw [bp_upd_iter f i x k t0 hmin t0 le_rfl]; exact h0

theorem bp_first_hit' (f : V → V) (i x k : V) (hk : ∃ t, (Function.update f i x)^[t] k = i) :
    ∃ t, f^[t] k = i ∧ (Function.update f i x)^[t] k = i := by
  classical
  let t0 := Nat.find hk
  have h0 : (Function.update f i x)^[t0] k = i := Nat.find_spec hk
  have hmin : ∀ s < t0, (Function.update f i x)^[s] k ≠ i := fun s hs => Nat.find_min hk hs
  refine ⟨t0, ?_, h0⟩
  rw [← bp_upd_iter' f i x k t0 hmin t0 le_rfl]; exact h0

theorem bp_cycles_mem (g : V → V) (C : Finset V) :
    C ∈ cycles g ↔ ∃ k, k ∈ Function.periodicPts g ∧ cycleOf g k = C := by
  simp [cycles]

noncomputable def bpS (f : V → V) (i : V) : Finset (Finset V) :=
  (Finset.univ.filter (fun k => k ∈ Function.periodicPts f ∧ ¬ ∃ t, f^[t] k = i)).image (cycleOf f)

theorem bp_mem_bpS (f : V → V) (i : V) (C : Finset V) :
    C ∈ bpS f i ↔ ∃ k, (k ∈ Function.periodicPts f ∧ ¬ ∃ t, f^[t] k = i) ∧ cycleOf f k = C := by
  simp [bpS]

theorem bp_self_mem_cycleOf (g : V → V) (i : V) : i ∈ cycleOf g i := by
  rw [bp_mem_cycleOf]; exact ⟨0, rfl⟩

theorem bp_not_mem_bpS (f : V → V) (i : V) (C : Finset V) (hC : i ∈ C) : C ∉ bpS f i := by
  rw [bp_mem_bpS]
  rintro ⟨k, ⟨-, hk⟩, rfl⟩
  exact hk ((bp_mem_cycleOf f k i).mp hC)

theorem bp_cycles_f (f : V → V) (i : V) (hi : i ∈ Function.periodicPts f) :
    cycles f = insert (cycleOf f i) (bpS f i) := by
  ext C
  rw [Finset.mem_insert, bp_cycles_mem, bp_mem_bpS]
  constructor
  · rintro ⟨k, hk, rfl⟩
    by_cases h : ∃ t, f^[t] k = i
    · obtain ⟨t, ht⟩ := h
      exact Or.inl (bp_cycleOf_eq f k i hk t ht)
    · exact Or.inr ⟨k, ⟨hk, h⟩, rfl⟩
  · rintro (rfl | ⟨k, ⟨hk, -⟩, rfl⟩)
    · exact ⟨i, hi, rfl⟩
    · exact ⟨k, hk, rfl⟩

theorem bp_nohit_cycle (f : V → V) (i x k : V) (hk : ¬ ∃ t, f^[t] k = i) :
    cycleOf (Function.update f i x) k = cycleOf f k ∧
    (k ∈ Function.periodicPts (Function.update f i x) ↔ k ∈ Function.periodicPts f) := by
  have hj : ∀ s, f^[s] k ≠ i := fun s hs => hk ⟨s, hs⟩
  have he := bp_upd_nohit f i x k hj
  refine ⟨?_, ?_⟩
  · ext j
    rw [bp_mem_cycleOf, bp_mem_cycleOf]
    simp only [he]
  · rw [Function.mem_periodicPts, Function.mem_periodicPts]
    simp only [Function.IsPeriodicPt, Function.IsFixedPt, he]

theorem bp_hit_not_periodic (f : V → V) (i x k : V) (hx : ¬ ∃ t, f^[t] x = i)
    (hk : ∃ t, f^[t] k = i) : k ∉ Function.periodicPts (Function.update f i x) := by
  intro hper
  obtain ⟨t0, h0, h0'⟩ := bp_first_hit f i x k hk
  obtain ⟨n, hn, hperk⟩ := Function.mem_periodicPts.mp hper
  have hperk' : (Function.update f i x)^[n] k = k := hperk
  set f' := Function.update f i x with hf'
  have h1 : f'^[t0 + 1] k = x := by
    rw [Function.iterate_succ_apply', h0', hf', Function.update_self]
  have h2 : f'^[(n * (t0 + 1) - (t0 + 1)) + (t0 + 1)] k = k := by
    have hle : t0 + 1 ≤ n * (t0 + 1) := Nat.le_mul_of_pos_left _ hn
    rw [show n * (t0 + 1) - (t0 + 1) + (t0 + 1) = 0 + n * (t0 + 1) by omega,
      bp_iter_period f' k n hperk']
    rfl
  rw [Function.iterate_add_apply, h1] at h2
  have hxs : ∀ s, f^[s] x ≠ i := fun s hs => hx ⟨s, hs⟩
  rw [bp_upd_nohit f i x x hxs] at h2
  obtain ⟨t, ht⟩ := hk
  exact hx ⟨(t + (n * (t0 + 1) - (t0 + 1))), by
    rw [Function.iterate_add_apply, h2, ht]⟩


theorem bp_cycles_nohit (f : V → V) (i x : V) (hx : ¬ ∃ t, f^[t] x = i) :
    cycles (Function.update f i x) = bpS f i ∧ i ∉ Function.periodicPts (Function.update f i x) := by
  refine ⟨?_, bp_hit_not_periodic f i x i hx ⟨0, rfl⟩⟩
  ext C
  rw [bp_cycles_mem, bp_mem_bpS]
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hnh : ¬ ∃ t, f^[t] k = i := fun h => bp_hit_not_periodic f i x k hx h hk
    obtain ⟨h1, h2⟩ := bp_nohit_cycle f i x k hnh
    exact ⟨k, ⟨h2.mp hk, hnh⟩, h1.symm⟩
  · rintro ⟨k, ⟨hk, hnh⟩, rfl⟩
    obtain ⟨h1, h2⟩ := bp_nohit_cycle f i x k hnh
    exact ⟨k, h2.mpr hk, h1⟩

theorem bp_cycles_hit (f : V → V) (i x : V) (hx : ∃ t, f^[t] x = i) :
    i ∈ Function.periodicPts (Function.update f i x) ∧
    cycles (Function.update f i x) = insert (cycleOf (Function.update f i x) i) (bpS f i) ∧
    (∀ j, j ∈ basin (Function.update f i x) (cycleOf (Function.update f i x) i) ↔
        ∃ t, f^[t] j = i) := by
  have hi' : i ∈ Function.periodicPts (Function.update f i x) := by
    obtain ⟨t, ht, ht'⟩ := bp_first_hit f i x x hx
    refine Function.mk_mem_periodicPts (n := t + 1) (by omega) ?_
    show (Function.update f i x)^[t + 1] i = i
    rw [Function.iterate_succ_apply, Function.update_self]
    exact ht'
  refine ⟨hi', ?_, ?_⟩
  · ext C
    rw [Finset.mem_insert, bp_cycles_mem, bp_mem_bpS]
    constructor
    · rintro ⟨k, hk, rfl⟩
      by_cases h : ∃ t, f^[t] k = i
      · obtain ⟨t, ht, ht'⟩ := bp_first_hit f i x k h
        exact Or.inl (bp_cycleOf_eq _ k i hk t ht')
      · obtain ⟨h1, h2⟩ := bp_nohit_cycle f i x k h
        exact Or.inr ⟨k, ⟨h2.mp hk, h⟩, h1.symm⟩
    · rintro (rfl | ⟨k, ⟨hk, hnh⟩, rfl⟩)
      · exact ⟨i, hi', rfl⟩
      · obtain ⟨h1, h2⟩ := bp_nohit_cycle f i x k hnh
        exact ⟨k, h2.mpr hk, h1⟩
  · intro j
    rw [bp_basin_iff_hits _ i hi']
    constructor
    · rintro h
      obtain ⟨t, ht, -⟩ := bp_first_hit' f i x j h
      exact ⟨t, ht⟩
    · rintro h
      obtain ⟨t, -, ht'⟩ := bp_first_hit f i x j h
      exact ⟨t, ht'⟩

theorem bp_psi_nohit (f : V → V) (i x : V) (hi : i ∈ Function.periodicPts f)
    (hx : ¬ ∃ t, f^[t] x = i) :
    ∑ C ∈ cycles (Function.update f i x), ((Fintype.card V : ℝ) - C.card) =
      ∑ C ∈ cycles f, ((Fintype.card V : ℝ) - C.card) -
        ((Fintype.card V : ℝ) - (cycleOf f i).card) := by
  rw [(bp_cycles_nohit f i x hx).1, bp_cycles_f f i hi,
    Finset.sum_insert (bp_not_mem_bpS f i _ (bp_self_mem_cycleOf f i))]
  ring

theorem bp_psi_hit (f : V → V) (i x : V) (hi : i ∈ Function.periodicPts f)
    (hx : ∃ t, f^[t] x = i) :
    ∑ C ∈ cycles (Function.update f i x), ((Fintype.card V : ℝ) - C.card) =
      ∑ C ∈ cycles f, ((Fintype.card V : ℝ) - C.card) -
        ((Fintype.card V : ℝ) - (cycleOf f i).card) +
        ((Fintype.card V : ℝ) - (cycleOf (Function.update f i x) i).card) := by
  rw [(bp_cycles_hit f i x hx).2.1, bp_cycles_f f i hi,
    Finset.sum_insert (bp_not_mem_bpS f i _ (bp_self_mem_cycleOf _ i)),
    Finset.sum_insert (bp_not_mem_bpS f i _ (bp_self_mem_cycleOf f i))]
  ring

end bpL2

section bpL3
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem bp_toMap_update (G : BPGraph V) (s : ∀ i, Strat G i) (i : V) (x : Strat G i) :
    toMap (Function.update s i x) = Function.update (toMap s) i x.1 := by
  funext k
  by_cases h : k = i
  · subst h; simp [toMap]
  · simp [toMap, h]

theorem bp_basinMass_nonneg (mu : V → ℝ) (hmu : IsDistribution mu) (f : V → V) (C : Finset V) :
    0 ≤ basinMass mu f C :=
  Finset.sum_nonneg fun j _ => hmu.1 j

theorem bp_cost_nonneg (G : BPGraph V) (mu : V → ℝ) (hmu : IsDistribution mu)
    (s : ∀ i, Strat G i) (i : V) : 0 ≤ cost G mu i s := by
  rw [bp_cost_eq]
  split_ifs
  · exact div_nonneg (bp_basinMass_nonneg mu hmu _ _) (Nat.cast_nonneg _)
  · exact le_rfl

/-- The core of the deviation analysis. -/
theorem bp_dev_core (G : BPGraph V) (mu : V → ℝ) (hmu : IsDistribution mu)
    (s : ∀ i, Strat G i) (i : V) (x : Strat G i)
    (hlt : cost G mu i (Function.update s i x) < cost G mu i s) :
    i ∈ Function.periodicPts (toMap s) ∧
    0 < basinMass mu (toMap s) (cycleOf (toMap s) i) ∧
    ((x.1 ∈ basin (toMap s) (cycleOf (toMap s) i) ∧
        (cycleOf (toMap s) i).card < (cycleOf (toMap (Function.update s i x)) i).card ∧
        i ∈ Function.periodicPts (toMap (Function.update s i x)) ∧
        Psi G (Function.update s i x) < Psi G s) ∨
      (x.1 ∉ basin (toMap s) (cycleOf (toMap s) i) ∧
        i ∉ Function.periodicPts (toMap (Function.update s i x)) ∧
        Psi G (Function.update s i x) < Psi G s)) := by
  have hnn := bp_cost_nonneg G mu hmu (Function.update s i x) i
  have hupd := bp_toMap_update G s i x
  have hi : i ∈ Function.periodicPts (toMap s) := by
    by_contra hi
    rw [bp_cost_eq G mu s i, if_neg hi] at hlt
    linarith
  have hcpos : 0 < ((cycleOf (toMap s) i).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨i, bp_self_mem_cycleOf _ i⟩
  have hbasis := bp_basin_iff_hits (toMap s) i hi
  by_cases hx : x.1 ∈ basin (toMap s) (cycleOf (toMap s) i)
  · have hx' : ∃ t, (toMap s)^[t] x.1 = i := (hbasis _).mp hx
    obtain ⟨hi', hcyc, hbas⟩ := bp_cycles_hit (toMap s) i x.1 hx'
    rw [← hupd] at hi' hbas hcyc
    have hmass : basinMass mu (toMap (Function.update s i x)) (cycleOf (toMap (Function.update s i x)) i)
        = basinMass mu (toMap s) (cycleOf (toMap s) i) := by
      unfold basinMass
      apply Finset.sum_congr
      · ext j
        rw [hbas, hbasis]
      · intro _ _; rfl
    rw [bp_cost_eq G mu s i, bp_cost_eq G mu (Function.update s i x) i, if_pos hi', if_pos hi, hmass] at hlt
    have hc'pos : 0 < ((cycleOf (toMap (Function.update s i x)) i).card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr ⟨i, bp_self_mem_cycleOf _ i⟩
    have hm := bp_basinMass_nonneg mu hmu (toMap s) (cycleOf (toMap s) i)
    have hmpos : 0 < basinMass mu (toMap s) (cycleOf (toMap s) i) := by
      rcases hm.lt_or_eq with h | h
      · exact h
      · rw [← h] at hlt; simp at hlt
    have hcc : ((cycleOf (toMap s) i).card : ℝ) <
        ((cycleOf (toMap (Function.update s i x)) i).card : ℝ) :=
      (div_lt_div_iff_of_pos_left hmpos hc'pos hcpos).mp hlt
    have hpsi : Psi G (Function.update s i x) = Psi G s
        - ((Fintype.card V : ℝ) - (cycleOf (toMap s) i).card)
        + ((Fintype.card V : ℝ) - (cycleOf (toMap (Function.update s i x)) i).card) := by
      unfold Psi
      simp only [hupd]
      exact bp_psi_hit (toMap s) i x.1 hi hx'
    refine ⟨hi, hmpos, Or.inl ⟨hx, by exact_mod_cast hcc, hi', ?_⟩⟩
    rw [hpsi]; linarith
  · have hx' : ¬ ∃ t, (toMap s)^[t] x.1 = i := fun h => hx ((hbasis _).mpr h)
    obtain ⟨hcyc, hi'⟩ := bp_cycles_nohit (toMap s) i x.1 hx'
    rw [← hupd] at hi' hcyc
    rw [bp_cost_eq G mu s i, bp_cost_eq G mu (Function.update s i x) i, if_neg hi', if_pos hi] at hlt
    have hmpos : 0 < basinMass mu (toMap s) (cycleOf (toMap s) i) := by
      have : 0 < basinMass mu (toMap s) (cycleOf (toMap s) i) / ((cycleOf (toMap s) i).card : ℝ) := hlt
      exact (div_pos_iff_of_pos_right hcpos).mp this
    have hpsi : Psi G (Function.update s i x) = Psi G s
        - ((Fintype.card V : ℝ) - (cycleOf (toMap s) i).card) := by
      unfold Psi
      simp only [hupd]
      exact bp_psi_nohit (toMap s) i x.1 hi hx'
    have hlt2 : (cycleOf (toMap s) i).card < Fintype.card V := by
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset (Finset.subset_univ _)]
      refine ⟨x.1, Finset.mem_univ _, fun hxC => hx ?_⟩
      rw [bp_mem_basin]; exact ⟨0, hxC⟩
    have hlt3 : ((cycleOf (toMap s) i).card : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast hlt2
    refine ⟨hi, hmpos, Or.inr ⟨hx, hi', ?_⟩⟩
    rw [hpsi]; linarith

theorem bp_theorem_1 (G : BPGraph V) (mu : V → ℝ) (hmu : IsDistribution mu) :
    IsGenOrdPotential (cost G mu) (Psi G) := by
  intro s i x hlt
  obtain ⟨-, -, h⟩ := bp_dev_core G mu hmu s i x hlt
  rcases h with ⟨-, -, -, h⟩ | ⟨-, -, h⟩ <;> exact h

end bpL3

section bpL4
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem bp_cycleOf_upd_sub (f : V → V) (i x : V) (hxC : x ∈ cycleOf f i) :
    cycleOf (Function.update f i x) i ⊆ cycleOf f i := by
  have hclosed : ∀ c ∈ cycleOf f i, Function.update f i x c ∈ cycleOf f i := by
    intro c hc
    by_cases hci : c = i
    · subst hci; rw [Function.update_self]; exact hxC
    · rw [Function.update_of_ne hci]
      obtain ⟨s, hs⟩ := (bp_mem_cycleOf f i c).mp hc
      rw [bp_mem_cycleOf]
      exact ⟨s + 1, by rw [Function.iterate_succ_apply', hs]⟩
  have : ∀ t : ℕ, (Function.update f i x)^[t] i ∈ cycleOf f i := by
    intro t
    induction t with
    | zero => exact bp_self_mem_cycleOf f i
    | succ t ih => rw [Function.iterate_succ_apply']; exact hclosed _ ih
  intro c hc
  obtain ⟨t, rfl⟩ := (bp_mem_cycleOf _ i c).mp hc
  exact this t

end bpL4

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : BPGraph V) (mu : V → ℝ) (hmu : IsDistribution mu) :
    IsGenOrdPotential (cost G mu) (Psi G) := bp_theorem_1 G mu hmu
