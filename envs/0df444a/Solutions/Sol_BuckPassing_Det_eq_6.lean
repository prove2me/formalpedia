-- Prove2me | solution 1 for BuckPassing.Det.eq_6
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T18:00:54.183148+00:00
-- url     : https://prove2.me/submissions/4d09efe7-2fe3-4f7a-8a02-a5d9c90a6d55

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

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : BPGraph V) (mu : V → ℝ) (s : ∀ i, Strat G i) :
    (∀ j i : V,
      Tendsto (fun T : ℕ =>
        (((Finset.Icc 1 T).filter (fun t => (toMap s)^[t] j = i)).card : ℝ) / T)
        atTop
        (nhds (if i ∈ Function.periodicPts (toMap s) ∧
                   j ∈ basin (toMap s) (cycleOf (toMap s) i)
               then (1 : ℝ) / (cycleOf (toMap s) i).card else 0))) ∧
    (∀ i : V, cost G mu i s =
      if i ∈ Function.periodicPts (toMap s) then
        basinMass mu (toMap s) (cycleOf (toMap s) i) /
          (cycleOf (toMap s) i).card
      else 0) :=
  ⟨fun j i => bp_freq_tendsto (toMap s) j i, fun i => bp_cost_eq G mu s i⟩
