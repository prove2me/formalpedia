-- Prove2me | solution 1 for ForkJoinCtrl.Tracking.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T12:08:04.529008+00:00
-- url     : https://prove2.me/submissions/36f0d6ee-432b-452e-b4ff-292284c1ddac

import Mathlib
import Definitions.Def_ForkJoinCtrl_Tracking_Bounds


open MeasureTheory ProbabilityTheory Filter Topology

namespace FJL5

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Chernoff bound for a sum over a finite set of indices `≥ 1` of the i.i.d. sequence. -/
theorem tail_finset (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (x : ℝ)
    (hmeas : ∀ n, Measurable (X n))
    (hindep : iIndepFun (fun n : {n : ℕ // 1 ≤ n} => X n.1) P)
    (hident : ∀ n, 1 ≤ n → IdentDistrib (X n) (X 1) P P)
    (σ θ : ℝ) (hθ : 0 ≤ θ)
    (hint : Integrable (fun ω => Real.exp (θ * (σ * (X 1 ω - x)))) P)
    (s : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n) (hsne : s.Nonempty) (c : ℝ) :
    P.real {ω | c ≤ ∑ n ∈ s, σ * (X n ω - x)} ≤
      Real.exp (-θ * c) * (mgf (fun ω => σ * (X 1 ω - x)) P θ) ^ s.card := by
  classical
  let g : ℝ → ℝ := fun y => σ * (y - x)
  have hg : Measurable g := by fun_prop
  let Z : {n : ℕ // 1 ≤ n} → Ω → ℝ := fun n ω => σ * (X n.1 ω - x)
  have hZind : iIndepFun Z P := hindep.comp (fun _ => g) (fun _ => hg)
  have hZmeas : ∀ i, Measurable (Z i) := fun i => hg.comp (hmeas i.1)
  have hZid1 : ∀ i : {n : ℕ // 1 ≤ n}, IdentDistrib (Z i) (fun ω => σ * (X 1 ω - x)) P P :=
    fun i => (hident i.1 i.2).comp hg
  let s' : Finset {n : ℕ // 1 ≤ n} := s.subtype (fun n => 1 ≤ n)
  have hfil : s.filter (fun n => 1 ≤ n) = s := Finset.filter_true_of_mem hs
  have hsum : ∀ ω, ∑ n ∈ s, σ * (X n ω - x) = (∑ i ∈ s', Z i) ω := by
    intro ω
    rw [Finset.sum_apply]
    simp only [s', Z]
    rw [Finset.sum_subtype_eq_sum_filter (f := fun n => σ * (X n ω - x)), hfil]
  have hcard : s'.card = s.card := by
    simp only [s']; rw [Finset.card_subtype, hfil]
  have hset : {ω | c ≤ ∑ n ∈ s, σ * (X n ω - x)} = {ω | c ≤ (∑ i ∈ s', Z i) ω} := by
    ext ω; simp only [Set.mem_setOf_eq, hsum ω]
  have hintZ : ∀ i ∈ s', Integrable (fun ω => Real.exp (θ * Z i ω)) P := by
    intro i _
    have := (hZid1 i).comp (show Measurable (fun y : ℝ => Real.exp (θ * y)) by fun_prop)
    exact this.integrable_iff.2 hint
  rw [hset]
  refine (measure_ge_le_exp_mul_mgf c hθ (hZind.integrable_exp_mul_sum hZmeas hintZ)).trans ?_
  obtain ⟨n0, hn0⟩ := hsne
  let j : {n : ℕ // 1 ≤ n} := ⟨n0, hs n0 hn0⟩
  have hj : j ∈ s' := by simp only [s', j, Finset.mem_subtype]; exact hn0
  rw [mgf_sum_of_identDistrib hZmeas hZind
    (fun i _ k _ => (hZid1 i).trans (hZid1 k).symm) hj, hcard, mgf_congr_identDistrib (hZid1 j)]

/-- Uniform-in-shift version of Lemma EC.1.2. -/
theorem shifted_chernoff (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (x : ℝ)
    (hmeas : ∀ n, Measurable (X n))
    (hindep : iIndepFun (fun n : {n : ℕ // 1 ≤ n} => X n.1) P)
    (hident : ∀ n, 1 ≤ n → IdentDistrib (X n) (X 1) P P)
    (hint : Integrable (X 1) P) (hmean : ∫ ω, X 1 ω ∂P = x)
    (hmom : ∃ αbar : ℝ, 0 < αbar ∧ ∀ α ∈ Set.Ioo (-αbar) αbar,
      Integrable (fun ω => Real.exp (α * X 1 ω)) P)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∃ C : ℝ, 0 < C ∧ ∃ r0 : ℕ, ∀ r : ℕ, r0 ≤ r → ∀ m : ℕ,
      P {ω | ∃ y ∈ Finset.Icc 1 ⌊a * r⌋₊, b * r < |∑ n ∈ Finset.Icc 1 y, (X (m + n) ω - x)|} ≤
        ENNReal.ofReal (2 * Real.exp (-C * r)) := by
  obtain ⟨αbar, hα, hmomα⟩ := hmom
  set Y : Ω → ℝ := fun ω => X 1 ω - x with hY
  have hYint : ∀ t ∈ Set.Ioo (-αbar) αbar, Integrable (fun ω => Real.exp (t * Y ω)) P := by
    intro t ht
    have := (hmomα t ht).const_mul (Real.exp (-(t * x)))
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [hY]
    rw [← Real.exp_add]; ring_nf
  have h0 : (0 : ℝ) ∈ interior (integrableExpSet Y P) := by
    rw [mem_interior]
    exact ⟨Set.Ioo (-αbar) αbar, fun t ht => hYint t ht, isOpen_Ioo, by simp [hα]⟩
  have hderiv := hasDerivAt_mgf h0
  have hmean0 : P[fun ω => Y ω * Real.exp (0 * Y ω)] = 0 := by
    simp only [zero_mul, Real.exp_zero, mul_one, hY]
    rw [integral_sub hint (integrable_const x), hmean]
    simp
  rw [hmean0] at hderiv
  set δ : ℝ := b / (2 * a) with hδ
  have hδpos : 0 < δ := by positivity
  have hlo := (hasDerivAt_iff_isLittleO.1 hderiv).bound hδpos
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.1 hlo
  set θ : ℝ := min ρ αbar / 2 with hθdef
  have hθpos : 0 < θ := by positivity
  have hθρ : θ < ρ := by
    have := min_le_left ρ αbar; rw [hθdef]; linarith
  have hθα : θ < αbar := by
    have := min_le_right ρ αbar; rw [hθdef]; linarith
  have hmgf_bd : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → mgf Y P (σ * θ) ≤ 1 + δ * θ := by
    intro σ hσ
    have habs : |σ * θ| = θ := by
      rcases hσ with rfl | rfl <;> simp [abs_of_pos hθpos]
    have hd : dist (σ * θ) 0 < ρ := by rw [Real.dist_eq, sub_zero, habs]; exact hθρ
    have := hball hd
    simp only [mgf_zero, sub_zero, smul_zero, Real.norm_eq_abs, habs] at this
    have := (abs_le.1 this).2
    linarith
  have htail : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → ∀ s : Finset ℕ, (∀ n ∈ s, 1 ≤ n) → s.Nonempty →
      ∀ c : ℝ, P.real {ω | c ≤ ∑ n ∈ s, σ * (X n ω - x)} ≤
        Real.exp (-θ * c) * Real.exp (δ * θ * s.card) := by
    intro σ hσ s hs hsne c
    have habs : |σ * θ| = θ := by
      rcases hσ with rfl | rfl <;> simp [abs_of_pos hθpos]
    have hint' : Integrable (fun ω => Real.exp (θ * (σ * (X 1 ω - x)))) P := by
      have := hYint (σ * θ) (by
        rw [Set.mem_Ioo, ← abs_lt, habs]; exact hθα)
      refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
      simp only [hY]; ring_nf
    refine (tail_finset P X x hmeas hindep hident σ θ hθpos.le hint' s hs hsne c).trans ?_
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    have hm : mgf (fun ω => σ * (X 1 ω - x)) P θ = mgf Y P (σ * θ) := by
      have := mgf_const_mul (X := Y) (μ := P) (t := θ) σ
      simpa [hY] using this
    rw [hm]
    have hnn : 0 ≤ mgf Y P (σ * θ) := mgf_nonneg
    calc mgf Y P (σ * θ) ^ s.card ≤ (Real.exp (δ * θ)) ^ s.card := by
          apply pow_le_pow_left₀ hnn
          refine (hmgf_bd σ hσ).trans ?_
          have := Real.add_one_le_exp (δ * θ); linarith
      _ = Real.exp (δ * θ * s.card) := by rw [← Real.exp_nat_mul]; ring_nf
  set C : ℝ := θ * b / 4 with hC
  have hCpos : 0 < C := by positivity
  have hev : ∀ᶠ r : ℕ in atTop, a * r * Real.exp (-C * r) ≤ 1 := by
    have ht := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      (Tendsto.const_mul_atTop hCpos tendsto_natCast_atTop_atTop)
    have := ht.eventually (ge_mem_nhds (show (0 : ℝ) < C / a by positivity))
    filter_upwards [this] with r hr
    simp only [Function.comp, pow_one] at hr
    have : a * r * Real.exp (-C * r) = (a / C) * (C * r * Real.exp (-(C * r))) := by
      field_simp
    rw [this]
    calc (a / C) * (C * r * Real.exp (-(C * r))) ≤ (a / C) * (C / a) :=
          mul_le_mul_of_nonneg_left hr (by positivity)
      _ = 1 := by field_simp
  obtain ⟨r0, hr0⟩ := eventually_atTop.1 hev
  refine ⟨C, hCpos, r0, ?_⟩
  intro r hr m
  have hfin := hr0 r hr
  set S := {ω | ∃ y ∈ Finset.Icc 1 ⌊a * r⌋₊, b * r < |∑ n ∈ Finset.Icc 1 y, (X (m + n) ω - x)|}
  have hshift : ∀ (y : ℕ) (σ : ℝ) (ω : Ω), ∑ n ∈ Finset.Icc 1 y, σ * (X (m + n) ω - x) =
      ∑ n ∈ (Finset.Icc 1 y).map (addLeftEmbedding m), σ * (X n ω - x) := by
    intro y σ ω; rw [Finset.sum_map]; rfl
  have hsub : S ⊆ ⋃ y ∈ Finset.Icc 1 ⌊a * r⌋₊,
      ({ω | b * r ≤ ∑ n ∈ (Finset.Icc 1 y).map (addLeftEmbedding m), (1 : ℝ) * (X n ω - x)} ∪
       {ω | b * r ≤ ∑ n ∈ (Finset.Icc 1 y).map (addLeftEmbedding m), (-1 : ℝ) * (X n ω - x)}) := by
    intro ω hω
    obtain ⟨y, hy, hlt⟩ := hω
    simp only [Set.mem_iUnion, Set.mem_union, Set.mem_setOf_eq]
    refine ⟨y, hy, ?_⟩
    rcases lt_abs.1 hlt with h | h
    · left; rw [← hshift]; simp only [one_mul]; exact h.le
    · right
      rw [← hshift]
      have : ∑ n ∈ Finset.Icc 1 y, (-1 : ℝ) * (X (m + n) ω - x) =
          -∑ n ∈ Finset.Icc 1 y, (X (m + n) ω - x) := by
        rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro n _; ring
      rw [this]; exact h.le
  have hbound : P.real S ≤ 2 * Real.exp (-C * r) := by
    have hfl : (⌊a * r⌋₊ : ℝ) ≤ a * r := Nat.floor_le (by positivity)
    have hterm : ∀ y ∈ Finset.Icc 1 ⌊a * r⌋₊,
        P.real ({ω | b * r ≤ ∑ n ∈ (Finset.Icc 1 y).map (addLeftEmbedding m),
            (1 : ℝ) * (X n ω - x)} ∪
          {ω | b * r ≤ ∑ n ∈ (Finset.Icc 1 y).map (addLeftEmbedding m),
            (-1 : ℝ) * (X n ω - x)}) ≤
        2 * Real.exp (-(2 * C) * r) := by
      intro y hy
      have hy1 := (Finset.mem_Icc.1 hy).1
      have hy2 : (y : ℝ) ≤ a * r := le_trans (by exact_mod_cast (Finset.mem_Icc.1 hy).2) hfl
      have hs : ∀ n ∈ (Finset.Icc 1 y).map (addLeftEmbedding m), 1 ≤ n := by
        intro n hn
        simp only [Finset.mem_map, Finset.mem_Icc, addLeftEmbedding_apply] at hn
        obtain ⟨k, hk, rfl⟩ := hn; omega
      have hsne : ((Finset.Icc 1 y).map (addLeftEmbedding m)).Nonempty := by
        simp only [Finset.map_nonempty, Finset.nonempty_Icc]; exact hy1
      have hcard : (((Finset.Icc 1 y).map (addLeftEmbedding m)).card : ℝ) = y := by
        simp
      have hexp : Real.exp (-θ * (b * r)) * Real.exp (δ * θ * y) ≤ Real.exp (-(2 * C) * r) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.2
        have : δ * θ * y ≤ δ * θ * (a * r) :=
          mul_le_mul_of_nonneg_left hy2 (by positivity)
        have e : δ * θ * (a * r) = θ * b * r / 2 := by rw [hδ]; field_simp
        rw [hC]; nlinarith
      refine (measureReal_union_le _ _).trans ?_
      have h1 := htail 1 (Or.inl rfl) _ hs hsne (b * r)
      have h2 := htail (-1) (Or.inr rfl) _ hs hsne (b * r)
      rw [hcard] at h1 h2
      linarith
    calc P.real S ≤ P.real (⋃ y ∈ Finset.Icc 1 ⌊a * r⌋₊,
          ({ω | b * r ≤ ∑ n ∈ (Finset.Icc 1 y).map (addLeftEmbedding m), (1 : ℝ) * (X n ω - x)} ∪
           {ω | b * r ≤ ∑ n ∈ (Finset.Icc 1 y).map (addLeftEmbedding m),
              (-1 : ℝ) * (X n ω - x)})) :=
          measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ ∑ y ∈ Finset.Icc 1 ⌊a * r⌋₊,
          P.real ({ω | b * r ≤ ∑ n ∈ (Finset.Icc 1 y).map (addLeftEmbedding m),
              (1 : ℝ) * (X n ω - x)} ∪
           {ω | b * r ≤ ∑ n ∈ (Finset.Icc 1 y).map (addLeftEmbedding m),
              (-1 : ℝ) * (X n ω - x)}) :=
          measureReal_biUnion_finset_le _ _
      _ ≤ ∑ y ∈ Finset.Icc 1 ⌊a * r⌋₊, 2 * Real.exp (-(2 * C) * r) := Finset.sum_le_sum hterm
      _ = (⌊a * r⌋₊ : ℝ) * (2 * Real.exp (-(2 * C) * r)) := by simp
      _ ≤ (a * r) * (2 * Real.exp (-(2 * C) * r)) :=
          mul_le_mul_of_nonneg_right hfl (by positivity)
      _ = 2 * Real.exp (-C * r) * (a * r * Real.exp (-C * r)) := by
          rw [show -(2 * C) * r = -C * r + -C * r by ring, Real.exp_add]; ring
      _ ≤ 2 * Real.exp (-C * r) * 1 := mul_le_mul_of_nonneg_left hfin (by positivity)
      _ = 2 * Real.exp (-C * r) := mul_one _
  rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top P S) (by positivity)]
  exact hbound

end FJL5


open ForkJoinCtrl.Tracking

namespace FJL5

theorem partialSum_zero (x : ℕ → ℝ) : partialSum x 0 = 0 := by
  simp [partialSum]

theorem partialSum_succ (x : ℕ → ℝ) (n : ℕ) : partialSum x (n + 1) = partialSum x n + x (n + 1) := by
  simp only [partialSum]
  rw [Finset.sum_Icc_succ_top (by omega)]

theorem partialSum_add (x : ℕ → ℝ) (m y : ℕ) :
    partialSum x (m + y) = partialSum x m + ∑ n ∈ Finset.Icc 1 y, x (m + n) := by
  induction y with
  | zero => simp
  | succ y ih =>
    rw [← add_assoc, partialSum_succ, ih, Finset.sum_Icc_succ_top (by omega)]
    ring

theorem partialSum_mono (x : ℕ → ℝ) (hpos : ∀ n, 1 ≤ n → 0 < x n) : Monotone (partialSum x) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [partialSum_succ]
  linarith [hpos (n + 1) (by omega)]

theorem count_ge (x : ℕ → ℝ) (hpos : ∀ n, 1 ≤ n → 0 < x n)
    (hunb : ∀ M : ℝ, ∃ n, M < partialSum x n) (t : ℝ) (ht : 0 ≤ t) (N : ℕ) :
    N ≤ count x t ↔ partialSum x N ≤ t := by
  obtain ⟨n0, hn0⟩ := hunb t
  have hbdd : BddAbove {n : ℕ | partialSum x n ≤ t} := by
    refine ⟨n0, fun n hn => ?_⟩
    by_contra h
    push Not at h
    have := partialSum_mono x hpos h.le
    simp only [Set.mem_setOf_eq] at hn
    linarith
  have hne : ({n : ℕ | partialSum x n ≤ t}).Nonempty := ⟨0, by simp [partialSum_zero, ht]⟩
  have hmem : partialSum x (count x t) ≤ t := Nat.sSup_mem hne hbdd
  constructor
  · intro h
    exact le_trans (partialSum_mono x hpos h) hmem
  · intro h
    exact le_csSup hbdd h

theorem count_mono (x : ℕ → ℝ) (hpos : ∀ n, 1 ≤ n → 0 < x n)
    (hunb : ∀ M : ℝ, ∃ n, M < partialSum x n) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    count x s ≤ count x t := by
  rw [count_ge x hpos hunb t (le_trans hs hst)]
  exact le_trans ((count_ge x hpos hunb s hs _).1 le_rfl) hst

/-- The deterministic core of the proof of Lemma 5 (EC.2): a large deviation of the counting
process over a window starting at an arbitrary time `s0` forces a large deviation of a partial sum
of the sequence, started either at index `m` or `m + 1`, where `m = count x s0`. -/
theorem window_dev (x : ℕ → ℝ) (hpos : ∀ n, 1 ≤ n → 0 < x n)
    (hunb : ∀ M : ℝ, ∃ n, M < partialSum x n) (ρ : ℝ) (hρ : 0 < ρ) (s0 t B : ℝ)
    (hs0 : 0 ≤ s0) (ht : 0 ≤ t) (hB : 1 < B)
    (hdev : B < |(count x (s0 + t) : ℝ) - (count x s0 : ℝ) - ρ * t|) :
    (∃ y : ℕ, 1 ≤ y ∧ (y : ℝ) ≤ B + ρ * t ∧
      (B - 1) / ρ < |∑ n ∈ Finset.Icc 1 y, (x (count x s0 + 1 + n) - 1 / ρ)|) ∨
    (∃ y : ℕ, 1 ≤ y ∧ (y : ℝ) ≤ ρ * t - B + 1 ∧
      (B - 1) / ρ < |∑ n ∈ Finset.Icc 1 y, (x (count x s0 + n) - 1 / ρ)|) := by
  set m := count x s0 with hm
  set c := count x (s0 + t) with hc
  have hst : 0 ≤ s0 + t := by linarith
  have hVm : partialSum x m ≤ s0 := (count_ge x hpos hunb s0 hs0 m).1 le_rfl
  have hVm1 : s0 < partialSum x (m + 1) := by
    by_contra h; push Not at h
    have := (count_ge x hpos hunb s0 hs0 (m + 1)).2 h
    omega
  have hmc : m ≤ c := count_mono x hpos hunb hs0 (by linarith)
  rcases lt_abs.1 hdev with h | h
  · -- upper deviation
    left
    set y := ⌊B + ρ * t⌋₊ with hy
    have hBt : 0 ≤ B + ρ * t := by nlinarith
    have hy1 : 1 ≤ y := by
      rw [hy]; apply Nat.le_floor; push_cast; nlinarith
    have hyle : (y : ℝ) ≤ B + ρ * t := Nat.floor_le hBt
    have hylt : B + ρ * t < y + 1 := Nat.lt_floor_add_one _
    have hcm : m + y + 1 ≤ c := by
      have : ((m + y + 1 : ℕ) : ℝ) ≤ (c : ℝ) := by
        push_cast
        have : (c : ℝ) - m > B + ρ * t := by linarith
        have h2 : (c : ℝ) - m > y := lt_of_le_of_lt hyle this
        have h3 : (c - m : ℤ) > y := by exact_mod_cast h2
        have h4 : (c - m : ℤ) ≥ y + 1 := h3
        have h5 : ((c : ℤ) : ℝ) - (m : ℤ) ≥ (y : ℤ) + 1 := by exact_mod_cast h4
        push_cast at h5; linarith
      exact_mod_cast this
    have hV : partialSum x (m + y + 1) ≤ s0 + t := (count_ge x hpos hunb _ hst _).1 hcm
    have hsplit : partialSum x (m + 1 + y) = partialSum x (m + 1) +
        ∑ n ∈ Finset.Icc 1 y, x (m + 1 + n) := partialSum_add x (m + 1) y
    rw [show m + 1 + y = m + y + 1 by ring] at hsplit
    have hsum : ∑ n ∈ Finset.Icc 1 y, x (m + 1 + n) < t := by linarith
    refine ⟨y, hy1, hyle, ?_⟩
    have hs : ∑ n ∈ Finset.Icc 1 y, (x (m + 1 + n) - 1 / ρ) =
        ∑ n ∈ Finset.Icc 1 y, x (m + 1 + n) - y / ρ := by
      rw [Finset.sum_sub_distrib]; simp; ring
    rw [hs]
    have : (y : ℝ) / ρ > (B + ρ * t - 1) / ρ := by
      apply div_lt_div_of_pos_right _ hρ; linarith
    have e : (B + ρ * t - 1) / ρ = (B - 1) / ρ + t := by field_simp; ring
    rw [lt_abs]; right; linarith
  · -- lower deviation
    right
    have hpos' : 0 < ρ * t - B := by
      have : (0 : ℝ) ≤ (c : ℝ) - m := by
        have : (m : ℝ) ≤ c := by exact_mod_cast hmc
        linarith
      linarith
    set y := ⌈ρ * t - B⌉₊ with hy
    have hy1 : 1 ≤ y := by rw [hy]; exact Nat.one_le_iff_ne_zero.2 (by
      rw [Ne, Nat.ceil_eq_zero, not_le]; exact hpos')
    have hyge : ρ * t - B ≤ y := Nat.le_ceil _
    have hylt : (y : ℝ) < ρ * t - B + 1 := Nat.ceil_lt_add_one hpos'.le
    have hcm : ¬ (m + y ≤ c) := by
      intro hle
      have : ((m + y : ℕ) : ℝ) ≤ c := by exact_mod_cast hle
      push_cast at this
      linarith
    have hV : s0 + t < partialSum x (m + y) := by
      by_contra hcon; push Not at hcon
      exact hcm ((count_ge x hpos hunb _ hst _).2 hcon)
    have hsplit := partialSum_add x m y
    have hsum : t < ∑ n ∈ Finset.Icc 1 y, x (m + n) := by linarith
    refine ⟨y, hy1, hylt.le, ?_⟩
    have hs : ∑ n ∈ Finset.Icc 1 y, (x (m + n) - 1 / ρ) =
        ∑ n ∈ Finset.Icc 1 y, x (m + n) - y / ρ := by
      rw [Finset.sum_sub_distrib]; simp; ring
    rw [hs]
    have : (y : ℝ) / ρ < (ρ * t - B + 1) / ρ := by
      apply div_lt_div_of_pos_right hylt hρ
    have e : (ρ * t - B + 1) / ρ = t - (B - 1) / ρ := by field_simp; ring
    rw [lt_abs]; left; linarith

end FJL5


open MeasureTheory ProbabilityTheory Filter Topology
open ForkJoinCtrl.Tracking

namespace FJL5

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The partial sums of an i.i.d. sequence with positive mean are a.s. unbounded. -/
theorem ae_unbounded (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (x : ℝ)
    (hmeas : ∀ n, Measurable (X n))
    (hindep : iIndepFun (fun n : {n : ℕ // 1 ≤ n} => X n.1) P)
    (hident : ∀ n, 1 ≤ n → IdentDistrib (X n) (X 1) P P)
    (hint : Integrable (X 1) P) (hmean : ∫ ω, X 1 ω ∂P = x)
    (hmom : ∃ αbar : ℝ, 0 < αbar ∧ ∀ α ∈ Set.Ioo (-αbar) αbar,
      Integrable (fun ω => Real.exp (α * X 1 ω)) P)
    (hx : 0 < x) :
    ∀ᵐ ω ∂P, ∀ M : ℝ, ∃ n, M < partialSum (fun n => X n ω) n := by
  obtain ⟨C, hC, r0, hr0⟩ := shifted_chernoff P X x hmeas hindep hident hint hmean hmom 1 (x / 4)
    one_pos (by positivity)
  rw [ae_iff]
  have hsub : {ω | ¬ ∀ M : ℝ, ∃ n, M < partialSum (fun n => X n ω) n} ⊆
      ⋃ M : ℕ, {ω | ∀ n, partialSum (fun n => X n ω) n ≤ M} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, not_forall, not_exists, not_lt] at hω
    obtain ⟨M, hM⟩ := hω
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨⌈M⌉₊, fun n => (hM n).trans (Nat.le_ceil M)⟩
  refine measure_mono_null hsub (measure_iUnion_null (fun M => ?_))
  set S := {ω | ∀ n, partialSum (fun n => X n ω) n ≤ (M : ℝ)}
  have hbd : ∀ N : ℕ, max r0 (⌈(2 * (M : ℝ)) / x⌉₊ + 1) ≤ N →
      P S ≤ ENNReal.ofReal (2 * Real.exp (-C * N)) := by
    intro N hN
    have hN0 : r0 ≤ N := le_trans (le_max_left _ _) hN
    have hN1 : ⌈(2 * (M : ℝ)) / x⌉₊ + 1 ≤ N := le_trans (le_max_right _ _) hN
    refine le_trans (measure_mono ?_) (hr0 N hN0 0)
    intro ω hω
    have hV := hω N
    have hNpos : 1 ≤ N := by omega
    refine ⟨N, ?_, ?_⟩
    · simp only [Finset.mem_Icc, one_mul, Nat.floor_natCast]; exact ⟨hNpos, le_rfl⟩
    · simp only [zero_add]
      have hs : ∑ n ∈ Finset.Icc 1 N, (X n ω - x) = partialSum (fun n => X n ω) N - N * x := by
        simp [partialSum, Finset.sum_sub_distrib]
      rw [hs]
      have hNM : 2 * (M : ℝ) / x < N := by
        have := Nat.le_ceil (2 * (M : ℝ) / x)
        have : ((⌈(2 * (M : ℝ)) / x⌉₊ + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hN1
        push_cast at this; linarith
      have hNM' : 2 * (M : ℝ) < N * x := by rwa [div_lt_iff₀ hx] at hNM
      rw [lt_abs]; right
      have : (0 : ℝ) ≤ M := Nat.cast_nonneg M
      nlinarith
  have htend : Tendsto (fun N : ℕ => ENNReal.ofReal (2 * Real.exp (-C * N))) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    apply ENNReal.tendsto_ofReal
    have : Tendsto (fun N : ℕ => Real.exp (-(C * N))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (Tendsto.const_mul_atTop hC tendsto_natCast_atTop_atTop)
    have h2 := this.const_mul 2
    simp only [mul_zero] at h2
    refine h2.congr (fun N => ?_)
    simp [neg_mul]
  exact le_antisymm (ge_of_tendsto htend (eventually_atTop.2 ⟨_, hbd⟩)) (zero_le)

end FJL5


open MeasureTheory ProbabilityTheory Filter Topology
open ForkJoinCtrl.Tracking

namespace FJL5

theorem partialSum_div (x : ℕ → ℝ) (κ : ℝ) (n : ℕ) :
    partialSum (fun l => x l / κ) n = partialSum x n / κ := by
  simp [partialSum, Finset.sum_div]

/-- the window lemma in the form used for all three families -/
theorem window (seq : ℕ → ℝ) (κ ρ : ℝ) (hκ : 0 < κ) (hρ : 0 < ρ)
    (hpos : ∀ n, 1 ≤ n → 0 < seq n) (hunb : ∀ M : ℝ, ∃ n, M < partialSum seq n)
    (s0 : ℝ) (hs0 : 0 ≤ s0) (r : ℕ) (a b Λ : ℝ) (ha : 0 < a) (hb : 0 < b) (hbr : 2 ≤ b * r)
    (hΛ : ρ ≤ Λ)
    (hdev : ∃ t ∈ Set.Icc 0 (a * r), b * r < |(count (fun l => seq l / κ) (s0 + t) : ℝ) -
        (count (fun l => seq l / κ) s0 : ℝ) - ρ * t|) :
    ∃ s ∈ ({count (fun l => seq l / κ) s0, count (fun l => seq l / κ) s0 + 1} : Finset ℕ),
      ∃ y ∈ Finset.Icc 1 ⌊(b + Λ * a) * r⌋₊,
        κ / ρ * (b / 2) * r < |∑ n ∈ Finset.Icc 1 y, (seq (s + n) - κ / ρ)| := by
  obtain ⟨t, ht, hdev⟩ := hdev
  have hpos' : ∀ n, 1 ≤ n → 0 < seq n / κ := fun n hn => div_pos (hpos n hn) hκ
  have hunb' : ∀ M : ℝ, ∃ n, M < partialSum (fun l => seq l / κ) n := by
    intro M
    obtain ⟨n, hn⟩ := hunb (M * κ)
    refine ⟨n, ?_⟩
    rw [partialSum_div, lt_div_iff₀ hκ]; exact hn
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have key : ∀ (s y : ℕ), (b * r - 1) / ρ <
      |∑ n ∈ Finset.Icc 1 y, (seq (s + n) / κ - 1 / ρ)| →
      κ / ρ * (b / 2) * r < |∑ n ∈ Finset.Icc 1 y, (seq (s + n) - κ / ρ)| := by
    intro s y h
    have e : ∑ n ∈ Finset.Icc 1 y, (seq (s + n) / κ - 1 / ρ) =
        (1 / κ) * ∑ n ∈ Finset.Icc 1 y, (seq (s + n) - κ / ρ) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro n _; field_simp
    rw [e, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / κ)] at h
    have h2 : κ * ((b * r - 1) / ρ) < |∑ n ∈ Finset.Icc 1 y, (seq (s + n) - κ / ρ)| := by
      have := mul_lt_mul_of_pos_left h hκ
      rwa [← mul_assoc, mul_one_div_cancel hκ.ne', one_mul] at this
    have h3 : κ / ρ * (b / 2) * r ≤ κ * ((b * r - 1) / ρ) := by
      rw [show κ / ρ * (b / 2) * r = κ * ((b * r / 2) / ρ) by ring]
      apply mul_le_mul_of_nonneg_left _ hκ.le
      apply div_le_div_of_nonneg_right _ hρ.le
      linarith
    linarith
  have hyb : ∀ y : ℕ, (y : ℝ) ≤ b * r + ρ * t ∨ (y : ℝ) ≤ ρ * t - b * r + 1 →
      y ≤ ⌊(b + Λ * a) * r⌋₊ := by
    intro y hy
    apply Nat.le_floor
    have hρt : ρ * t ≤ Λ * (a * r) := mul_le_mul hΛ ht.2 ht.1 (by linarith)
    rcases hy with hy | hy <;> nlinarith
  rcases window_dev (fun l => seq l / κ) hpos' hunb' ρ hρ s0 t (b * r) hs0 ht.1 (by linarith)
    hdev with ⟨y, hy1, hyle, hyd⟩ | ⟨y, hy1, hyle, hyd⟩
  · refine ⟨count (fun l => seq l / κ) s0 + 1, by simp, y, Finset.mem_Icc.2 ⟨hy1, hyb y (Or.inl hyle)⟩, key _ y ?_⟩
    simpa using hyd
  · refine ⟨count (fun l => seq l / κ) s0, by simp, y, Finset.mem_Icc.2 ⟨hy1, hyb y (Or.inr hyle)⟩, key _ y ?_⟩
    simpa using hyd

variable {Ω : Type*} [MeasurableSpace Ω]

/-- union bound over the possible starting indices -/
theorem assemble (P : Measure Ω) [IsFiniteMeasure P] (Ev Bad : Set Ω) (hBad : P Bad = 0)
    (K0 : ℕ) (E : ℕ → Set Ω) (u : ℝ) (hu : 0 ≤ u) (hE : ∀ s, P (E s) ≤ ENNReal.ofReal u)
    (hsub : Ev ⊆ Bad ∪ ⋃ m ∈ Finset.range K0, (E (m + 1) ∪ E m)) :
    P Ev ≤ ENNReal.ofReal (2 * K0 * u) := by
  rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)]
  have hE' : ∀ s, P.real (E s) ≤ u := fun s => ENNReal.toReal_le_of_le_ofReal hu (hE s)
  have hB' : P.real Bad = 0 := by simp [measureReal_def, hBad]
  calc P.real Ev ≤ P.real (Bad ∪ ⋃ m ∈ Finset.range K0, (E (m + 1) ∪ E m)) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ P.real Bad + P.real (⋃ m ∈ Finset.range K0, (E (m + 1) ∪ E m)) :=
        measureReal_union_le _ _
    _ ≤ 0 + ∑ m ∈ Finset.range K0, P.real (E (m + 1) ∪ E m) := by
        rw [hB']; gcongr; exact measureReal_biUnion_finset_le _ _
    _ ≤ 0 + ∑ m ∈ Finset.range K0, (u + u) := by
        gcongr with m hm
        exact (measureReal_union_le _ _).trans (add_le_add (hE' _) (hE' _))
    _ = 2 * K0 * u := by simp; ring

section Model

variable {N : Network} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem indep_arr (M : Model N Ω P) (j : Fin N.J) :
    iIndepFun (fun n : {n : ℕ // 1 ≤ n} => M.ubar j n.1) P := by
  have := M.indep.precomp (g := fun n : {n : ℕ // 1 ≤ n} =>
    (⟨PrimIdx.arr j n.1, n.2⟩ : {x : PrimIdx N // x.Valid}))
    (by intro n n' h
        have h1 := congrArg Subtype.val h
        simp only [PrimIdx.arr.injEq, true_and] at h1
        exact Subtype.ext h1)
  exact this

theorem indep_ded (M : Model N Ω P) (k : Fin N.K) :
    iIndepFun (fun n : {n : ℕ // 1 ≤ n} => M.v k n.1) P := by
  have := M.indep.precomp (g := fun n : {n : ℕ // 1 ≤ n} =>
    (⟨PrimIdx.ded k n.1, n.2⟩ : {x : PrimIdx N // x.Valid}))
    (by intro n n' h
        have h1 := congrArg Subtype.val h
        simp only [PrimIdx.ded.injEq, true_and] at h1
        exact Subtype.ext h1)
  exact this

theorem indep_sh (M : Model N Ω P) (i : Fin N.I) (j : Fin N.J) (hij : N.P i j = true) :
    iIndepFun (fun n : {n : ℕ // 1 ≤ n} => M.vs i j n.1) P := by
  have := M.indep.precomp (g := fun n : {n : ℕ // 1 ≤ n} =>
    (⟨PrimIdx.sh i j n.1, ⟨hij, n.2⟩⟩ : {x : PrimIdx N // x.Valid}))
    (by intro n n' h
        have h1 := congrArg Subtype.val h
        simp only [PrimIdx.sh.injEq, true_and] at h1
        exact Subtype.ext h1)
  exact this

theorem pos_ae {X : ℕ → Ω → ℝ} (h : ∀ n, 1 ≤ n → ∀ᵐ ω ∂P, 0 < X n ω) :
    ∀ᵐ ω ∂P, ∀ n, 1 ≤ n → 0 < X n ω := by
  rw [ae_all_iff]
  intro n
  by_cases hn : 1 ≤ n
  · exact (h n hn).mono (fun ω hω _ => hω)
  · exact Eventually.of_forall (fun ω h' => absurd h' hn)

end Model

section Parts

variable {N : Network} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem m_lt_K0 {m : ℕ} {r : ℕ} {T : ℝ} (h : (m : ℝ) ≤ (⌊N.C8 * (r : ℝ) ^ 2 * T⌋ : ℝ) - 1) :
    m ∈ Finset.range ⌊N.C8 * (r : ℝ) ^ 2 * T⌋₊ := by
  rw [Finset.mem_range]
  have h1 : ((m + 1 : ℕ) : ℝ) ≤ N.C8 * (r : ℝ) ^ 2 * T := by
    push_cast
    have := Int.floor_le (N.C8 * (r : ℝ) ^ 2 * T)
    linarith
  have := Nat.le_floor h1
  omega

theorem part_a (M : Model N Ω P) (run : ∀ r : ℕ, PolicyRun M r) (T : ℝ) (hT : 0 < T) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (j : Fin N.J) (Λ C : ℝ) (r : ℕ) (hbr : 2 ≤ b * r)
    (hΛ : M.lamr r j ≤ Λ)
    (hch : ∀ m, P {ω | ∃ y ∈ Finset.Icc 1 ⌊(b + Λ * a) * r⌋₊,
      b / 2 * r < |∑ n ∈ Finset.Icc 1 y, (M.ubar j (m + n) ω - 1)|} ≤
        ENNReal.ofReal (2 * Real.exp (-C * r)))
    (hpos : ∀ᵐ ω ∂P, ∀ n, 1 ≤ n → 0 < M.ubar j n ω)
    (hunb : ∀ᵐ ω ∂P, ∀ Mx : ℝ, ∃ n, Mx < partialSum (fun n => M.ubar j n ω) n)
    (l : Fin N.I) (n : ℕ) :
    P {ω | (∃ t ∈ Set.Icc 0 (a * r),
          b * r < |(M.A r j ω (((run r).tau l n ω).toReal + t) : ℝ)
            - (M.A r j ω ((run r).tau l n ω).toReal : ℝ) - M.lamr r j * t|) ∧
        (run r).tau l n ω ≤ ENNReal.ofReal ((r : ℝ) ^ 2 * T) ∧ ω ∈ M.Bevent T r}
      ≤ ENNReal.ofReal (2 * ⌊N.C8 * (r : ℝ) ^ 2 * T⌋₊ * (2 * Real.exp (-C * r))) := by
  haveI := M.isProb
  set Bad := {ω | ¬ ∀ n, 1 ≤ n → 0 < M.ubar j n ω} ∪
    {ω | ¬ ∀ Mx : ℝ, ∃ n, Mx < partialSum (fun n => M.ubar j n ω) n}
  have hBad : P Bad = 0 := measure_union_null (ae_iff.1 hpos) (ae_iff.1 hunb)
  have hlam := M.lamr_pos r j
  apply assemble P _ Bad hBad _ _ _ (by positivity) hch
  rintro ω ⟨hdev, hτ, hB⟩
  by_cases hω : ω ∈ Bad
  · exact Or.inl hω
  right
  simp only [Bad, Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hω
  obtain ⟨hp, hu⟩ := hω
  set τ := ((run r).tau l n ω).toReal
  have hτ0 : 0 ≤ τ := ENNReal.toReal_nonneg
  have hτT : τ ≤ (r : ℝ) ^ 2 * T := ENNReal.toReal_le_of_le_ofReal (by positivity) hτ
  obtain ⟨s', hs', y, hy, hd⟩ := window (fun l => M.ubar j l ω) (M.lamr r j) (M.lamr r j) hlam hlam hp hu
    τ hτ0 r a b Λ ha hb hbr hΛ hdev
  rw [div_self hlam.ne', one_mul] at hd
  have hmK : count (fun l => M.ubar j l ω / M.lamr r j) τ ∈
      Finset.range ⌊N.C8 * (r : ℝ) ^ 2 * T⌋₊ := by
    apply m_lt_K0
    have h1 := hB.1 j
    have hpos' : ∀ n, 1 ≤ n → 0 < M.ubar j n ω / M.lamr r j := fun n hn => div_pos (hp n hn) hlam
    have hunb' : ∀ Mx : ℝ, ∃ n, Mx < partialSum (fun l => M.ubar j l ω / M.lamr r j) n := by
      intro Mx
      obtain ⟨n, hn⟩ := hu (Mx * M.lamr r j)
      exact ⟨n, by rw [partialSum_div, lt_div_iff₀ hlam]; exact hn⟩
    have h2 := count_mono _ hpos' hunb' hτ0 hτT
    have h3 : (count (fun l => M.ubar j l ω / M.lamr r j) τ : ℝ) ≤
        (M.A r j ω ((r : ℝ) ^ 2 * T) : ℝ) := by exact_mod_cast h2
    linarith
  simp only [Set.mem_iUnion, Set.mem_union, Set.mem_ofPred_eq]
  refine ⟨_, hmK, ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs'
  rcases hs' with rfl | rfl
  · right; exact ⟨y, hy, hd⟩
  · left; exact ⟨y, hy, hd⟩

theorem part_b (M : Model N Ω P) (run : ∀ r : ℕ, PolicyRun M r) (T : ℝ) (hT : 0 < T) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (i : Fin N.I) (j : Fin N.J) (hij : N.P i j = true) (C : ℝ) (r : ℕ)
    (hbr : 2 ≤ b * r)
    (hch : ∀ m, P {ω | ∃ y ∈ Finset.Icc 1 ⌊(b + N.mu i j * a) * r⌋₊,
      1 / N.mu i j * (b / 2) * r < |∑ n ∈ Finset.Icc 1 y, (M.vs i j (m + n) ω - 1 / N.mu i j)|} ≤
        ENNReal.ofReal (2 * Real.exp (-C * r)))
    (hpos : ∀ᵐ ω ∂P, ∀ n, 1 ≤ n → 0 < M.vs i j n ω)
    (hunb : ∀ᵐ ω ∂P, ∀ Mx : ℝ, ∃ n, Mx < partialSum (fun n => M.vs i j n ω) n)
    (l : Fin N.I) (n : ℕ) :
    P {ω | (∃ t ∈ Set.Icc 0 (a * r),
          b * r < |(M.Ss i j ω ((run r).Tij i j ω ((run r).tau l n ω).toReal + t) : ℝ)
            - (M.Ss i j ω ((run r).Tij i j ω ((run r).tau l n ω).toReal) : ℝ)
            - N.mu i j * t|) ∧
        (run r).tau l n ω ≤ ENNReal.ofReal ((r : ℝ) ^ 2 * T) ∧ ω ∈ M.Bevent T r}
      ≤ ENNReal.ofReal (2 * ⌊N.C8 * (r : ℝ) ^ 2 * T⌋₊ * (2 * Real.exp (-C * r))) := by
  haveI := M.isProb
  set Bad := ({ω | ¬ ∀ n, 1 ≤ n → 0 < M.vs i j n ω} ∪
    {ω | ¬ ∀ Mx : ℝ, ∃ n, Mx < partialSum (fun n => M.vs i j n ω) n}) ∪
    {ω | ¬ (run r).toPaths.IsAdmissibleAt M r ω}
  have hBad : P Bad = 0 := measure_union_null (measure_union_null (ae_iff.1 hpos) (ae_iff.1 hunb))
    (ae_iff.1 (run r).adm)
  have hmu := N.mu_pos i j hij
  apply assemble P _ Bad hBad _ _ _ (by positivity) hch
  rintro ω ⟨hdev, hτ, hB⟩
  by_cases hω : ω ∈ Bad
  · exact Or.inl hω
  right
  simp only [Bad, Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hω
  obtain ⟨⟨hp, hu⟩, hadm⟩ := hω
  set τ := ((run r).tau l n ω).toReal
  have hτ0 : 0 ≤ τ := ENNReal.toReal_nonneg
  have hτT : τ ≤ (r : ℝ) ^ 2 * T := ENNReal.toReal_le_of_le_ofReal (by positivity) hτ
  -- busy time bounds
  have hT12 := hadm.2.2.2.2.2.2.2.2.2.2.2.1
  have hidle := (hadm.2.2.2.2.2.2.2.2.2.1 i)
  have hT0 : ∀ j', N.P i j' = true → 0 ≤ (run r).Tij i j' ω τ := by
    intro j' hj'
    have h := hT12 i j' hj'
    have := h.2.1 (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hτ0) hτ0
    rw [h.2.2] at this; exact this
  have hsumle : ∑ j' ∈ N.Ji i, (run r).Tij i j' ω τ ≤ τ := by
    have h1 := hidle.1 (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hτ0) hτ0
    rw [hidle.2.1] at h1
    simp only [Paths.Ii] at h1
    linarith
  have hTle : (run r).Tij i j ω τ ≤ τ := by
    have hj : j ∈ N.Ji i := by simp [Network.Ji, hij]
    have := Finset.single_le_sum (f := fun j' => (run r).Tij i j' ω τ)
      (fun j' hj' => hT0 j' (by simpa [Network.Ji] using hj')) hj
    linarith
  set s0 := (run r).Tij i j ω τ
  have hs0 : 0 ≤ s0 := hT0 j hij
  have hdev' : ∃ t ∈ Set.Icc 0 (a * r), b * r <
      |(count (fun l => M.vs i j l ω / 1) (s0 + t) : ℝ) -
        (count (fun l => M.vs i j l ω / 1) s0 : ℝ) - N.mu i j * t| := by
    simpa only [div_one, Model.Ss, Model.S] using hdev
  obtain ⟨s', hs', y, hy, hd⟩ := window (fun l => M.vs i j l ω) 1 (N.mu i j) one_pos hmu hp hu
    s0 hs0 r a b (N.mu i j) ha hb hbr le_rfl hdev'
  have hmK : count (fun l => M.vs i j l ω / 1) s0 ∈ Finset.range ⌊N.C8 * (r : ℝ) ^ 2 * T⌋₊ := by
    apply m_lt_K0
    have h1 := hB.2.1 i j hij
    have h2 := count_mono _ hp hu hs0 (hTle.trans hτT)
    have h3 : (count (fun l => M.vs i j l ω) s0 : ℝ) ≤
        (M.Ss i j ω ((r : ℝ) ^ 2 * T) : ℝ) := by exact_mod_cast h2
    simp only [div_one]
    linarith
  simp only [Set.mem_iUnion, Set.mem_union, Set.mem_ofPred_eq]
  refine ⟨_, hmK, ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs'
  rcases hs' with rfl | rfl
  · right; exact ⟨y, hy, hd⟩
  · left; exact ⟨y, hy, hd⟩

theorem part_c (M : Model N Ω P) (run : ∀ r : ℕ, PolicyRun M r) (T : ℝ) (hT : 0 < T) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (k : Fin N.K) (C : ℝ) (r : ℕ)
    (hbr : 2 ≤ b * r)
    (hch : ∀ m, P {ω | ∃ y ∈ Finset.Icc 1 ⌊(b + N.muK k * a) * r⌋₊,
      1 / N.muK k * (b / 2) * r < |∑ n ∈ Finset.Icc 1 y, (M.v k (m + n) ω - 1 / N.muK k)|} ≤
        ENNReal.ofReal (2 * Real.exp (-C * r)))
    (hpos : ∀ᵐ ω ∂P, ∀ n, 1 ≤ n → 0 < M.v k n ω)
    (hunb : ∀ᵐ ω ∂P, ∀ Mx : ℝ, ∃ n, Mx < partialSum (fun n => M.v k n ω) n)
    (l : Fin N.I) (n : ℕ) :
    P {ω | (∃ t ∈ Set.Icc 0 (a * r),
          b * r < |(M.S k ω ((run r).Tk k ω ((run r).tau l n ω).toReal + t) : ℝ)
            - (M.S k ω ((run r).Tk k ω ((run r).tau l n ω).toReal) : ℝ)
            - N.muK k * t|) ∧
        (run r).tau l n ω ≤ ENNReal.ofReal ((r : ℝ) ^ 2 * T) ∧ ω ∈ M.Bevent T r}
      ≤ ENNReal.ofReal (2 * ⌊N.C8 * (r : ℝ) ^ 2 * T⌋₊ * (2 * Real.exp (-C * r))) := by
  haveI := M.isProb
  set Bad := ({ω | ¬ ∀ n, 1 ≤ n → 0 < M.v k n ω} ∪
    {ω | ¬ ∀ Mx : ℝ, ∃ n, Mx < partialSum (fun n => M.v k n ω) n}) ∪
    {ω | ¬ (run r).toPaths.IsAdmissibleAt M r ω}
  have hBad : P Bad = 0 := measure_union_null (measure_union_null (ae_iff.1 hpos) (ae_iff.1 hunb))
    (ae_iff.1 (run r).adm)
  have hmu := N.muK_pos k
  apply assemble P _ Bad hBad _ _ _ (by positivity) hch
  rintro ω ⟨hdev, hτ, hB⟩
  by_cases hω : ω ∈ Bad
  · exact Or.inl hω
  right
  simp only [Bad, Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hω
  obtain ⟨⟨hp, hu⟩, hadm⟩ := hω
  set τ := ((run r).tau l n ω).toReal
  have hτ0 : 0 ≤ τ := ENNReal.toReal_nonneg
  have hτT : τ ≤ (r : ℝ) ^ 2 * T := ENNReal.toReal_le_of_le_ofReal (by positivity) hτ
  have hTk := hadm.2.2.2.2.2.2.2.2.2.2.1 k
  have hidle := hadm.2.2.2.2.2.2.2.2.1 k
  have hTk0 : (run r).Tk k ω 0 = 0 := by
    have := hidle.2.1; simp only [Paths.Ik] at this; linarith
  have hs0 : 0 ≤ (run r).Tk k ω τ := by
    have := hTk.2 (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hτ0) hτ0
    rwa [hTk0] at this
  have hTle : (run r).Tk k ω τ ≤ τ := by
    have h1 := hidle.1 (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hτ0) hτ0
    rw [hidle.2.1] at h1
    simp only [Paths.Ik] at h1
    linarith
  set s0 := (run r).Tk k ω τ
  have hdev' : ∃ t ∈ Set.Icc 0 (a * r), b * r <
      |(count (fun l => M.v k l ω / 1) (s0 + t) : ℝ) -
        (count (fun l => M.v k l ω / 1) s0 : ℝ) - N.muK k * t| := by
    simpa only [div_one, Model.Ss, Model.S] using hdev
  obtain ⟨s', hs', y, hy, hd⟩ := window (fun l => M.v k l ω) 1 (N.muK k) one_pos hmu hp hu
    s0 hs0 r a b (N.muK k) ha hb hbr le_rfl hdev'
  have hmK : count (fun l => M.v k l ω / 1) s0 ∈ Finset.range ⌊N.C8 * (r : ℝ) ^ 2 * T⌋₊ := by
    apply m_lt_K0
    have h1 := hB.2.2 k
    have h2 := count_mono _ hp hu hs0 (hTle.trans hτT)
    have h3 : (count (fun l => M.v k l ω) s0 : ℝ) ≤
        (M.S k ω ((r : ℝ) ^ 2 * T) : ℝ) := by exact_mod_cast h2
    simp only [div_one]
    linarith
  simp only [Set.mem_iUnion, Set.mem_union, Set.mem_ofPred_eq]
  refine ⟨_, hmK, ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs'
  rcases hs' with rfl | rfl
  · right; exact ⟨y, hy, hd⟩
  · left; exact ⟨y, hy, hd⟩

end Parts


theorem C8_pos (N : Network) : 0 < N.C8 := by
  unfold Network.C8
  have h1 : N.lamBar ≤ (insert N.lamBar (insert N.muBar (Finset.univ.image N.muK))).max'
      (Finset.insert_nonempty _ _) := Finset.le_max' _ _ (Finset.mem_insert_self _ _)
  have h2 : N.lam ⟨0, N.J_pos⟩ ≤ N.lamBar := by
    unfold Network.lamBar
    exact Finset.le_sup' N.lam (Finset.mem_univ _)
  have h3 := N.lam_pos ⟨0, N.J_pos⟩
  linarith

/-- a positive constant below finitely many positive constants -/
theorem small_le {ι : Type*} [Fintype ι] (C : ι → ℝ) (hC : ∀ i, 0 < C i) (S : ℝ) (hS : 0 ≤ S)
    (i : ι) : 1 / (1 + S + ∑ i, 1 / C i) ≤ C i := by
  have h1 : 1 / C i ≤ ∑ i, 1 / C i :=
    Finset.single_le_sum (f := fun i => 1 / C i) (fun i _ => le_of_lt (by have := hC i; positivity))
      (Finset.mem_univ i)
  have hci := hC i
  have hpos : 0 < 1 + S + ∑ i, 1 / C i := by
    have : 0 ≤ ∑ i, 1 / C i := Finset.sum_nonneg (fun i _ => le_of_lt (by have := hC i; positivity))
    linarith
  rw [div_le_iff₀ hpos]
  have : 1 ≤ C i * (1 / C i) + C i * S + C i * (∑ i, 1 / C i - 1 / C i) := by
    rw [mul_one_div_cancel hci.ne']
    have : 0 ≤ C i * S := mul_nonneg hci.le hS
    have : 0 ≤ C i * (∑ i, 1 / C i - 1 / C i) := mul_nonneg hci.le (by linarith)
    linarith
  nlinarith

end FJL5

theorem solution {N : Network} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (M : Model N Ω P) (hA1 : M.Assumption1) (hA2 : M.Assumption2)
    (run : ∀ r : ℕ, PolicyRun M r) (T : ℝ) (hT : 0 < T) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∃ r1 : ℕ, 1 ≤ r1 ∧ ∃ C9 : ℝ, 0 < C9 ∧ ∃ C10 : ℝ, 0 < C10 ∧ ∀ r : ℕ, r1 ≤ r →
      (∀ (j : Fin N.J) (l : Fin N.I) (n : ℕ), 1 ≤ n → n ≤ N.Mr T r →
        P {ω | (∃ t ∈ Set.Icc 0 (a * r),
              b * r < |(M.A r j ω (((run r).tau l n ω).toReal + t) : ℝ)
                - (M.A r j ω ((run r).tau l n ω).toReal : ℝ) - M.lamr r j * t|) ∧
            (run r).tau l n ω ≤ ENNReal.ofReal ((r : ℝ) ^ 2 * T) ∧ ω ∈ M.Bevent T r}
          ≤ ENNReal.ofReal (C9 * (r : ℝ) ^ 2 * Real.exp (-C10 * r))) ∧
      (∀ (j : Fin N.J) (i : Fin N.I) (l : Fin N.I) (n : ℕ), N.P i j = true → 1 ≤ n →
        n ≤ N.Mr T r →
        P {ω | (∃ t ∈ Set.Icc 0 (a * r),
              b * r < |(M.Ss i j ω ((run r).Tij i j ω ((run r).tau l n ω).toReal + t) : ℝ)
                - (M.Ss i j ω ((run r).Tij i j ω ((run r).tau l n ω).toReal) : ℝ)
                - N.mu i j * t|) ∧
            (run r).tau l n ω ≤ ENNReal.ofReal ((r : ℝ) ^ 2 * T) ∧ ω ∈ M.Bevent T r}
          ≤ ENNReal.ofReal (C9 * (r : ℝ) ^ 2 * Real.exp (-C10 * r))) ∧
      (∀ (k : Fin N.K) (l : Fin N.I) (n : ℕ), 1 ≤ n → n ≤ N.Mr T r →
        P {ω | (∃ t ∈ Set.Icc 0 (a * r),
              b * r < |(M.S k ω ((run r).Tk k ω ((run r).tau l n ω).toReal + t) : ℝ)
                - (M.S k ω ((run r).Tk k ω ((run r).tau l n ω).toReal) : ℝ)
                - N.muK k * t|) ∧
            (run r).tau l n ω ≤ ENNReal.ofReal ((r : ℝ) ^ 2 * T) ∧ ω ∈ M.Bevent T r}
          ≤ ENNReal.ofReal (C9 * (r : ℝ) ^ 2 * Real.exp (-C10 * r))) := by
  haveI := M.isProb
  obtain ⟨αbar, hα, hmom⟩ := hA1
  -- Chernoff constants for the three families
  have harr : ∀ j : Fin N.J, ∃ C : ℝ, 0 < C ∧ ∃ r0 : ℕ, ∀ r : ℕ, r0 ≤ r → ∀ m : ℕ,
      P {ω | ∃ y ∈ Finset.Icc 1 ⌊(b + (N.lam j + 1) * a) * r⌋₊,
        b / 2 * r < |∑ n ∈ Finset.Icc 1 y, (M.ubar j (m + n) ω - 1)|} ≤
        ENNReal.ofReal (2 * Real.exp (-C * r)) := by
    intro j
    have hl := N.lam_pos j
    exact FJL5.shifted_chernoff P (M.ubar j) 1 (fun n => M.meas (.arr j n)) (FJL5.indep_arr M j)
      (M.ubar_ident j) ((M.ubar_L2 j).integrable one_le_two) (M.ubar_mean j)
      ⟨αbar, hα, fun α hα' => (hmom α hα').1 j⟩ (b + (N.lam j + 1) * a) (b / 2)
      (by positivity) (by positivity)
  have hsh : ∀ i : Fin N.I, ∀ j : Fin N.J, ∃ C : ℝ, 0 < C ∧ ∃ r0 : ℕ, N.P i j = true →
      ∀ r : ℕ, r0 ≤ r → ∀ m : ℕ,
      P {ω | ∃ y ∈ Finset.Icc 1 ⌊(b + N.mu i j * a) * r⌋₊,
        1 / N.mu i j * (b / 2) * r < |∑ n ∈ Finset.Icc 1 y, (M.vs i j (m + n) ω - 1 / N.mu i j)|}
        ≤ ENNReal.ofReal (2 * Real.exp (-C * r)) := by
    intro i j
    by_cases hij : N.P i j = true
    · have hm := N.mu_pos i j hij
      obtain ⟨C, hC, r0, h⟩ := FJL5.shifted_chernoff P (M.vs i j) (1 / N.mu i j)
        (fun n => M.meas (.sh i j n)) (FJL5.indep_sh M i j hij)
        (fun n hn => M.vs_ident i j n hij hn) ((M.vs_L2 i j hij).integrable one_le_two)
        (M.vs_mean i j hij) ⟨αbar, hα, fun α hα' => (hmom α hα').2.2 i j hij⟩
        (b + N.mu i j * a) (1 / N.mu i j * (b / 2)) (by positivity) (by positivity)
      exact ⟨C, hC, r0, fun _ => h⟩
    · exact ⟨1, one_pos, 0, fun h => absurd h hij⟩
  have hded : ∀ k : Fin N.K, ∃ C : ℝ, 0 < C ∧ ∃ r0 : ℕ, ∀ r : ℕ, r0 ≤ r → ∀ m : ℕ,
      P {ω | ∃ y ∈ Finset.Icc 1 ⌊(b + N.muK k * a) * r⌋₊,
        1 / N.muK k * (b / 2) * r < |∑ n ∈ Finset.Icc 1 y, (M.v k (m + n) ω - 1 / N.muK k)|}
        ≤ ENNReal.ofReal (2 * Real.exp (-C * r)) := by
    intro k
    have hm := N.muK_pos k
    exact FJL5.shifted_chernoff P (M.v k) (1 / N.muK k) (fun n => M.meas (.ded k n))
      (FJL5.indep_ded M k) (M.v_ident k) ((M.v_L2 k).integrable one_le_two) (M.v_mean k)
      ⟨αbar, hα, fun α hα' => (hmom α hα').2.1 k⟩ (b + N.muK k * a) (1 / N.muK k * (b / 2))
      (by positivity) (by positivity)
  choose Ca hCa ra hra using harr
  choose Cs hCs rs hrs using hsh
  choose Cd hCd rd hrd using hded
  -- the arrival rates are eventually below `λ_j + 1`
  have hlam : ∀ᶠ r : ℕ in atTop, ∀ j, M.lamr r j ≤ N.lam j + 1 := by
    rw [eventually_all]
    intro j
    exact ((hA2.1 j).eventually (gt_mem_nhds (lt_add_one (N.lam j)))).mono (fun r h => h.le)
  obtain ⟨rl, hrl⟩ := eventually_atTop.1 hlam
  -- constants
  set Ssh : ℝ := ∑ p : Fin N.I × Fin N.J, 1 / Cs p.1 p.2
  set Sd : ℝ := ∑ k, 1 / Cd k
  set Sa : ℝ := ∑ j, 1 / Ca j
  have hSsh : 0 ≤ Ssh := Finset.sum_nonneg (fun p _ => le_of_lt (by have := hCs p.1 p.2; positivity))
  have hSd : 0 ≤ Sd := Finset.sum_nonneg (fun k _ => le_of_lt (by have := hCd k; positivity))
  have hSa : 0 ≤ Sa := Finset.sum_nonneg (fun j _ => le_of_lt (by have := hCa j; positivity))
  set C10 : ℝ := 1 / (1 + (Ssh + Sd + Sa)) with hC10
  have hC10pos : 0 < C10 := by positivity
  have hinv : ∀ C X : ℝ, 0 < C → 1 / C ≤ X → 1 / (1 + X) ≤ C := by
    intro C X hC hX
    have hX0 : 0 ≤ X := le_trans (by positivity) hX
    rw [div_le_iff₀ (by linarith)]
    have : C * (1 / C) ≤ C * X := mul_le_mul_of_nonneg_left hX hC.le
    rw [mul_one_div_cancel hC.ne'] at this
    nlinarith
  have hC10a : ∀ j, C10 ≤ Ca j := by
    intro j
    apply hinv _ _ (hCa j)
    have : 1 / Ca j ≤ Sa := Finset.single_le_sum (f := fun j => 1 / Ca j)
      (fun j _ => le_of_lt (by have := hCa j; positivity)) (Finset.mem_univ j)
    linarith
  have hC10s : ∀ i j, C10 ≤ Cs i j := by
    intro i j
    apply hinv _ _ (hCs i j)
    have : 1 / Cs i j ≤ Ssh := Finset.single_le_sum (f := fun p : Fin N.I × Fin N.J => 1 / Cs p.1 p.2)
      (fun p _ => le_of_lt (by have := hCs p.1 p.2; positivity)) (Finset.mem_univ (i, j))
    linarith
  have hC10d : ∀ k, C10 ≤ Cd k := by
    intro k
    apply hinv _ _ (hCd k)
    have : 1 / Cd k ≤ Sd := Finset.single_le_sum (f := fun k => 1 / Cd k)
      (fun k _ => le_of_lt (by have := hCd k; positivity)) (Finset.mem_univ k)
    linarith
  have hC8 := FJL5.C8_pos N
  set C9 : ℝ := 4 * N.C8 * T + 1 with hC9
  set r1 : ℕ := 1 + rl + ⌈2 / b⌉₊ + ∑ j, ra j + ∑ p : Fin N.I × Fin N.J, rs p.1 p.2 + ∑ k, rd k
  have hra1 : ∀ j, ra j ≤ r1 := by
    intro j
    have := Finset.single_le_sum (f := ra) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    simp only [r1]; omega
  have hrs1 : ∀ i j, rs i j ≤ r1 := by
    intro i j
    have := Finset.single_le_sum (f := fun p : Fin N.I × Fin N.J => rs p.1 p.2)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ (i, j))
    simp only at this
    simp only [r1]; omega
  have hrd1 : ∀ k, rd k ≤ r1 := by
    intro k
    have := Finset.single_le_sum (f := rd) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    simp only [r1]; omega
  refine ⟨r1, by omega, C9, by positivity, C10, hC10pos, fun r hr => ?_⟩
  have hrl' : rl ≤ r := by omega
  have hbr : 2 ≤ b * r := by
    have h1 : ⌈2 / b⌉₊ ≤ r := by omega
    have h2 : 2 / b ≤ (r : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast h1)
    rw [div_le_iff₀ hb] at h2; linarith
  -- final numeric comparison
  have hfin : ∀ C : ℝ, C10 ≤ C →
      ENNReal.ofReal (2 * ⌊N.C8 * (r : ℝ) ^ 2 * T⌋₊ * (2 * Real.exp (-C * r))) ≤
        ENNReal.ofReal (C9 * (r : ℝ) ^ 2 * Real.exp (-C10 * r)) := by
    intro C hC
    apply ENNReal.ofReal_le_ofReal
    have hfl : (⌊N.C8 * (r : ℝ) ^ 2 * T⌋₊ : ℝ) ≤ N.C8 * (r : ℝ) ^ 2 * T :=
      Nat.floor_le (by positivity)
    have he : Real.exp (-C * r) ≤ Real.exp (-C10 * r) := by
      apply Real.exp_le_exp.2
      have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      nlinarith
    have hr2 : (0 : ℝ) ≤ (r : ℝ) ^ 2 := by positivity
    calc 2 * (⌊N.C8 * (r : ℝ) ^ 2 * T⌋₊ : ℝ) * (2 * Real.exp (-C * r))
        ≤ 2 * (N.C8 * (r : ℝ) ^ 2 * T) * (2 * Real.exp (-C10 * r)) := by
          apply mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
      _ = (4 * N.C8 * T) * (r : ℝ) ^ 2 * Real.exp (-C10 * r) := by ring
      _ ≤ C9 * (r : ℝ) ^ 2 * Real.exp (-C10 * r) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_right _ hr2
          rw [hC9]; linarith
  refine ⟨?_, ?_, ?_⟩
  · intro j l n _ _
    refine le_trans ?_ (hfin (Ca j) (hC10a j))
    exact FJL5.part_a M run T hT a b ha hb j (N.lam j + 1) (Ca j) r hbr (hrl r hrl' j)
      (hra j r (le_trans (hra1 j) hr))
      (FJL5.pos_ae (M.ubar_pos j))
      (FJL5.ae_unbounded P (M.ubar j) 1 (fun n => M.meas (.arr j n)) (FJL5.indep_arr M j)
        (M.ubar_ident j) ((M.ubar_L2 j).integrable one_le_two) (M.ubar_mean j)
        ⟨αbar, hα, fun α hα' => (hmom α hα').1 j⟩ one_pos) l n
  · intro j i l n hij _ _
    refine le_trans ?_ (hfin (Cs i j) (hC10s i j))
    have hm := N.mu_pos i j hij
    exact FJL5.part_b M run T hT a b ha hb i j hij (Cs i j) r hbr
      (hrs i j hij r (le_trans (hrs1 i j) hr))
      (FJL5.pos_ae (fun n hn => M.vs_pos i j n hij hn))
      (FJL5.ae_unbounded P (M.vs i j) (1 / N.mu i j) (fun n => M.meas (.sh i j n))
        (FJL5.indep_sh M i j hij) (fun n hn => M.vs_ident i j n hij hn)
        ((M.vs_L2 i j hij).integrable one_le_two) (M.vs_mean i j hij)
        ⟨αbar, hα, fun α hα' => (hmom α hα').2.2 i j hij⟩ (by positivity)) l n
  · intro k l n _ _
    refine le_trans ?_ (hfin (Cd k) (hC10d k))
    have hm := N.muK_pos k
    exact FJL5.part_c M run T hT a b ha hb k (Cd k) r hbr
      (hrd k r (le_trans (hrd1 k) hr))
      (FJL5.pos_ae (M.v_pos k))
      (FJL5.ae_unbounded P (M.v k) (1 / N.muK k) (fun n => M.meas (.ded k n))
        (FJL5.indep_ded M k) (M.v_ident k) ((M.v_L2 k).integrable one_le_two) (M.v_mean k)
        ⟨αbar, hα, fun α hα' => (hmom α hα').2.1 k⟩ (by positivity)) l n

