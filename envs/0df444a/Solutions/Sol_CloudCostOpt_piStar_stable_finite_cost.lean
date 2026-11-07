-- Prove2me | solution 1 for CloudCostOpt.piStar_stable_finite_cost
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-06T17:55:27.636059+00:00
-- url     : https://prove2.me/submissions/7862b5a0-adce-450f-b460-e426b162902d

import Mathlib
import Definitions.Def_CloudCostOpt_piStar
import Definitions.Def_CloudCostOpt_avgCost
import Definitions.Def_CloudCostOpt_IsStable
import Definitions.Def_CloudCostOpt_Standing

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CloudCostOpt

/-! ## Part 1: pathwise dynamics of `π*` -/

/-- number of the `x` orders of cell `(i,s,l)` sent to `j` in period `t` whose step succeeds -/
noncomputable def c1Succ (S : System)
    (U : Fin S.I × ℕ × ℕ × ℕ × Fin (S.J + 1) × ℕ → unitInterval)
    (t : ℕ) (i : Fin S.I) (s l : ℕ) (j : Fin (S.J + 1)) (x : ℕ) : ℕ :=
  ((Finset.range x).filter fun k => ((U (i, t, s, l, j, k) : ℝ) < S.β i j)).card

/-- number of those whose step fails -/
noncomputable def c1Fail (S : System)
    (U : Fin S.I × ℕ × ℕ × ℕ × Fin (S.J + 1) × ℕ → unitInterval)
    (t : ℕ) (i : Fin S.I) (s l : ℕ) (j : Fin (S.J + 1)) (x : ℕ) : ℕ :=
  ((Finset.range x).filter fun k => ¬ ((U (i, t, s, l, j, k) : ℝ) < S.β i j)).card

theorem c1_cellSucc (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0)
    (U : Fin S.I × ℕ × ℕ × ℕ × Fin (S.J + 1) × ℕ → unitInterval) (t n : ℕ)
    (h : Fin (n + 1) → State S) (i : Fin S.I) (s l : ℕ) :
    cellSucc S U t i s l ((piStar S sel lam).a n h i s l) =
      c1Succ S U t i s l (sel.jStar i s l) (h (Fin.last n) i s l) := by
  unfold cellSucc c1Succ
  rw [Finset.sum_eq_single (sel.jStar i s l)]
  · simp [piStar, piHat]
  · intro j _ hj
    simp [piStar, piHat, hj]
  · simp

theorem c1_cellFail (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0)
    (U : Fin S.I × ℕ × ℕ × ℕ × Fin (S.J + 1) × ℕ → unitInterval) (t n : ℕ)
    (h : Fin (n + 1) → State S) (i : Fin S.I) (s l : ℕ) :
    cellFail S U t i s l ((piStar S sel lam).a n h i s l) =
      c1Fail S U t i s l (sel.jStar i s l) (h (Fin.last n) i s l) := by
  unfold cellFail
  rw [c1_cellSucc]
  have hsum : ∑ j, (piStar S sel lam).a n h i s l j = h (Fin.last n) i s l := by
    simp [piStar, piHat]
  rw [hsum]
  have := Finset.card_filter_add_card_filter_not
    (s := Finset.range (h (Fin.last n) i s l))
    (fun k => ((U (i, t, s, l, sel.jStar i s l, k) : ℝ) < S.β i (sel.jStar i s l)))
  simp only [Finset.card_range] at this
  unfold c1Succ c1Fail
  omega

theorem c1_st_zero (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0) (ω : Omega S)
    (n : ℕ) (i : Fin S.I) (l : ℕ) :
    stateAt S (piStar S sel lam) ω (n + 1) i 0 l =
      if S.L i ≤ l then 0 else if l = 0 then ω.1 (i, n + 1) else 0 := by
  simp only [stateAt, history, Fin.snoc_last]

theorem c1_st_succ (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0) (ω : Omega S)
    (n : ℕ) (i : Fin S.I) (s l : ℕ) :
    stateAt S (piStar S sel lam) ω (n + 1) i (s + 1) l =
      if S.L i ≤ l then 0 else
        (if l = 0 then 0 else c1Succ S ω.2 (n + 1) i s (l - 1) (sel.jStar i s (l - 1))
            (stateAt S (piStar S sel lam) ω n i s (l - 1))) +
        c1Fail S ω.2 (n + 1) i s l (sel.jStar i s l) (stateAt S (piStar S sel lam) ω n i s l) := by
  simp only [stateAt, history, Fin.snoc_last, c1_cellSucc, c1_cellFail]

theorem c1_st_old (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0) (ω : Omega S) :
    ∀ n i s l, n ≤ s → stateAt S (piStar S sel lam) ω n i s l = 0 := by
  intro n
  induction n with
  | zero => intro i s l _; simp [stateAt, history]
  | succ n ih =>
    intro i s l hs
    obtain ⟨s, rfl⟩ : ∃ s0, s = s0 + 1 := ⟨s - 1, by omega⟩
    rw [c1_st_succ, ih i s (l - 1) (by omega), ih i s l (by omega)]
    simp [c1Succ, c1Fail]

/-- the time shift of the sample point by one period -/
def c1shift (S : System) (ω : Omega S) : Omega S :=
  (fun p => ω.1 (p.1, p.2 + 1), fun p => ω.2 (p.1, p.2.1 + 1, p.2.2))

theorem c1_st_shift (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0) (ω : Omega S) :
    ∀ n i s l, s < n → stateAt S (piStar S sel lam) ω (n + 1) i s l =
      stateAt S (piStar S sel lam) (c1shift S ω) n i s l := by
  intro n
  induction n with
  | zero => intro i s l h; omega
  | succ n ih =>
    intro i s l h
    rcases s with _ | s
    · rw [c1_st_zero, c1_st_zero]; rfl
    · rw [c1_st_succ, c1_st_succ, ih i s (l - 1) (by omega), ih i s l (by omega)]; rfl

/-! ## Part 2: deterministic summability of the rates -/

theorem c1_rateX_succ (S : System) (hS : Standing S) (sel : Selection S)
    (lam : Fin S.I → ℝ≥0) (i : Fin S.I) (s l : ℕ) (hl : l < S.L i) :
    (rateX S sel lam i (s + 1) l : ℝ) =
      (if l = 0 then 0 else S.β i (sel.jStar i s (l - 1)) * rateX S sel lam i s (l - 1)) +
        (1 - S.β i (sel.jStar i s l)) * rateX S sel lam i s l := by
  have h1 := hS.β_nonneg i (sel.jStar i s l)
  have h2 := hS.β_le_one i (sel.jStar i s l)
  have h3 := hS.β_nonneg i (sel.jStar i s (l - 1))
  have e1 : (((1 - S.β i (sel.jStar i s l)).toNNReal : ℝ≥0) : ℝ) = 1 - S.β i (sel.jStar i s l) :=
    Real.coe_toNNReal _ (by linarith)
  have e2 : (((S.β i (sel.jStar i s (l - 1))).toNNReal : ℝ≥0) : ℝ) = S.β i (sel.jStar i s (l - 1)) :=
    Real.coe_toNNReal _ h3
  rw [rateX]
  simp only [not_le.2 hl, if_false]
  split_ifs with h0
  · simp [e1]
  · simp [e1, e2]

/-- potential: remaining steps of the age-`s` cohort, in expectation -/
noncomputable def c1Pot (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0) (i : Fin S.I)
    (s : ℕ) : ℝ :=
  ∑ l ∈ Finset.range (S.L i), ((S.L i : ℝ) - l) * rateX S sel lam i s l

theorem c1_pot_succ (S : System) (hS : Standing S) (sel : Selection S)
    (lam : Fin S.I → ℝ≥0) (i : Fin S.I) (s : ℕ) :
    c1Pot S sel lam i (s + 1) = c1Pot S sel lam i s -
      ∑ l ∈ Finset.range (S.L i), S.β i (sel.jStar i s l) * rateX S sel lam i s l := by
  obtain ⟨K, hK⟩ : ∃ K, S.L i = K + 1 := ⟨S.L i - 1, by have := hS.one_le_L i; omega⟩
  unfold c1Pot
  have hc : ∀ l ∈ Finset.range (S.L i), ((S.L i : ℝ) - l) * rateX S sel lam i (s + 1) l =
      ((S.L i : ℝ) - l) * (if l = 0 then 0 else
        S.β i (sel.jStar i s (l - 1)) * rateX S sel lam i s (l - 1)) +
      ((S.L i : ℝ) - l) * ((1 - S.β i (sel.jStar i s l)) * rateX S sel lam i s l) := by
    intro l hl
    rw [c1_rateX_succ S hS sel lam i s l (Finset.mem_range.1 hl), mul_add]
  rw [Finset.sum_congr rfl hc, Finset.sum_add_distrib]
  rw [hK]
  rw [Finset.sum_range_succ' (fun l => ((((K + 1 : ℕ) : ℝ)) - l) * (if l = 0 then 0 else
        S.β i (sel.jStar i s (l - 1)) * rateX S sel lam i s (l - 1)))]
  have hlast : ∑ l ∈ Finset.range (K + 1), ((K : ℝ) - l) *
      (S.β i (sel.jStar i s l) * rateX S sel lam i s l) =
      ∑ l ∈ Finset.range K, ((K : ℝ) - l) *
      (S.β i (sel.jStar i s l) * rateX S sel lam i s l) := by
    rw [Finset.sum_range_succ]; simp
  have hA : ∑ l ∈ Finset.range K, ((((K + 1 : ℕ) : ℝ)) - ((l + 1 : ℕ) : ℝ)) *
      (if l + 1 = 0 then 0 else
        S.β i (sel.jStar i s (l + 1 - 1)) * rateX S sel lam i s (l + 1 - 1)) =
      ∑ l ∈ Finset.range K, ((K : ℝ) - l) *
      (S.β i (sel.jStar i s l) * rateX S sel lam i s l) := by
    apply Finset.sum_congr rfl
    intro l _
    simp only [Nat.add_sub_cancel, Nat.add_one_ne_zero, if_false]
    push_cast; ring
  rw [hA, ← hlast]
  simp only [if_true, mul_zero, add_zero]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  push_cast; ring

theorem c1_pot_le (S : System) (hS : Standing S) (sel : Selection S)
    (lam : Fin S.I → ℝ≥0) (i : Fin S.I) (s : ℕ) :
    c1Pot S sel lam i (s + 1) ≤ c1Pot S sel lam i s := by
  rw [c1_pot_succ S hS sel lam i s]
  have : 0 ≤ ∑ l ∈ Finset.range (S.L i), S.β i (sel.jStar i s l) * rateX S sel lam i s l :=
    Finset.sum_nonneg fun l _ => mul_nonneg (hS.β_nonneg _ _) (NNReal.coe_nonneg _)
  linarith

theorem c1_pot_le0 (S : System) (hS : Standing S) (sel : Selection S)
    (lam : Fin S.I → ℝ≥0) (i : Fin S.I) : ∀ s, c1Pot S sel lam i s ≤ c1Pot S sel lam i 0 := by
  intro s
  induction s with
  | zero => exact le_refl _
  | succ s ih => exact (c1_pot_le S hS sel lam i s).trans ih

theorem c1_mass_le_pot (S : System) (sel : Selection S)
    (lam : Fin S.I → ℝ≥0) (i : Fin S.I) (s : ℕ) :
    ∑ l ∈ Finset.range (S.L i), (rateX S sel lam i s l : ℝ) ≤ c1Pot S sel lam i s := by
  unfold c1Pot
  apply Finset.sum_le_sum
  intro l hl
  have : (l : ℝ) + 1 ≤ S.L i := by
    have := Finset.mem_range.1 hl; exact_mod_cast this
  have h0 : (0 : ℝ) ≤ rateX S sel lam i s l := NNReal.coe_nonneg _
  nlinarith

theorem c1_mass_bound (S : System) (hS : Standing S) (sel : Selection S)
    (lam : Fin S.I → ℝ≥0) (i : Fin S.I) (N : ℕ) :
    ∑ s ∈ Finset.range N, ∑ l ∈ Finset.range (S.L i), (rateX S sel lam i s l : ℝ) ≤
      S.δ i * c1Pot S sel lam i 0 + c1Pot S sel lam i 0 / S.β i (sel.jLate i) := by
  set b := S.β i (sel.jLate i) with hb
  have hbpos : 0 < b := sel.jLate_pos i
  set P0 := c1Pot S sel lam i 0
  have hP0 : 0 ≤ P0 := (le_trans (Finset.sum_nonneg fun l _ => NNReal.coe_nonneg _)
    (c1_mass_le_pot S sel lam i 0))
  have key : ∀ s, ∑ l ∈ Finset.range (S.L i), (rateX S sel lam i s l : ℝ) ≤
      (if s < S.δ i then P0 else 0) +
        (c1Pot S sel lam i s - c1Pot S sel lam i (s + 1)) / b := by
    intro s
    have hd : 0 ≤ c1Pot S sel lam i s - c1Pot S sel lam i (s + 1) := by
      linarith [c1_pot_le S hS sel lam i s]
    split_ifs with hs
    · have := c1_mass_le_pot S sel lam i s
      have := c1_pot_le0 S hS sel lam i s
      have : 0 ≤ (c1Pot S sel lam i s - c1Pot S sel lam i (s + 1)) / b := div_nonneg hd hbpos.le
      linarith
    · rw [c1_pot_succ S hS sel lam i s]
      have hj : ∀ l, sel.jStar i s l = sel.jLate i := by
        intro l; simp [Selection.jStar, hs]
      simp only [hj, ← Finset.mul_sum]
      rw [← hb]
      field_simp
      linarith
  calc ∑ s ∈ Finset.range N, ∑ l ∈ Finset.range (S.L i), (rateX S sel lam i s l : ℝ)
      ≤ ∑ s ∈ Finset.range N, ((if s < S.δ i then P0 else 0) +
        (c1Pot S sel lam i s - c1Pot S sel lam i (s + 1)) / b) := Finset.sum_le_sum fun s _ => key s
    _ = ∑ s ∈ Finset.range N, (if s < S.δ i then P0 else 0) +
        (P0 - c1Pot S sel lam i N) / b := by
      rw [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_range_sub']
    _ ≤ S.δ i * P0 + P0 / b := by
      gcongr
      · rw [← Finset.sum_filter]
        calc ∑ s ∈ (Finset.range N).filter (· < S.δ i), P0
            ≤ ∑ s ∈ Finset.range (S.δ i), P0 := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro s hs; simp only [Finset.mem_filter] at hs; exact Finset.mem_range.2 hs.2
              · intro _ _ _; exact hP0
          _ = S.δ i * P0 := by simp
      · have : 0 ≤ c1Pot S sel lam i N :=
          le_trans (Finset.sum_nonneg fun l _ => NNReal.coe_nonneg _)
            (c1_mass_le_pot S sel lam i N)
        linarith

/-- the total expected sojourn of type-`i` orders is finite -/
theorem c1_G_lt_top (S : System) (hS : Standing S) (sel : Selection S)
    (lam : Fin S.I → ℝ≥0) (i : Fin S.I) :
    ∑' s, ∑ l ∈ Finset.range (S.L i), (rateX S sel lam i s l : ℝ≥0∞) < ⊤ := by
  refine lt_of_le_of_lt (ENNReal.tsum_le_of_sum_range_le (c := ENNReal.ofReal
    (S.δ i * c1Pot S sel lam i 0 + c1Pot S sel lam i 0 / S.β i (sel.jLate i))) fun N => ?_)
    ENNReal.ofReal_lt_top
  have := c1_mass_bound S hS sel lam i N
  refine le_trans (le_of_eq ?_) (ENNReal.ofReal_le_ofReal this)
  rw [ENNReal.ofReal_sum_of_nonneg (fun s _ => Finset.sum_nonneg fun l _ => NNReal.coe_nonneg _)]
  apply Finset.sum_congr rfl; intro s _
  rw [ENNReal.ofReal_sum_of_nonneg (fun l _ => NNReal.coe_nonneg _)]
  apply Finset.sum_congr rfl; intro l _
  simp

/-! ## Part 3: Cesàro averages in `ℝ≥0∞` -/

theorem c1_cesaro (a : ℕ → ℝ≥0∞) (c : ℝ≥0) (ha : Tendsto a atTop (𝓝 (c : ℝ≥0∞)))
    (hfin : ∀ n, a n ≠ ⊤) :
    Tendsto (fun T : ℕ => (∑ n ∈ Finset.range T, a n) / (T : ℝ≥0∞)) atTop (𝓝 (c : ℝ≥0∞)) := by
  have hr : Tendsto (fun n => (a n).toReal) atTop (𝓝 (c : ℝ)) := by
    have := (ENNReal.tendsto_toReal ENNReal.coe_ne_top).comp ha
    rw [ENNReal.coe_toReal] at this
    exact this
  have h2 := ENNReal.tendsto_ofReal hr.cesaro
  rw [ENNReal.ofReal_coe_nnreal] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with T hT
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  rw [ENNReal.ofReal_mul (inv_nonneg.2 hTpos.le), ENNReal.ofReal_inv_of_pos hTpos,
    ENNReal.ofReal_natCast,
    ENNReal.ofReal_sum_of_nonneg (fun n _ => ENNReal.toReal_nonneg)]
  simp only [ENNReal.ofReal_toReal (hfin _)]
  rw [div_eq_mul_inv, mul_comm]

/-! ## Part 4: measurability, dependence on the past, independence of the current uniforms -/

/-- index type of the uniforms -/
abbrev c1Idx (S : System) : Type := Fin S.I × ℕ × ℕ × ℕ × Fin (S.J + 1) × ℕ

/-- the law of the uniforms -/
noncomputable def c1μU (S : System) : Measure (c1Idx S → unitInterval) :=
  Measure.infinitePi fun _ : c1Idx S => (volume : Measure unitInterval)

/-- the σ-algebra of the uniforms of periods `≤ n` -/
noncomputable def c1MA (S : System) (n : ℕ) : MeasurableSpace (c1Idx S → unitInterval) :=
  ⨆ p ∈ {p : c1Idx S | p.2.1 ≤ n},
    MeasurableSpace.comap (fun U : c1Idx S → unitInterval => U p) inferInstance

theorem c1_meas_natfun {α : Type*} [MeasurableSpace α] {γ : Type*} [MeasurableSpace γ]
    (F : ℕ → α → γ) (hF : ∀ x, Measurable (F x)) (X : α → ℕ) (hX : Measurable X) :
    Measurable fun a => F (X a) a :=
  (measurable_from_prod_countable_left (f := fun p : α × ℕ => F p.2 p.1) fun y => hF y).comp
    (measurable_id.prodMk hX)

theorem c1_meas_cnt (S : System) (q : ℕ → c1Idx S) (P : unitInterval → Prop) [DecidablePred P]
    (hP : MeasurableSet {u | P u}) (X : Omega S → ℕ) (hX : Measurable X) :
    Measurable fun ω : Omega S => ((Finset.range (X ω)).filter fun k => P (ω.2 (q k))).card := by
  refine c1_meas_natfun (fun x (ω : Omega S) => ((Finset.range x).filter fun k => P (ω.2 (q k))).card)
    (fun x => ?_) X hX
  simp only [Finset.card_filter]
  refine Finset.measurable_sum _ fun k _ => ?_
  exact Measurable.ite (hP.preimage ((measurable_pi_apply (q k)).comp measurable_snd))
    measurable_const measurable_const

theorem c1_meas_st (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0) :
    ∀ n i s l, Measurable fun ω : Omega S => stateAt S (piStar S sel lam) ω n i s l := by
  intro n
  induction n with
  | zero => intro i s l; simp only [stateAt, history]; exact measurable_const
  | succ n ih =>
    intro i s l
    rcases s with _ | s
    · by_cases h1 : S.L i ≤ l
      · simp only [c1_st_zero, h1, if_true]; exact measurable_const
      · by_cases h2 : l = 0
        · subst h2
          simp only [c1_st_zero, h1, if_false, if_true]
          exact (measurable_pi_apply _).comp measurable_fst
        · simp only [c1_st_zero, h1, h2, if_false]; exact measurable_const
    · simp only [c1_st_succ]
      by_cases h1 : S.L i ≤ l
      · simp only [h1, if_true]; exact measurable_const
      simp only [h1, if_false]
      refine Measurable.add ?_ ?_
      · by_cases h2 : l = 0
        · simp only [h2, if_true]; exact measurable_const
        · simp only [h2, if_false]
          exact c1_meas_cnt S (fun k => (i, n + 1, s, l - 1, sel.jStar i s (l - 1), k))
            (fun u => (u : ℝ) < S.β i (sel.jStar i s (l - 1)))
            (measurableSet_lt measurable_subtype_coe measurable_const) _ (ih i s (l - 1))
      · exact c1_meas_cnt S (fun k => (i, n + 1, s, l, sel.jStar i s l, k))
          (fun u => ¬ (u : ℝ) < S.β i (sel.jStar i s l))
          (measurableSet_lt measurable_subtype_coe measurable_const).compl _ (ih i s l)

theorem c1Succ_congr (S : System) (U U' : c1Idx S → unitInterval) (t : ℕ) (i : Fin S.I)
    (s l : ℕ) (j : Fin (S.J + 1)) (x : ℕ)
    (h : ∀ k, U (i, t, s, l, j, k) = U' (i, t, s, l, j, k)) :
    c1Succ S U t i s l j x = c1Succ S U' t i s l j x := by
  unfold c1Succ; simp only [h]

theorem c1Fail_congr (S : System) (U U' : c1Idx S → unitInterval) (t : ℕ) (i : Fin S.I)
    (s l : ℕ) (j : Fin (S.J + 1)) (x : ℕ)
    (h : ∀ k, U (i, t, s, l, j, k) = U' (i, t, s, l, j, k)) :
    c1Fail S U t i s l j x = c1Fail S U' t i s l j x := by
  unfold c1Fail; simp only [h]

theorem c1_dep (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0) :
    ∀ n (N : Fin S.I × ℕ → ℕ) (U U' : c1Idx S → unitInterval),
      (∀ p : c1Idx S, p.2.1 ≤ n → U p = U' p) →
      ∀ i s l, stateAt S (piStar S sel lam) (N, U) n i s l =
        stateAt S (piStar S sel lam) (N, U') n i s l := by
  intro n
  induction n with
  | zero => intro N U U' _ i s l; simp [stateAt, history]
  | succ n ih =>
    intro N U U' h i s l
    rcases s with _ | s
    · simp only [c1_st_zero]
    · simp only [c1_st_succ]
      rw [ih N U U' (fun p hp => h p (by omega)) i s (l - 1),
        ih N U U' (fun p hp => h p (by omega)) i s l,
        c1Succ_congr S U U' _ i s (l - 1) _ _ (fun k => h _ le_rfl),
        c1Fail_congr S U U' _ i s l _ _ (fun k => h _ le_rfl)]

/-- projection on the uniforms of periods `≤ n` -/
noncomputable def c1proj (S : System) (n : ℕ) (U : c1Idx S → unitInterval) :
    c1Idx S → unitInterval :=
  fun p => if p.2.1 ≤ n then U p else 0

theorem c1_meas_proj (S : System) (n : ℕ) :
    Measurable[c1MA S n] (c1proj S n) := by
  let _ : MeasurableSpace (c1Idx S → unitInterval) := c1MA S n
  refine measurable_pi_lambda _ fun p => ?_
  by_cases h : p.2.1 ≤ n
  · simp only [c1proj, h, if_true]
    exact (comap_measurable (fun U : c1Idx S → unitInterval => U p)).mono
      (le_iSup₂ (f := fun (p : c1Idx S) (_ : p ∈ {p : c1Idx S | p.2.1 ≤ n}) =>
        MeasurableSpace.comap (fun U : c1Idx S → unitInterval => U p) inferInstance) p h) le_rfl
  · simp only [c1proj, h, if_false]; exact measurable_const

theorem c1_tsum_ind (x : ℕ) : ∑' k : ℕ, (if k < x then (1 : ℝ≥0∞) else 0) = x := by
  rw [tsum_eq_sum (s := Finset.range x) (fun k hk => by
    simp only [Finset.mem_range] at hk; simp [hk])]
  rw [Finset.sum_ite_of_true (fun k hk => Finset.mem_range.1 hk)]
  simp

theorem c1_inner (S : System) (n : ℕ) (q : ℕ → c1Idx S) (hq : ∀ k, (q k).2.1 = n + 1)
    (P : unitInterval → Prop) [DecidablePred P] (hP : MeasurableSet {u | P u})
    (x : (c1Idx S → unitInterval) → ℕ) (hx : Measurable[c1MA S n] x) :
    ∫⁻ U, ((((Finset.range (x U)).filter fun k => P (U (q k))).card : ℕ) : ℝ≥0∞) ∂(c1μU S) =
      volume {u | P u} * ∫⁻ U, (x U : ℝ≥0∞) ∂(c1μU S) := by
  have hle : c1MA S n ≤ MeasurableSpace.pi :=
    iSup₂_le fun p _ => (measurable_pi_apply p).comap_le
  have hxm : Measurable x := hx.mono hle le_rfl
  have hcard : ∀ U : c1Idx S → unitInterval,
      ((((Finset.range (x U)).filter fun k => P (U (q k))).card : ℕ) : ℝ≥0∞) =
      ∑' k, (if k < x U then (1 : ℝ≥0∞) else 0) * ({u | P u}.indicator 1 (U (q k))) := by
    intro U
    rw [Finset.card_filter]
    push_cast
    rw [tsum_eq_sum (s := Finset.range (x U)) (fun k hk => by
      simp only [Finset.mem_range] at hk; simp [hk])]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Finset.mem_range] at hk
    by_cases hp : P (U (q k)) <;> simp [hk, hp]
  simp_rw [hcard]
  have hgm : ∀ k, Measurable fun U : c1Idx S → unitInterval => ({u | P u}.indicator 1 (U (q k)) : ℝ≥0∞) :=
    fun k => (measurable_one.indicator hP).comp (measurable_pi_apply (q k))
  have hfm : ∀ k, Measurable[c1MA S n] fun U : c1Idx S → unitInterval =>
      (if k < x U then (1 : ℝ≥0∞) else 0) :=
    fun k => Measurable.ite (hx measurableSet_Ioi) measurable_const measurable_const
  rw [lintegral_tsum (f := fun k (U : c1Idx S → unitInterval) =>
      (if k < x U then (1 : ℝ≥0∞) else 0) * ({u | P u}.indicator 1 (U (q k))))
    (fun k => by exact (((hfm k).mono hle le_rfl).mul (hgm k)).aemeasurable)]
  have hind : ∀ k, ∫⁻ U, (if k < x U then (1 : ℝ≥0∞) else 0) * ({u | P u}.indicator 1 (U (q k))) ∂(c1μU S)
      = (∫⁻ U, (if k < x U then (1 : ℝ≥0∞) else 0) ∂(c1μU S)) * volume {u | P u} := by
    intro k
    let m : c1Idx S → MeasurableSpace (c1Idx S → unitInterval) := fun p =>
      MeasurableSpace.comap (fun U : c1Idx S → unitInterval => U p) inferInstance
    have hiI : iIndep m (c1μU S) := by
      have := iIndepFun_infinitePi (P := fun _ : c1Idx S => (volume : Measure unitInterval))
        (X := fun _ (u : unitInterval) => u) (fun _ => measurable_id)
      exact (iIndepFun_iff_iIndep _ _ _).1 this
    have hdisj : Disjoint {p : c1Idx S | p.2.1 ≤ n} ({q k} : Set (c1Idx S)) := by
      rw [Set.disjoint_singleton_right]
      simp only [Set.mem_setOf_eq, hq k]; omega
    have hI := indep_iSup_of_disjoint (fun p => (measurable_pi_apply p).comap_le) hiI hdisj
    have hg' : Measurable[⨆ p ∈ ({q k} : Set (c1Idx S)), m p]
        fun U : c1Idx S → unitInterval => ({u | P u}.indicator 1 (U (q k)) : ℝ≥0∞) :=
      ((measurable_one.indicator hP).comp
        (comap_measurable (fun U : c1Idx S → unitInterval => U (q k)))).mono
        (le_iSup₂ (f := fun p (_ : p ∈ ({q k} : Set (c1Idx S))) => m p) (q k) rfl) le_rfl
    rw [lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
      (iSup₂_le fun p _ => (measurable_pi_apply p).comap_le)
      (iSup₂_le fun p _ => (measurable_pi_apply p).comap_le) hI (hfm k) hg']
    congr 1
    unfold c1μU
    have := (measurePreserving_eval_infinitePi (fun _ : c1Idx S => (volume : Measure unitInterval))
      (q k)).lintegral_comp (measurable_one.indicator hP)
    rw [lintegral_indicator_one hP] at this
    exact this
  simp_rw [hind]
  rw [ENNReal.tsum_mul_right, mul_comm, ← lintegral_tsum
    (fun k => ((hfm k).mono hle le_rfl).aemeasurable)]
  simp_rw [c1_tsum_ind]

/-! ## Part 5: first moments `E x_n(s,l) = λ^x(s,l)` -/

theorem c1_poisson_mean (r : ℝ≥0) : ∫⁻ k, (k : ℝ≥0∞) ∂(poissonMeasure r) = r := by
  have e : ∫⁻ k, (k : ℝ≥0∞) ∂(poissonMeasure r) = ∑' n : ℕ,
      ENNReal.ofReal (Real.exp (-r) * r ^ n / (Nat.factorial n : ℝ)) * (n : ℝ≥0∞) := by
    rw [poissonMeasure, lintegral_sum_measure]
    simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  rw [e, tsum_eq_zero_add' ENNReal.summable]
  simp only [Nat.cast_zero, mul_zero, zero_add]
  have h : ∀ n : ℕ, ENNReal.ofReal (Real.exp (-r) * r ^ (n + 1) / (Nat.factorial (n + 1) : ℝ)) *
      ((n + 1 : ℕ) : ℝ≥0∞)
      = (r : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-r) * r ^ n / (Nat.factorial n : ℝ)) := by
    intro n
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Nat.factorial_succ]; push_cast
    have : (Nat.factorial n : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  rw [tsum_congr h, ENNReal.tsum_mul_left,
    ← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) (hasSum_one_poissonMeasure r).summable,
    (hasSum_one_poissonMeasure r).tsum_eq]
  simp

theorem c1_E_N (S : System) (lam : Fin S.I → ℝ≥0) (i : Fin S.I) (t : ℕ) :
    ∫⁻ ω, (ω.1 (i, t) : ℝ≥0∞) ∂(sampleMeasure S lam) = lam i := by
  unfold sampleMeasure
  rw [lintegral_prod (fun ω : Omega S => (ω.1 (i, t) : ℝ≥0∞)) (by
    exact (measurable_from_nat.comp ((measurable_pi_apply _).comp measurable_fst)).aemeasurable)]
  simp only [lintegral_const, measure_univ, mul_one]
  have := (measurePreserving_eval_infinitePi
    (fun p : Fin S.I × ℕ => poissonMeasure (lam p.1)) (i, t)).lintegral_comp
    (measurable_from_nat (f := fun k : ℕ => (k : ℝ≥0∞)))
  rw [c1_poisson_mean] at this
  exact this

theorem c1_E_cnt (S : System) (lam : Fin S.I → ℝ≥0) (n : ℕ) (q : ℕ → c1Idx S)
    (hq : ∀ k, (q k).2.1 = n + 1)
    (P : unitInterval → Prop) [DecidablePred P] (hP : MeasurableSet {u | P u})
    (X : Omega S → ℕ) (hX : Measurable X)
    (hdep : ∀ N (U U' : c1Idx S → unitInterval), (∀ p : c1Idx S, p.2.1 ≤ n → U p = U' p) →
      X (N, U) = X (N, U')) :
    ∫⁻ ω, ((((Finset.range (X ω)).filter fun k => P (ω.2 (q k))).card : ℕ) : ℝ≥0∞)
      ∂(sampleMeasure S lam) = volume {u | P u} * ∫⁻ ω, (X ω : ℝ≥0∞) ∂(sampleMeasure S lam) := by
  unfold sampleMeasure
  rw [lintegral_prod (fun ω : Omega S =>
      ((((Finset.range (X ω)).filter fun k => P (ω.2 (q k))).card : ℕ) : ℝ≥0∞))
      (by exact (measurable_from_nat.comp (c1_meas_cnt S q P hP X hX)).aemeasurable),
    lintegral_prod (fun ω : Omega S => (X ω : ℝ≥0∞))
      (by exact (measurable_from_nat.comp hX).aemeasurable),
    ← lintegral_const_mul' _ _ (measure_ne_top _ _)]
  refine lintegral_congr fun N => ?_
  have hx : Measurable[c1MA S n] (fun U => X (N, U)) := by
    have h1 : (fun U => X (N, U)) = (fun U => X (N, U)) ∘ c1proj S n :=
      funext fun U => hdep N U (c1proj S n U) (fun p hp => by simp [c1proj, hp])
    rw [h1]
    exact (hX.comp measurable_prodMk_left).comp (c1_meas_proj S n)
  exact c1_inner S n q hq P hP _ hx

theorem c1_vol_lt (S : System) (hS : Standing S) (i : Fin S.I) (j : Fin (S.J + 1)) :
    volume {u : unitInterval | (u : ℝ) < S.β i j} = ENNReal.ofReal (S.β i j) := by
  have : {u : unitInterval | (u : ℝ) < S.β i j} =
      Set.Iio (⟨S.β i j, hS.β_nonneg i j, hS.β_le_one i j⟩ : unitInterval) := Set.ext fun u => Iff.rfl
  rw [this, unitInterval.volume_Iio]

theorem c1_vol_nlt (S : System) (hS : Standing S) (i : Fin S.I) (j : Fin (S.J + 1)) :
    volume {u : unitInterval | ¬ (u : ℝ) < S.β i j} = ENNReal.ofReal (1 - S.β i j) := by
  have : {u : unitInterval | ¬ (u : ℝ) < S.β i j} = {u : unitInterval | (u : ℝ) < S.β i j}ᶜ := rfl
  rw [this, prob_compl_eq_one_sub (measurableSet_lt measurable_subtype_coe measurable_const),
    c1_vol_lt S hS, ENNReal.ofReal_sub _ (hS.β_nonneg i j), ENNReal.ofReal_one]

theorem c1_meas_succ (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0) (n : ℕ)
    (i : Fin S.I) (s l : ℕ) (j : Fin (S.J + 1)) (t : ℕ) :
    Measurable fun ω : Omega S => (c1Succ S ω.2 t i s l j
      (stateAt S (piStar S sel lam) ω n i s l) : ℝ≥0∞) :=
  measurable_from_nat.comp (c1_meas_cnt S (fun k => (i, t, s, l, j, k))
    (fun u => (u : ℝ) < S.β i j) (measurableSet_lt measurable_subtype_coe measurable_const) _
    (c1_meas_st S sel lam n i s l))

theorem c1_E_succ (S : System) (hS : Standing S) (sel : Selection S) (lam : Fin S.I → ℝ≥0)
    (n : ℕ) (i : Fin S.I) (s l : ℕ) (j : Fin (S.J + 1)) :
    ∫⁻ ω, (c1Succ S ω.2 (n + 1) i s l j (stateAt S (piStar S sel lam) ω n i s l) : ℝ≥0∞)
      ∂(sampleMeasure S lam) =
      ENNReal.ofReal (S.β i j) *
        ∫⁻ ω, (stateAt S (piStar S sel lam) ω n i s l : ℝ≥0∞) ∂(sampleMeasure S lam) := by
  rw [← c1_vol_lt S hS i j]
  exact c1_E_cnt S lam n (fun k => (i, n + 1, s, l, j, k)) (fun k => rfl)
    (fun u => (u : ℝ) < S.β i j) (measurableSet_lt measurable_subtype_coe measurable_const)
    (fun ω => stateAt S (piStar S sel lam) ω n i s l) (c1_meas_st S sel lam n i s l)
    (fun N U U' h => c1_dep S sel lam n N U U' h i s l)

theorem c1_E_fail (S : System) (hS : Standing S) (sel : Selection S) (lam : Fin S.I → ℝ≥0)
    (n : ℕ) (i : Fin S.I) (s l : ℕ) (j : Fin (S.J + 1)) :
    ∫⁻ ω, (c1Fail S ω.2 (n + 1) i s l j (stateAt S (piStar S sel lam) ω n i s l) : ℝ≥0∞)
      ∂(sampleMeasure S lam) =
      ENNReal.ofReal (1 - S.β i j) *
        ∫⁻ ω, (stateAt S (piStar S sel lam) ω n i s l : ℝ≥0∞) ∂(sampleMeasure S lam) := by
  rw [← c1_vol_nlt S hS i j]
  exact c1_E_cnt S lam n (fun k => (i, n + 1, s, l, j, k)) (fun k => rfl)
    (fun u => ¬ (u : ℝ) < S.β i j)
    (measurableSet_lt measurable_subtype_coe measurable_const).compl
    (fun ω => stateAt S (piStar S sel lam) ω n i s l) (c1_meas_st S sel lam n i s l)
    (fun N U U' h => c1_dep S sel lam n N U U' h i s l)

theorem c1_fm (S : System) (hS : Standing S) (sel : Selection S) (lam : Fin S.I → ℝ≥0) :
    ∀ n i s l, ∫⁻ ω, (stateAt S (piStar S sel lam) ω n i s l : ℝ≥0∞) ∂(sampleMeasure S lam) =
      if s < n then (rateX S sel lam i s l : ℝ≥0∞) else 0 := by
  intro n
  induction n with
  | zero => intro i s l; simp [stateAt, history]
  | succ n ih =>
    intro i s l
    by_cases hsn : n + 1 ≤ s
    · rw [if_neg (by omega)]
      have h0 : ∀ ω, stateAt S (piStar S sel lam) ω (n + 1) i s l = 0 :=
        fun ω => c1_st_old S sel lam ω (n + 1) i s l hsn
      simp [h0]
    rw [if_pos (by omega)]
    rcases s with _ | s
    · simp only [c1_st_zero]
      by_cases h1 : S.L i ≤ l
      · simp [h1, rateX]
      by_cases h2 : l = 0
      · subst h2
        simp only [h1, if_false, if_true]
        rw [c1_E_N]; simp [rateX, h1]
      · simp [h1, h2, rateX]
    · simp only [c1_st_succ]
      by_cases h1 : S.L i ≤ l
      · simp [h1, rateX]
      by_cases h2 : l = 0
      · subst h2
        simp only [h1, if_false, if_true, zero_add]
        rw [c1_E_fail S hS, ih i s 0, if_pos (by omega)]
        simp only [rateX, h1, if_false, if_true, zero_add]
        simp only [ENNReal.ofReal, ENNReal.coe_mul]
      · simp only [h1, h2, if_false, Nat.cast_add]
        rw [lintegral_add_left (c1_meas_succ S sel lam n i s (l - 1) _ (n + 1)),
          c1_E_succ S hS, c1_E_fail S hS, ih i s (l - 1), ih i s l]
        have hs : s < n := by omega
        simp only [hs, if_true]
        simp only [rateX, h1, h2, if_false]
        simp only [ENNReal.ofReal, ENNReal.coe_mul, ENNReal.coe_add]

/-! ## Part 6: the time shift preserves the law; on-demand capacity grows along it -/

theorem c1_shift_mp (S : System) (lam : Fin S.I → ℝ≥0) :
    MeasurePreserving (c1shift S) (sampleMeasure S lam) (sampleMeasure S lam) := by
  have h1 : MeasurePreserving (fun (N : Fin S.I × ℕ → ℕ) (p : Fin S.I × ℕ) => N (p.1, p.2 + 1))
      (Measure.infinitePi fun p : Fin S.I × ℕ => poissonMeasure (lam p.1))
      (Measure.infinitePi fun p : Fin S.I × ℕ => poissonMeasure (lam p.1)) := by
    refine ⟨measurable_pi_lambda _ fun p => measurable_pi_apply _, ?_⟩
    exact Measure.map_infinitePi_infinitePi_of_inj
      (f := fun p : Fin S.I × ℕ => (p.1, p.2 + 1))
      (by intro p q h; simp only [Prod.ext_iff, add_left_inj] at h ⊢; exact h)
  have h2 : MeasurePreserving
      (fun (U : c1Idx S → unitInterval) (p : c1Idx S) => U (p.1, p.2.1 + 1, p.2.2))
      (Measure.infinitePi fun _ : c1Idx S => (volume : Measure unitInterval))
      (Measure.infinitePi fun _ : c1Idx S => (volume : Measure unitInterval)) := by
    refine ⟨measurable_pi_lambda _ fun p => measurable_pi_apply _, ?_⟩
    exact Measure.map_infinitePi_infinitePi_of_inj
      (f := fun p : c1Idx S => (p.1, p.2.1 + 1, p.2.2))
      (by intro p q h; simp only [Prod.ext_iff, add_left_inj] at h ⊢; exact h)
  unfold sampleMeasure
  exact h1.prod h2

theorem c1_meas_usage (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0) (n : ℕ)
    (j : Fin S.J) :
    Measurable fun ω : Omega S => usage S sel n (stateAt S (piStar S sel lam) ω n) j := by
  unfold usage
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun l _ =>
    Finset.measurable_sum _ fun s _ => ?_
  exact Measurable.ite (MeasurableSet.const _) (c1_meas_st S sel lam n i s l) measurable_const

theorem c1_m_eq (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0) (n : ℕ)
    (ω : Omega S) (j : Fin S.J) :
    (piStar S sel lam).m n (history S (piStar S sel lam) ω n) j =
      ((usage S sel n (stateAt S (piStar S sel lam) ω n) j : ℕ) : ℝ≥0) - (piStar S sel lam).M j :=
  rfl

theorem c1_meas_m (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0) (n : ℕ)
    (j : Fin S.J) :
    Measurable fun ω : Omega S =>
      ((piStar S sel lam).m n (history S (piStar S sel lam) ω n) j : ℝ≥0∞) := by
  simp only [c1_m_eq]
  exact (measurable_from_nat (f := fun u : ℕ =>
    ((((u : ℝ≥0) - (piStar S sel lam).M j : ℝ≥0)) : ℝ≥0∞))).comp (c1_meas_usage S sel lam n j)

theorem c1_usage_mono (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0) (n : ℕ)
    (ω : Omega S) (j : Fin S.J) :
    usage S sel n (stateAt S (piStar S sel lam) (c1shift S ω) n) j ≤
      usage S sel (n + 1) (stateAt S (piStar S sel lam) ω (n + 1)) j := by
  unfold usage
  apply Finset.sum_le_sum; intro i _
  apply Finset.sum_le_sum; intro l _
  rw [Finset.sum_range_succ]
  refine le_trans (le_of_eq ?_) (Nat.le_add_right _ _)
  apply Finset.sum_congr rfl
  intro s hs
  rw [c1_st_shift S sel lam ω n i s l (Finset.mem_range.1 hs)]

theorem c1_Em_mono (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0) (j : Fin S.J) :
    Monotone fun n => ∫⁻ ω, ((piStar S sel lam).m n (history S (piStar S sel lam) ω n) j : ℝ≥0∞)
      ∂(sampleMeasure S lam) := by
  refine monotone_nat_of_le_succ fun n => ?_
  have hc := (c1_shift_mp S lam).lintegral_comp (c1_meas_m S sel lam n j)
  rw [← hc]
  refine lintegral_mono fun ω => ?_
  simp only [c1_m_eq]
  exact ENNReal.coe_le_coe.2 (tsub_le_tsub_right (by exact_mod_cast c1_usage_mono S sel lam n ω j) _)

/-! ## Part 7: bounds and assembly -/

/-- total expected sojourn of type `i` -/
noncomputable def c1G (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0) (i : Fin S.I) : ℝ≥0∞ :=
  ∑' s, ∑ l ∈ Finset.range (S.L i), (rateX S sel lam i s l : ℝ≥0∞)

theorem c1_E_usage_le (S : System) (hS : Standing S) (sel : Selection S) (lam : Fin S.I → ℝ≥0)
    (n : ℕ) (j : Fin S.J) :
    ∫⁻ ω, (usage S sel n (stateAt S (piStar S sel lam) ω n) j : ℝ≥0∞) ∂(sampleMeasure S lam) ≤
      ∑ i, c1G S sel lam i := by
  have hmx : ∀ (c : Prop) [Decidable c] i s l, Measurable fun ω : Omega S =>
      (if c then (stateAt S (piStar S sel lam) ω n i s l : ℝ≥0∞) else 0) :=
    fun c _ i s l => Measurable.ite (MeasurableSet.const _)
      (measurable_from_nat.comp (c1_meas_st S sel lam n i s l)) measurable_const
  unfold usage
  push_cast
  rw [lintegral_finset_sum _ (fun i _ => Finset.measurable_sum _ fun l _ =>
    Finset.measurable_sum _ fun s _ => hmx _ i s l)]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [lintegral_finset_sum _ (fun l _ => Finset.measurable_sum _ fun s _ => hmx _ i s l)]
  calc ∑ l ∈ Finset.range (S.L i), ∫⁻ ω, ∑ s ∈ Finset.range n,
        (if j.succ = sel.jStar i s l then (stateAt S (piStar S sel lam) ω n i s l : ℝ≥0∞) else 0)
        ∂(sampleMeasure S lam)
      ≤ ∑ l ∈ Finset.range (S.L i), ∑ s ∈ Finset.range n, (rateX S sel lam i s l : ℝ≥0∞) := by
        refine Finset.sum_le_sum fun l _ => ?_
        rw [lintegral_finset_sum _ (fun s _ => hmx _ i s l)]
        refine Finset.sum_le_sum fun s hs => ?_
        calc ∫⁻ ω, (if j.succ = sel.jStar i s l then
              (stateAt S (piStar S sel lam) ω n i s l : ℝ≥0∞) else 0) ∂(sampleMeasure S lam)
            ≤ ∫⁻ ω, (stateAt S (piStar S sel lam) ω n i s l : ℝ≥0∞) ∂(sampleMeasure S lam) :=
              lintegral_mono fun ω => by split_ifs <;> simp
          _ = rateX S sel lam i s l := by
              rw [c1_fm S hS sel lam n i s l, if_pos (Finset.mem_range.1 hs)]
    _ = ∑ s ∈ Finset.range n, ∑ l ∈ Finset.range (S.L i), (rateX S sel lam i s l : ℝ≥0∞) :=
        Finset.sum_comm
    _ ≤ c1G S sel lam i := ENNReal.sum_le_tsum _

theorem c1_E_m_le (S : System) (hS : Standing S) (sel : Selection S) (lam : Fin S.I → ℝ≥0)
    (n : ℕ) (j : Fin S.J) :
    ∫⁻ ω, ((piStar S sel lam).m n (history S (piStar S sel lam) ω n) j : ℝ≥0∞)
      ∂(sampleMeasure S lam) ≤ ∑ i, c1G S sel lam i := by
  refine le_trans (lintegral_mono fun ω => ?_) (c1_E_usage_le S hS sel lam n j)
  simp only [c1_m_eq]
  rw [← ENNReal.coe_natCast]
  exact ENNReal.coe_le_coe.2 tsub_le_self

theorem c1_G_ne_top (S : System) (hS : Standing S) (sel : Selection S) (lam : Fin S.I → ℝ≥0) :
    ∑ i, c1G S sel lam i ≠ ⊤ :=
  (ENNReal.sum_lt_top.2 fun i _ => c1_G_lt_top S hS sel lam i).ne

theorem c1_E_cost_le (S : System) (hS : Standing S) (sel : Selection S) (lam : Fin S.I → ℝ≥0)
    (A B : Fin S.J → ℝ) (n : ℕ) :
    ∫⁻ ω, periodCost S A B (piStar S sel lam) ω n ∂(sampleMeasure S lam) ≤
      ∑ j, (ENNReal.ofReal (A j) * ((piStar S sel lam).M j : ℝ≥0∞) +
        ENNReal.ofReal (B j) * ∑ i, c1G S sel lam i) +
      ∑ i, ENNReal.ofReal (S.W i) * c1G S sel lam i := by
  have : IsProbabilityMeasure (sampleMeasure S lam) := by unfold sampleMeasure; infer_instance
  unfold periodCost
  have hmx : ∀ i s l, Measurable fun ω : Omega S =>
      ENNReal.ofReal (S.W i) * (stateAt S (piStar S sel lam) ω n i s l : ℝ≥0∞) :=
    fun i s l => (measurable_from_nat.comp (c1_meas_st S sel lam n i s l)).const_mul _
  have hmj : ∀ j, Measurable fun ω : Omega S => ENNReal.ofReal (A j) * ((piStar S sel lam).M j : ℝ≥0∞) +
      ENNReal.ofReal (B j) * ((piStar S sel lam).m n (history S (piStar S sel lam) ω n) j : ℝ≥0∞) :=
    fun j => measurable_const.add ((c1_meas_m S sel lam n j).const_mul _)
  rw [lintegral_add_left (Finset.measurable_sum _ fun j _ => hmj j)]
  gcongr
  · rw [lintegral_finset_sum _ (fun j _ => hmj j)]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
      lintegral_const_mul _ (c1_meas_m S sel lam n j)]
    gcongr
    exact c1_E_m_le S hS sel lam n j
  · rw [lintegral_finset_sum _ (fun i _ => Finset.measurable_sum _ fun s _ =>
      Finset.measurable_sum _ fun l _ => hmx i s l)]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [lintegral_finset_sum _ (fun s _ => Finset.measurable_sum _ fun l _ => hmx i s l)]
    calc ∑ s ∈ Finset.Ico (S.δ i) n, ∫⁻ ω, ∑ l ∈ Finset.range (S.L i),
          ENNReal.ofReal (S.W i) * (stateAt S (piStar S sel lam) ω n i s l : ℝ≥0∞)
          ∂(sampleMeasure S lam)
        ≤ ∑ s ∈ Finset.Ico (S.δ i) n, ENNReal.ofReal (S.W i) *
          ∑ l ∈ Finset.range (S.L i), (rateX S sel lam i s l : ℝ≥0∞) := by
          refine Finset.sum_le_sum fun s hs => ?_
          rw [lintegral_finset_sum _ (fun l _ => hmx i s l), Finset.mul_sum]
          refine Finset.sum_le_sum fun l _ => ?_
          rw [lintegral_const_mul (f := fun ω : Omega S =>
              (stateAt S (piStar S sel lam) ω n i s l : ℝ≥0∞)) _
              (by exact measurable_from_nat.comp (c1_meas_st S sel lam n i s l)),
            c1_fm S hS sel lam n i s l, if_pos (Finset.mem_Ico.1 hs).2]
      _ = ENNReal.ofReal (S.W i) * ∑ s ∈ Finset.Ico (S.δ i) n,
          ∑ l ∈ Finset.range (S.L i), (rateX S sel lam i s l : ℝ≥0∞) := by rw [Finset.mul_sum]
      _ ≤ ENNReal.ofReal (S.W i) * c1G S sel lam i := by
          gcongr
          exact ENNReal.sum_le_tsum _

theorem piStar_stable_finite_cost_aux (S : System) (hS : Standing S) (sel : Selection S)
    (lam : Fin S.I → ℝ≥0) (A B : Fin S.J → ℝ) :
    IsStable S lam (piStar S sel lam) ∧ avgCost S A B lam (piStar S sel lam) < ⊤ := by
  have hG := c1_G_ne_top S hS sel lam
  refine ⟨⟨fun j => ?_, fun i s l => ?_⟩, ?_⟩
  · -- on-demand capacity: monotone bounded expectations
    set a : ℕ → ℝ≥0∞ := fun n => ∫⁻ ω, ((piStar S sel lam).m n
      (history S (piStar S sel lam) ω n) j : ℝ≥0∞) ∂(sampleMeasure S lam) with ha
    have hle : ∀ n, a n ≤ ∑ i, c1G S sel lam i := fun n => c1_E_m_le S hS sel lam n j
    have hsup : (⨆ n, a n) ≠ ⊤ := ne_top_of_le_ne_top hG (iSup_le hle)
    have htend : Tendsto a atTop (𝓝 (((⨆ n, a n).toNNReal : ℝ≥0) : ℝ≥0∞)) := by
      rw [ENNReal.coe_toNNReal hsup]
      exact tendsto_atTop_iSup (c1_Em_mono S sel lam j)
    exact ⟨(⨆ n, a n).toNNReal, c1_cesaro a _ htend fun n => ne_top_of_le_ne_top hG (hle n)⟩
  · -- states: eventually constant expectations
    refine ⟨rateX S sel lam i s l, c1_cesaro _ _ ?_ fun n => ?_⟩
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_gt_atTop s] with n hn
      rw [c1_fm S hS sel lam n i s l, if_pos hn]
    · rw [c1_fm S hS sel lam n i s l]; split_ifs <;> simp
  · -- finite cost
    set K := ∑ j, (ENNReal.ofReal (A j) * ((piStar S sel lam).M j : ℝ≥0∞) +
        ENNReal.ofReal (B j) * ∑ i, c1G S sel lam i) +
      ∑ i, ENNReal.ofReal (S.W i) * c1G S sel lam i with hK
    have hKt : K < ⊤ := by
      have hGi : ∀ i, c1G S sel lam i ≠ ⊤ := fun i => (c1_G_lt_top S hS sel lam i).ne
      refine ENNReal.add_lt_top.2 ⟨ENNReal.sum_lt_top.2 fun j _ => ENNReal.add_lt_top.2
        ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.coe_lt_top,
         ENNReal.mul_lt_top ENNReal.ofReal_lt_top hG.lt_top⟩,
        ENNReal.sum_lt_top.2 fun i _ => ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hGi i).lt_top⟩
    refine lt_of_le_of_lt (Filter.liminf_le_of_frequently_le' (x := K) ?_) hKt
    refine Filter.Eventually.frequently ?_
    filter_upwards [eventually_ge_atTop 1] with T hT
    refine ENNReal.div_le_of_le_mul ?_
    calc ∑ n ∈ Finset.range T, ∫⁻ ω, periodCost S A B (piStar S sel lam) ω n ∂(sampleMeasure S lam)
        ≤ ∑ n ∈ Finset.range T, K := Finset.sum_le_sum fun n _ => c1_E_cost_le S hS sel lam A B n
      _ = K * T := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]

theorem c1_main (S : System) (hS : Standing S) (sel : Selection S)
    (lam : Fin S.I → ℝ≥0) :
    IsStable S lam (piStar S sel lam) ∧ avgCost S S.R S.V lam (piStar S sel lam) < ⊤ :=
  piStar_stable_finite_cost_aux S hS sel lam S.R S.V

end CloudCostOpt

open CloudCostOpt in
theorem solution (S : System) (hS : Standing S) (sel : Selection S)
    (lam : Fin S.I → ℝ≥0) (hlam : ∀ i, 0 < lam i)
    (hR : ∀ j, 0 < S.R j) (hRV : ∀ j, S.R j < S.V j) :
    IsStable S lam (piStar S sel lam) ∧ avgCost S S.R S.V lam (piStar S sel lam) < ⊤ := by
  exact CloudCostOpt.c1_main S hS sel lam
