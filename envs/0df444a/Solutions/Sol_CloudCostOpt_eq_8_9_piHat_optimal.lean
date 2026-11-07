-- Prove2me | solution 1 for CloudCostOpt.eq_8_9_piHat_optimal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-06T14:11:52.435815+00:00
-- url     : https://prove2.me/submissions/fb1ea492-ce0f-40e2-857b-67115b89172e

import Mathlib
import Definitions.Def_CloudCostOpt_piHat
import Definitions.Def_CloudCostOpt_piStar
import Definitions.Def_CloudCostOpt_opt
import Definitions.Def_CloudCostOpt_avgCost
import Definitions.Def_CloudCostOpt_IsStable
import Definitions.Def_CloudCostOpt_mu
import Definitions.Def_CloudCostOpt_rateX
import Definitions.Def_CloudCostOpt_Standing
import Definitions.Def_CloudCostOpt_fDP

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


/-! ## Part 8: the policy `π̂`: stability and the closed form (8) of its `ℙ_LB` cost -/

theorem e8_hist (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0) (ω : Omega S) :
    ∀ n, history S (piHat S sel) ω n = history S (piStar S sel lam) ω n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp only [history, ih]; rfl

theorem e8_st (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0) (ω : Omega S) (n : ℕ) :
    stateAt S (piHat S sel) ω n = stateAt S (piStar S sel lam) ω n := by
  simp only [stateAt, e8_hist S sel lam ω n]

theorem e8_m (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0) (ω : Omega S) (n : ℕ)
    (j : Fin S.J) :
    ((piHat S sel).m n (history S (piHat S sel) ω n) j : ℝ≥0∞) =
      (usage S sel n (stateAt S (piStar S sel lam) ω n) j : ℝ≥0∞) := by
  show (((usage S sel n (history S (piHat S sel) ω n (Fin.last n)) j : ℕ) : ℝ≥0) : ℝ≥0∞) = _
  rw [e8_hist S sel lam ω n]
  rfl

theorem e8_rateX_zero (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0) (i : Fin S.I) :
    ∀ s l, s < l → rateX S sel lam i s l = 0 := by
  intro s
  induction s with
  | zero => intro l hl; simp [rateX]; intro _ h; omega
  | succ s ih =>
    intro l hl
    simp only [rateX]
    rw [ih (l - 1) (by omega), ih l (by omega)]
    simp

/-- expected usage of resource `j` in period `n + 1` under `π̂` (= `π*`) -/
theorem e8_Eu (S : System) (hS : Standing S) (sel : Selection S) (lam : Fin S.I → ℝ≥0)
    (n : ℕ) (j : Fin S.J) :
    ∫⁻ ω, (usage S sel n (stateAt S (piStar S sel lam) ω n) j : ℝ≥0∞) ∂(sampleMeasure S lam) =
      ∑ i, ∑ s ∈ Finset.range n, ∑ l ∈ Finset.range (S.L i),
        (if j.succ = sel.jStar i s l then (rateX S sel lam i s l : ℝ≥0∞) else 0) := by
  have hmx : ∀ (c : Prop) [Decidable c] i s l, Measurable fun ω : Omega S =>
      (if c then (stateAt S (piStar S sel lam) ω n i s l : ℝ≥0∞) else 0) :=
    fun c _ i s l => Measurable.ite (MeasurableSet.const _)
      (measurable_from_nat.comp (c1_meas_st S sel lam n i s l)) measurable_const
  unfold usage
  push_cast
  rw [lintegral_finset_sum _ (fun i _ => Finset.measurable_sum _ fun l _ =>
    Finset.measurable_sum _ fun s _ => hmx _ i s l)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lintegral_finset_sum _ (fun l _ => Finset.measurable_sum _ fun s _ => hmx _ i s l)]
  have key : ∀ l, ∫⁻ ω, ∑ s ∈ Finset.range n,
      (if j.succ = sel.jStar i s l then (stateAt S (piStar S sel lam) ω n i s l : ℝ≥0∞) else 0)
      ∂(sampleMeasure S lam) = ∑ s ∈ Finset.range n,
      (if j.succ = sel.jStar i s l then (rateX S sel lam i s l : ℝ≥0∞) else 0) := by
    intro l
    rw [lintegral_finset_sum _ (fun s _ => hmx _ i s l)]
    refine Finset.sum_congr rfl fun s hs => ?_
    split_ifs
    · rw [c1_fm S hS sel lam n i s l, if_pos (Finset.mem_range.1 hs)]
    · simp
  simp only [key]
  exact Finset.sum_comm

theorem e8_mu (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0) (j : Fin S.J) :
    mu S sel lam j = ∑ i, ∑' s, ∑ l ∈ Finset.range (S.L i),
      (if j.succ = sel.jStar i s l then (rateX S sel lam i s l : ℝ≥0∞) else 0) := by
  unfold mu
  refine Finset.sum_congr rfl fun i _ => ?_
  refine (ENNReal.tsum_prod (f := fun s l => if l ≤ s ∧ l < S.L i ∧ sel.jStar i s l = j.succ then
    (rateX S sel lam i s l : ℝ≥0∞) else 0)).trans ?_
  refine tsum_congr fun s => ?_
  rw [tsum_eq_sum (s := Finset.range (S.L i)) (fun l hl => by
    rw [if_neg]; rintro ⟨_, h, _⟩; exact hl (Finset.mem_range.2 h))]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' := Finset.mem_range.1 hl
  by_cases hls : l ≤ s
  · by_cases hj : sel.jStar i s l = j.succ
    · rw [if_pos ⟨hls, hl', hj⟩, if_pos hj.symm]
    · rw [if_neg (fun h => hj h.2.2), if_neg (fun h => hj h.symm)]
  · rw [e8_rateX_zero S sel lam i s l (by omega)]
    simp

theorem e8_mu_le (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0) (j : Fin S.J) :
    mu S sel lam j ≤ ∑ i, c1G S sel lam i := by
  rw [e8_mu]
  refine Finset.sum_le_sum fun i _ => ENNReal.tsum_le_tsum fun s => Finset.sum_le_sum fun l _ => ?_
  split_ifs <;> simp

theorem e8_mu_ne_top (S : System) (hS : Standing S) (sel : Selection S) (lam : Fin S.I → ℝ≥0)
    (j : Fin S.J) : mu S sel lam j ≠ ⊤ :=
  ne_top_of_le_ne_top (c1_G_ne_top S hS sel lam) (e8_mu_le S sel lam j)

theorem e8_Eu_tendsto (S : System) (hS : Standing S) (sel : Selection S) (lam : Fin S.I → ℝ≥0)
    (j : Fin S.J) :
    Tendsto (fun n => ∫⁻ ω, (usage S sel n (stateAt S (piStar S sel lam) ω n) j : ℝ≥0∞)
      ∂(sampleMeasure S lam)) atTop (𝓝 (mu S sel lam j)) := by
  simp only [e8_Eu S hS sel lam, e8_mu S sel lam j]
  exact tendsto_finset_sum _ fun i _ => ENNReal.tendsto_nat_tsum _

theorem e8_Eu_mono (S : System) (hS : Standing S) (sel : Selection S) (lam : Fin S.I → ℝ≥0)
    (j : Fin S.J) :
    Monotone (fun n => ∫⁻ ω, (usage S sel n (stateAt S (piStar S sel lam) ω n) j : ℝ≥0∞)
      ∂(sampleMeasure S lam)) := by
  intro a b hab
  simp only [e8_Eu S hS sel lam]
  exact Finset.sum_le_sum fun i _ =>
    Finset.sum_le_sum_of_subset (Finset.range_mono hab)

/-- the closed form (8) -/
noncomputable def e8CF (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0) : ℝ≥0∞ :=
  ∑ j, ENNReal.ofReal (S.R j) * mu S sel lam j +
    ∑ i, ∑' k : ℕ, ∑ l ∈ Finset.range (S.L i),
      ENNReal.ofReal (S.W i) * (rateX S sel lam i (S.δ i + k) l : ℝ≥0∞)

theorem e8_Ecost (S : System) (hS : Standing S) (sel : Selection S) (lam : Fin S.I → ℝ≥0)
    (n : ℕ) :
    ∫⁻ ω, periodCost S S.R S.R (piHat S sel) ω n ∂(sampleMeasure S lam) =
      ∑ j, ENNReal.ofReal (S.R j) *
        ∫⁻ ω, (usage S sel n (stateAt S (piStar S sel lam) ω n) j : ℝ≥0∞) ∂(sampleMeasure S lam) +
      ∑ i, ∑ k ∈ Finset.range (n - S.δ i), ∑ l ∈ Finset.range (S.L i),
        ENNReal.ofReal (S.W i) * (rateX S sel lam i (S.δ i + k) l : ℝ≥0∞) := by
  have hmu : ∀ j, Measurable fun ω : Omega S =>
      (usage S sel n (stateAt S (piStar S sel lam) ω n) j : ℝ≥0∞) :=
    fun j => measurable_from_nat.comp (c1_meas_usage S sel lam n j)
  have hmx : ∀ i s l, Measurable fun ω : Omega S =>
      ENNReal.ofReal (S.W i) * (stateAt S (piStar S sel lam) ω n i s l : ℝ≥0∞) :=
    fun i s l => (measurable_from_nat.comp (c1_meas_st S sel lam n i s l)).const_mul _
  have hpc : ∀ ω, periodCost S S.R S.R (piHat S sel) ω n =
      ∑ j, ENNReal.ofReal (S.R j) * (usage S sel n (stateAt S (piStar S sel lam) ω n) j : ℝ≥0∞) +
      ∑ i, ∑ s ∈ Finset.Ico (S.δ i) n, ∑ l ∈ Finset.range (S.L i),
        ENNReal.ofReal (S.W i) * (stateAt S (piStar S sel lam) ω n i s l : ℝ≥0∞) := by
    intro ω
    unfold periodCost
    rw [e8_st S sel lam ω n]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [e8_m S sel lam ω n j]
    simp [piHat]
  rw [lintegral_congr hpc, lintegral_add_left (Finset.measurable_sum _ fun j _ => (hmu j).const_mul _),
    lintegral_finset_sum _ (fun j _ => (hmu j).const_mul _),
    lintegral_finset_sum _ (fun i _ => Finset.measurable_sum _ fun s _ =>
      Finset.measurable_sum _ fun l _ => hmx i s l)]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [lintegral_const_mul _ (hmu j)]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [lintegral_finset_sum _ (fun s _ => Finset.measurable_sum _ fun l _ => hmx i s l),
      Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [lintegral_finset_sum _ (fun l _ => hmx i _ l)]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [lintegral_const_mul (f := fun ω : Omega S =>
        (stateAt S (piStar S sel lam) ω n i (S.δ i + k) l : ℝ≥0∞)) _
        (by exact measurable_from_nat.comp (c1_meas_st S sel lam n i _ l)),
      c1_fm S hS sel lam n i _ l, if_pos (by have := Finset.mem_range.1 hk; omega)]

theorem e8_Ecost_tendsto (S : System) (hS : Standing S) (sel : Selection S)
    (lam : Fin S.I → ℝ≥0) :
    Tendsto (fun n => ∫⁻ ω, periodCost S S.R S.R (piHat S sel) ω n ∂(sampleMeasure S lam))
      atTop (𝓝 (e8CF S sel lam)) := by
  simp only [e8_Ecost S hS sel lam]
  refine Tendsto.add (tendsto_finset_sum _ fun j _ =>
    ENNReal.Tendsto.const_mul (e8_Eu_tendsto S hS sel lam j) (Or.inr ENNReal.ofReal_ne_top))
    (tendsto_finset_sum _ fun i _ => ?_)
  exact (ENNReal.tendsto_nat_tsum _).comp (tendsto_sub_atTop_nat (S.δ i))

theorem e8_Ecost_mono (S : System) (hS : Standing S) (sel : Selection S)
    (lam : Fin S.I → ℝ≥0) :
    Monotone (fun n => ∫⁻ ω, periodCost S S.R S.R (piHat S sel) ω n ∂(sampleMeasure S lam)) := by
  intro a b hab
  simp only [e8_Ecost S hS sel lam]
  refine add_le_add (Finset.sum_le_sum fun j _ => mul_le_mul_right (by exact e8_Eu_mono S hS sel lam j hab) _)
    (Finset.sum_le_sum fun i _ => Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.sub_le_sub_right hab _)))

theorem e8_CF_ne_top (S : System) (hS : Standing S) (sel : Selection S) (lam : Fin S.I → ℝ≥0) :
    e8CF S sel lam ≠ ⊤ := by
  unfold e8CF
  refine ENNReal.add_ne_top.2 ⟨ENNReal.sum_ne_top.2 fun j _ =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (e8_mu_ne_top S hS sel lam j),
    ENNReal.sum_ne_top.2 fun i _ => ?_⟩
  have h1 : ∑' k : ℕ, ∑ l ∈ Finset.range (S.L i),
      ENNReal.ofReal (S.W i) * (rateX S sel lam i (S.δ i + k) l : ℝ≥0∞) ≤
      ENNReal.ofReal (S.W i) * c1G S sel lam i := by
    simp only [← Finset.mul_sum, ENNReal.tsum_mul_left]
    gcongr
    exact ENNReal.tsum_comp_le_tsum_of_injective (add_right_injective (S.δ i))
      (fun s => ∑ l ∈ Finset.range (S.L i), (rateX S sel lam i s l : ℝ≥0∞))
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (c1_G_lt_top S hS sel lam i).ne) h1

theorem e8_avgCost (S : System) (hS : Standing S) (sel : Selection S) (lam : Fin S.I → ℝ≥0) :
    avgCost S S.R S.R lam (piHat S sel) = e8CF S sel lam := by
  have hfin := e8_CF_ne_top S hS sel lam
  have ht := e8_Ecost_tendsto S hS sel lam
  have hle : ∀ n, ∫⁻ ω, periodCost S S.R S.R (piHat S sel) ω n ∂(sampleMeasure S lam) ≤
      e8CF S sel lam := fun n => (e8_Ecost_mono S hS sel lam).ge_of_tendsto ht n
  rw [← ENNReal.coe_toNNReal hfin] at ht ⊢
  exact (c1_cesaro _ _ ht fun n => ne_top_of_le_ne_top hfin (hle n)).liminf_eq

theorem e8_stable (S : System) (hS : Standing S) (sel : Selection S) (lam : Fin S.I → ℝ≥0) :
    IsStable S lam (piHat S sel) := by
  refine ⟨fun j => ?_, fun i s l => ?_⟩
  · have hfin := e8_mu_ne_top S hS sel lam j
    have ht := e8_Eu_tendsto S hS sel lam j
    have hle : ∀ n, ∫⁻ ω, (usage S sel n (stateAt S (piStar S sel lam) ω n) j : ℝ≥0∞)
        ∂(sampleMeasure S lam) ≤ mu S sel lam j :=
      fun n => (e8_Eu_mono S hS sel lam j).ge_of_tendsto ht n
    rw [← ENNReal.coe_toNNReal hfin] at ht
    refine ⟨(mu S sel lam j).toNNReal, ?_⟩
    simp only [e8_m S sel lam]
    exact c1_cesaro _ _ ht fun n => ne_top_of_le_ne_top hfin (hle n)
  · obtain ⟨c, hc⟩ := (c1_main S hS sel lam).1.2 i s l
    refine ⟨c, ?_⟩
    simp only [e8_st S sel lam]
    exact hc

/-- (8)-(9) from the lower bound `LB ≥ (8)` for every policy -/
theorem e8_of_lb (S : System) (hS : Standing S) (sel : Selection S) (lam : Fin S.I → ℝ≥0)
    (hLB : ∀ π : Policy S, e8CF S sel lam ≤ avgCost S S.R S.R lam π) :
    IsStable S lam (piHat S sel) ∧
    avgCost S S.R S.R lam (piHat S sel) =
      ∑ j, ENNReal.ofReal (S.R j) * mu S sel lam j +
      ∑ i, ∑' k : ℕ, ∑ l ∈ Finset.range (S.L i),
        ENNReal.ofReal (S.W i) * (rateX S sel lam i (S.δ i + k) l : ℝ≥0∞) ∧
    opt S S.R S.R lam = avgCost S S.R S.R lam (piHat S sel) := by
  have hst := e8_stable S hS sel lam
  have hav := e8_avgCost S hS sel lam
  refine ⟨hst, hav, le_antisymm (iInf₂_le _ hst) ?_⟩
  rw [hav]
  exact le_iInf₂ fun π _ => hLB π

/-! ## Part 9: the dynamic program `fᵢ` (deterministic) -/

theorem d1_resCost_nonneg (S : System) (hS : Standing S) (j : Fin (S.J + 1)) :
    0 ≤ resCost S j := by
  cases j using Fin.cases with
  | zero => simp [resCost]
  | succ j => simpa [resCost] using hS.R_nonneg j

theorem d1_resCost_zero (S : System) : resCost S 0 = 0 := by simp [resCost]

theorem d1_resCost_succ (S : System) (j : Fin S.J) : resCost S j.succ = S.R j := by
  simp [resCost]

theorem d1_lr_le (S : System) (i : Fin S.I) (j : Fin (S.J + 1)) (hj : 0 < S.β i j) :
    lateRatio S i ≤ (resCost S j + S.W i) / S.β i j :=
  ciInf_le (Set.finite_range _).bddBelow (⟨j, hj⟩ : {j : Fin (S.J + 1) // 0 < S.β i j})

theorem d1_lr_eq (S : System) (sel : Selection S) (i : Fin S.I) :
    lateRatio S i = (resCost S (sel.jLate i) + S.W i) / S.β i (sel.jLate i) := by
  haveI : Nonempty {j : Fin (S.J + 1) // 0 < S.β i j} := ⟨⟨sel.jLate i, sel.jLate_pos i⟩⟩
  exact le_antisymm (d1_lr_le S i _ (sel.jLate_pos i))
    (le_ciInf fun j => sel.jLate_min i j j.2)

theorem d1_lr_nonneg (S : System) (hS : Standing S) (sel : Selection S) (i : Fin S.I) :
    0 ≤ lateRatio S i := by
  rw [d1_lr_eq S sel i]
  exact div_nonneg (add_nonneg (d1_resCost_nonneg S hS _) (hS.W_pos i).le) (hS.β_nonneg _ _)

theorem d1_go_ge (S : System) (i : Fin S.I) (k l : ℕ) (hl : S.L i ≤ l) :
    fDPToGo S i k l = 0 := by
  cases k with
  | zero => simp [fDPToGo, not_lt.2 hl]
  | succ k => simp [fDPToGo, hl]

theorem d1_go_term_le (S : System) (i : Fin S.I) (k l : ℕ) (hl : l < S.L i)
    (j : Fin (S.J + 1)) :
    fDPToGo S i (k + 1) l ≤
      resCost S j + S.β i j * fDPToGo S i k (l + 1) + (1 - S.β i j) * fDPToGo S i k l := by
  rw [fDPToGo, if_neg (not_le.2 hl)]
  exact ciInf_le (Set.finite_range _).bddBelow j

theorem d1_go_nonneg (S : System) (hS : Standing S) (sel : Selection S) (i : Fin S.I) :
    ∀ k l, 0 ≤ fDPToGo S i k l := by
  intro k
  induction k with
  | zero =>
    intro l
    simp only [fDPToGo]
    split_ifs with h
    · have : (l : ℝ) < S.L i := by exact_mod_cast h
      exact mul_nonneg (by linarith) (d1_lr_nonneg S hS sel i)
    · exact le_rfl
  | succ k ih =>
    intro l
    rw [fDPToGo]
    split_ifs with h
    · exact le_rfl
    · exact le_ciInf fun j => add_nonneg (add_nonneg (d1_resCost_nonneg S hS j)
        (mul_nonneg (hS.β_nonneg i j) (ih _)))
        (mul_nonneg (by linarith [hS.β_le_one i j]) (ih _))

theorem d1_go_succ_le (S : System) (hS : Standing S) (i : Fin S.I) (k l : ℕ) :
    fDPToGo S i (k + 1) l ≤ fDPToGo S i k l := by
  by_cases hl : l < S.L i
  · refine (d1_go_term_le S i k l hl 0).trans (le_of_eq ?_)
    rw [d1_resCost_zero, hS.β_idle]; ring
  · rw [d1_go_ge S i _ l (not_lt.1 hl), d1_go_ge S i _ l (not_lt.1 hl)]

theorem d1_go_le (S : System) (hS : Standing S) (i : Fin S.I) (l : ℕ) :
    ∀ k, fDPToGo S i k l ≤ fDPToGo S i 0 l := by
  intro k
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact (d1_go_succ_le S hS i k l).trans ih

/-- the uniform bound `Kᵢ = Lᵢ · min_j (R_j + Wᵢ)/β_{i,j}` -/
noncomputable def d1K (S : System) (i : Fin S.I) : ℝ := (S.L i : ℝ) * lateRatio S i

theorem d1_f_nonneg (S : System) (hS : Standing S) (sel : Selection S) (i : Fin S.I)
    (s l : ℕ) : 0 ≤ fDP S i s l := d1_go_nonneg S hS sel i _ _

theorem d1_f_le (S : System) (hS : Standing S) (sel : Selection S) (i : Fin S.I) (s l : ℕ) :
    fDP S i s l ≤ d1K S i := by
  refine (d1_go_le S hS i l _).trans ?_
  have hr := d1_lr_nonneg S hS sel i
  simp only [fDPToGo, d1K]
  split_ifs
  · have : (0 : ℝ) ≤ l := Nat.cast_nonneg l
    nlinarith
  · exact mul_nonneg (Nat.cast_nonneg _) hr

theorem d1_f_ge (S : System) (i : Fin S.I) (s l : ℕ) (hl : S.L i ≤ l) : fDP S i s l = 0 :=
  d1_go_ge S i _ l hl

theorem d1_late (S : System) (i : Fin S.I) (s l : ℕ) (hs : S.δ i ≤ s) :
    fDP S i s l = if l < S.L i then ((S.L i : ℝ) - l) * lateRatio S i else 0 := by
  simp only [fDP, Nat.sub_eq_zero_of_le hs, fDPToGo]

/-- Bellman inequality of `fᵢ`, early and late, for every resource `j` -/
theorem d1_bell_le (S : System) (hS : Standing S) (sel : Selection S) (i : Fin S.I)
    (s l : ℕ) (hl : l < S.L i) (j : Fin (S.J + 1)) :
    fDP S i s l ≤ resCost S j + (if S.δ i ≤ s then S.W i else 0) +
      S.β i j * fDP S i (s + 1) (l + 1) + (1 - S.β i j) * fDP S i (s + 1) l := by
  by_cases hs : s < S.δ i
  · obtain ⟨k, hk⟩ : ∃ k, S.δ i - s = k + 1 := ⟨S.δ i - s - 1, by omega⟩
    have hk' : S.δ i - (s + 1) = k := by omega
    rw [if_neg (by omega), add_zero]
    simp only [fDP, hk, hk']
    exact d1_go_term_le S i k l hl j
  · rw [if_pos (by omega), d1_late S i s l (by omega), d1_late S i (s + 1) l (by omega),
      d1_late S i (s + 1) (l + 1) (by omega), if_pos hl]
    have hr := d1_lr_nonneg S hS sel i
    have hβ0 := hS.β_nonneg i j
    have hβr : S.β i j * lateRatio S i ≤ resCost S j + S.W i := by
      rcases hβ0.lt_or_eq with hp | hz
      · have := d1_lr_le S i j hp
        rw [le_div_iff₀ hp] at this; linarith
      · rw [← hz, zero_mul]; exact add_nonneg (d1_resCost_nonneg S hS j) (hS.W_pos i).le
    have e2 : (if l + 1 < S.L i then ((S.L i : ℝ) - ((l + 1 : ℕ) : ℝ)) * lateRatio S i else 0) =
        ((S.L i : ℝ) - l - 1) * lateRatio S i := by
      split_ifs with h
      · push_cast; ring
      · have : S.L i = l + 1 := by omega
        rw [this]; push_cast; ring
    rw [e2]
    linarith

/-- the selected resource `j*` attains the Bellman minimum -/
theorem d1_bell_eq (S : System) (hS : Standing S) (sel : Selection S) (i : Fin S.I)
    (s l : ℕ) (hl : l < S.L i) :
    fDP S i s l = resCost S (sel.jStar i s l) + (if S.δ i ≤ s then S.W i else 0) +
      S.β i (sel.jStar i s l) * fDP S i (s + 1) (l + 1) +
      (1 - S.β i (sel.jStar i s l)) * fDP S i (s + 1) l := by
  refine le_antisymm (d1_bell_le S hS sel i s l hl _) ?_
  by_cases hs : s < S.δ i
  · rw [Selection.jStar, if_pos hs, if_neg (by omega), add_zero]
    have hinf : fDP S i s l = ⨅ j : Fin (S.J + 1), (resCost S j +
        S.β i j * fDP S i (s + 1) (l + 1) + (1 - S.β i j) * fDP S i (s + 1) l) := by
      obtain ⟨k, hk⟩ : ∃ k, S.δ i - s = k + 1 := ⟨S.δ i - s - 1, by omega⟩
      have hk' : S.δ i - (s + 1) = k := by omega
      simp only [fDP, hk, hk']
      rw [fDPToGo, if_neg (not_le.2 hl)]
    rw [hinf]
    exact le_ciInf fun j => sel.jEarly_min i s l j hs hl
  · rw [Selection.jStar, if_neg hs, if_pos (by omega), d1_late S i s l (by omega),
      d1_late S i (s + 1) l (by omega), d1_late S i (s + 1) (l + 1) (by omega), if_pos hl]
    have hβ := sel.jLate_pos i
    have hr : lateRatio S i * S.β i (sel.jLate i) = resCost S (sel.jLate i) + S.W i := by
      rw [d1_lr_eq S sel i, div_mul_cancel₀ _ hβ.ne']
    have e2 : (if l + 1 < S.L i then ((S.L i : ℝ) - ((l + 1 : ℕ) : ℝ)) * lateRatio S i else 0) =
        ((S.L i : ℝ) - l - 1) * lateRatio S i := by
      split_ifs with h
      · push_cast; ring
      · have : S.L i = l + 1 := by omega
        rw [this]; push_cast; ring
    rw [e2]
    linarith

/-- per-order cost of cell `(s, l)` under `j*` -/
noncomputable def d1c (S : System) (sel : Selection S) (i : Fin S.I) (s l : ℕ) : ℝ :=
  resCost S (sel.jStar i s l) + (if S.δ i ≤ s then S.W i else 0)

theorem d1_flow_step (S : System) (hS : Standing S) (sel : Selection S) (lam : Fin S.I → ℝ≥0)
    (i : Fin S.I) (n : ℕ) :
    ∑ l ∈ Finset.range (S.L i), (rateX S sel lam i n l : ℝ) * fDP S i n l =
      ∑ l ∈ Finset.range (S.L i), (rateX S sel lam i n l : ℝ) * d1c S sel i n l +
      ∑ l ∈ Finset.range (S.L i), (rateX S sel lam i (n + 1) l : ℝ) * fDP S i (n + 1) l := by
  obtain ⟨K, hK⟩ : ∃ K, S.L i = K + 1 := ⟨S.L i - 1, by have := hS.one_le_L i; omega⟩
  have hb : ∀ l ∈ Finset.range (S.L i), (rateX S sel lam i n l : ℝ) * fDP S i n l =
      (rateX S sel lam i n l : ℝ) * d1c S sel i n l +
      S.β i (sel.jStar i n l) * (rateX S sel lam i n l : ℝ) * fDP S i (n + 1) (l + 1) +
      (1 - S.β i (sel.jStar i n l)) * (rateX S sel lam i n l : ℝ) * fDP S i (n + 1) l := by
    intro l hl
    rw [d1_bell_eq S hS sel i n l (Finset.mem_range.1 hl), d1c]; ring
  have hs : ∀ l ∈ Finset.range (S.L i), (rateX S sel lam i (n + 1) l : ℝ) * fDP S i (n + 1) l =
      (if l = 0 then 0 else S.β i (sel.jStar i n (l - 1)) * rateX S sel lam i n (l - 1)) *
        fDP S i (n + 1) l +
      (1 - S.β i (sel.jStar i n l)) * (rateX S sel lam i n l : ℝ) * fDP S i (n + 1) l := by
    intro l hl
    rw [c1_rateX_succ S hS sel lam i n l (Finset.mem_range.1 hl)]; ring
  rw [Finset.sum_congr rfl hb, Finset.sum_congr rfl hs]
  simp only [Finset.sum_add_distrib]
  have hshift : ∑ l ∈ Finset.range (S.L i),
      S.β i (sel.jStar i n l) * (rateX S sel lam i n l : ℝ) * fDP S i (n + 1) (l + 1) =
      ∑ l ∈ Finset.range (S.L i),
      (if l = 0 then 0 else S.β i (sel.jStar i n (l - 1)) * rateX S sel lam i n (l - 1)) *
        fDP S i (n + 1) l := by
    have hg : fDP S i (n + 1) (K + 1) = 0 := d1_f_ge S i _ _ (by omega)
    rw [hK, Finset.sum_range_succ, Finset.sum_range_succ', hg]
    simp
  rw [hshift]; ring

theorem d1_flow (S : System) (hS : Standing S) (sel : Selection S) (lam : Fin S.I → ℝ≥0)
    (i : Fin S.I) : ∀ n, (lam i : ℝ) * fDP S i 0 0 =
      ∑ s ∈ Finset.range n, ∑ l ∈ Finset.range (S.L i),
        (rateX S sel lam i s l : ℝ) * d1c S sel i s l +
      ∑ l ∈ Finset.range (S.L i), (rateX S sel lam i n l : ℝ) * fDP S i n l := by
  intro n
  induction n with
  | zero =>
    obtain ⟨K, hK⟩ : ∃ K, S.L i = K + 1 := ⟨S.L i - 1, by have := hS.one_le_L i; omega⟩
    rw [Finset.sum_range_zero, zero_add, hK, Finset.sum_range_succ']
    have h0 : ∀ l, (rateX S sel lam i 0 (l + 1) : ℝ) = 0 := by intro l; simp [rateX]
    simp [h0, rateX, hK]
  | succ n ih => rw [ih, d1_flow_step S hS sel lam i n, Finset.sum_range_succ]; ring

/-- the partial cost sums of `π̂` are at most `Σᵢ λᵢ fᵢ(0, 0)` -/
theorem d1_partial_le (S : System) (hS : Standing S) (sel : Selection S)
    (lam : Fin S.I → ℝ≥0) (n : ℕ) :
    ∑ j, ENNReal.ofReal (S.R j) * ∑ i, ∑ s ∈ Finset.range n, ∑ l ∈ Finset.range (S.L i),
        (if j.succ = sel.jStar i s l then (rateX S sel lam i s l : ℝ≥0∞) else 0) +
      ∑ i, ∑ k ∈ Finset.range (n - S.δ i), ∑ l ∈ Finset.range (S.L i),
        ENNReal.ofReal (S.W i) * (rateX S sel lam i (S.δ i + k) l : ℝ≥0∞) ≤
      ∑ i, ENNReal.ofReal ((lam i : ℝ) * fDP S i 0 0) := by
  have hj : ∀ i s l, ∑ j : Fin S.J, ENNReal.ofReal (S.R j) *
      (if j.succ = sel.jStar i s l then (rateX S sel lam i s l : ℝ≥0∞) else 0) =
      ENNReal.ofReal (resCost S (sel.jStar i s l)) * (rateX S sel lam i s l : ℝ≥0∞) := by
    intro i s l
    cases h : sel.jStar i s l using Fin.cases with
    | zero => simp [d1_resCost_zero, Fin.succ_ne_zero]
    | succ j0 =>
      simp only [Fin.succ_inj, mul_ite, mul_zero, d1_resCost_succ]
      rw [Finset.sum_ite_eq' Finset.univ j0]
      simp
  have h1 : ∑ j, ENNReal.ofReal (S.R j) * ∑ i, ∑ s ∈ Finset.range n, ∑ l ∈ Finset.range (S.L i),
      (if j.succ = sel.jStar i s l then (rateX S sel lam i s l : ℝ≥0∞) else 0) =
      ∑ i, ∑ s ∈ Finset.range n, ∑ l ∈ Finset.range (S.L i),
      ENNReal.ofReal (resCost S (sel.jStar i s l)) * (rateX S sel lam i s l : ℝ≥0∞) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => hj i s l
  have h2 : ∀ i, ∑ k ∈ Finset.range (n - S.δ i), ∑ l ∈ Finset.range (S.L i),
      ENNReal.ofReal (S.W i) * (rateX S sel lam i (S.δ i + k) l : ℝ≥0∞) =
      ∑ s ∈ Finset.range n, ∑ l ∈ Finset.range (S.L i),
      (if S.δ i ≤ s then ENNReal.ofReal (S.W i) * (rateX S sel lam i s l : ℝ≥0∞) else 0) := by
    intro i
    symm
    have hi : ∀ s, ∑ l ∈ Finset.range (S.L i),
        (if S.δ i ≤ s then ENNReal.ofReal (S.W i) * (rateX S sel lam i s l : ℝ≥0∞) else 0) =
        if S.δ i ≤ s then ∑ l ∈ Finset.range (S.L i),
          ENNReal.ofReal (S.W i) * (rateX S sel lam i s l : ℝ≥0∞) else 0 := fun s => by
      split_ifs <;> simp
    have hf : (Finset.range n).filter (fun s => S.δ i ≤ s) = Finset.Ico (S.δ i) n := by
      ext s; simp only [Finset.mem_Ico, Finset.mem_filter, Finset.mem_range]; omega
    simp only [hi]
    rw [← Finset.sum_filter, hf, Finset.sum_Ico_eq_sum_range]
  rw [h1, Finset.sum_congr rfl fun i _ => h2 i, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  have hc : ∀ s l, ENNReal.ofReal (resCost S (sel.jStar i s l)) * (rateX S sel lam i s l : ℝ≥0∞) +
      (if S.δ i ≤ s then ENNReal.ofReal (S.W i) * (rateX S sel lam i s l : ℝ≥0∞) else 0) =
      ENNReal.ofReal ((rateX S sel lam i s l : ℝ) * d1c S sel i s l) := by
    intro s l
    have hR := d1_resCost_nonneg S hS (sel.jStar i s l)
    have hW := (hS.W_pos i).le
    rw [ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal, d1c]
    split_ifs
    · rw [ENNReal.ofReal_add hR hW]; ring
    · rw [add_zero, add_zero, mul_comm]
  simp only [← Finset.sum_add_distrib, hc]
  have hnn : ∀ s l, 0 ≤ (rateX S sel lam i s l : ℝ) * d1c S sel i s l := fun s l =>
    mul_nonneg (NNReal.coe_nonneg _) (add_nonneg (d1_resCost_nonneg S hS _)
      (by split_ifs <;> linarith [hS.W_pos i]))
  calc ∑ s ∈ Finset.range n, ∑ l ∈ Finset.range (S.L i),
        ENNReal.ofReal ((rateX S sel lam i s l : ℝ) * d1c S sel i s l)
      = ENNReal.ofReal (∑ s ∈ Finset.range n, ∑ l ∈ Finset.range (S.L i),
        (rateX S sel lam i s l : ℝ) * d1c S sel i s l) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun s _ => Finset.sum_nonneg fun l _ => hnn s l)]
        exact Finset.sum_congr rfl fun s _ =>
          (ENNReal.ofReal_sum_of_nonneg fun l _ => hnn s l).symm
    _ ≤ ENNReal.ofReal ((lam i : ℝ) * fDP S i 0 0) := by
        apply ENNReal.ofReal_le_ofReal
        rw [d1_flow S hS sel lam i n]
        have : 0 ≤ ∑ l ∈ Finset.range (S.L i), (rateX S sel lam i n l : ℝ) * fDP S i n l :=
          Finset.sum_nonneg fun l _ => mul_nonneg (NNReal.coe_nonneg _) (d1_f_nonneg S hS sel i _ _)
        linarith


/-- the closed form (8) is at most `Λ = Σᵢ λᵢ fᵢ(0, 0)` -/
theorem e9_CF_le (S : System) (hS : Standing S) (sel : Selection S) (lam : Fin S.I → ℝ≥0) :
    e8CF S sel lam ≤ ∑ i, ENNReal.ofReal ((lam i : ℝ) * fDP S i 0 0) := by
  refine le_of_tendsto' (e8_Ecost_tendsto S hS sel lam) fun n => ?_
  rw [e8_Ecost S hS sel lam n]
  simp only [e8_Eu S hS sel lam n]
  exact d1_partial_le S hS sel lam n

/-! ## Part 10: pathwise dynamics of an arbitrary policy -/

theorem g_st_zero (S : System) (π : Policy S) (ω : Omega S) (n : ℕ) (i : Fin S.I) (l : ℕ) :
    stateAt S π ω (n + 1) i 0 l =
      if S.L i ≤ l then 0 else if l = 0 then ω.1 (i, n + 1) else 0 := by
  simp only [stateAt, history, Fin.snoc_last]

theorem g_st_succ (S : System) (π : Policy S) (ω : Omega S) (n : ℕ) (i : Fin S.I) (s l : ℕ) :
    stateAt S π ω (n + 1) i (s + 1) l = if S.L i ≤ l then 0 else
      (if l = 0 then 0 else
        cellSucc S ω.2 (n + 1) i s (l - 1) (π.a n (history S π ω n) i s (l - 1))) +
      cellFail S ω.2 (n + 1) i s l (π.a n (history S π ω n) i s l) := by
  simp only [stateAt, history, Fin.snoc_last]

theorem g_succ_le (S : System) (U : Fin S.I × ℕ × ℕ × ℕ × Fin (S.J + 1) × ℕ → unitInterval)
    (t : ℕ) (i : Fin S.I) (s l : ℕ) (a : Fin (S.J + 1) → ℕ) :
    cellSucc S U t i s l a ≤ ∑ j, a j := by
  unfold cellSucc
  exact Finset.sum_le_sum fun j _ => (Finset.card_filter_le _ _).trans (Finset.card_range _).le

theorem g_succ_fail (S : System) (U : Fin S.I × ℕ × ℕ × ℕ × Fin (S.J + 1) × ℕ → unitInterval)
    (t : ℕ) (i : Fin S.I) (s l : ℕ) (a : Fin (S.J + 1) → ℕ) :
    cellSucc S U t i s l a + cellFail S U t i s l a = ∑ j, a j := by
  have := g_succ_le S U t i s l a
  unfold cellFail; omega

theorem g_assign (S : System) (π : Policy S) (ω : Omega S) (n : ℕ) (i : Fin S.I) (s l : ℕ)
    (hl : l < S.L i) : ∑ j, π.a n (history S π ω n) i s l j = stateAt S π ω n i s l :=
  π.assign_sum n (history S π ω n) i s l hl

theorem g_st_old (S : System) (π : Policy S) (ω : Omega S) :
    ∀ n i s l, n ≤ s → stateAt S π ω n i s l = 0 := by
  intro n
  induction n with
  | zero => intro i s l _; simp [stateAt, history]
  | succ n ih =>
    intro i s l hs
    obtain ⟨s, rfl⟩ : ∃ s0, s = s0 + 1 := ⟨s - 1, by omega⟩
    rw [g_st_succ]
    split_ifs with hL h0
    · rfl
    · have h2 := g_succ_fail S ω.2 (n + 1) i s l (π.a n (history S π ω n) i s l)
      rw [g_assign S π ω n i s l (by omega), ih i s l (by omega)] at h2
      omega
    · have h1 := g_succ_fail S ω.2 (n + 1) i s (l - 1) (π.a n (history S π ω n) i s (l - 1))
      have h2 := g_succ_fail S ω.2 (n + 1) i s l (π.a n (history S π ω n) i s l)
      rw [g_assign S π ω n i s l (by omega), ih i s l (by omega)] at h2
      rw [g_assign S π ω n i s (l - 1) (by omega), ih i s (l - 1) (by omega)] at h1
      omega

theorem g_st_ge (S : System) (π : Policy S) (ω : Omega S) (n : ℕ) (i : Fin S.I) (s l : ℕ)
    (hl : S.L i ≤ l) : stateAt S π ω n i s l = 0 := by
  cases n with
  | zero => simp [stateAt, history]
  | succ n =>
    cases s with
    | zero => rw [g_st_zero, if_pos hl]
    | succ s => rw [g_st_succ, if_pos hl]

/-- cohort conservation: orders only leave -/
theorem g_cons (S : System) (hS : Standing S) (π : Policy S) (ω : Omega S) (n : ℕ)
    (i : Fin S.I) (s : ℕ) :
    ∑ l ∈ Finset.range (S.L i), stateAt S π ω (n + 1) i (s + 1) l ≤
      ∑ l ∈ Finset.range (S.L i), stateAt S π ω n i s l := by
  obtain ⟨K, hK⟩ : ∃ K, S.L i = K + 1 := ⟨S.L i - 1, by have := hS.one_le_L i; omega⟩
  have hX : ∀ l ∈ Finset.range (S.L i), stateAt S π ω n i s l =
      cellSucc S ω.2 (n + 1) i s l (π.a n (history S π ω n) i s l) +
      cellFail S ω.2 (n + 1) i s l (π.a n (history S π ω n) i s l) := by
    intro l hl
    rw [g_succ_fail, g_assign S π ω n i s l (Finset.mem_range.1 hl)]
  have hY : ∀ l ∈ Finset.range (S.L i), stateAt S π ω (n + 1) i (s + 1) l =
      (if l = 0 then 0 else
        cellSucc S ω.2 (n + 1) i s (l - 1) (π.a n (history S π ω n) i s (l - 1))) +
      cellFail S ω.2 (n + 1) i s l (π.a n (history S π ω n) i s l) := by
    intro l hl
    rw [g_st_succ, if_neg (by have := Finset.mem_range.1 hl; omega)]
  rw [Finset.sum_congr rfl hY, Finset.sum_congr rfl hX, Finset.sum_add_distrib,
    Finset.sum_add_distrib, hK, Finset.sum_range_succ' (fun l => if l = 0 then 0 else
      cellSucc S ω.2 (n + 1) i s (l - 1) (π.a n (history S π ω n) i s (l - 1))),
    Finset.sum_range_succ (fun l => cellSucc S ω.2 (n + 1) i s l (π.a n (history S π ω n) i s l))]
  simp only [Nat.add_one_ne_zero, if_false, if_true, Nat.add_sub_cancel]
  omega

/-- a cohort never exceeds its arrivals -/
theorem g_cohort_le (S : System) (hS : Standing S) (π : Policy S) (ω : Omega S) (i : Fin S.I) :
    ∀ s n, s < n → ∑ l ∈ Finset.range (S.L i), stateAt S π ω n i s l ≤ ω.1 (i, n - s) := by
  intro s
  induction s with
  | zero =>
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨K, hK⟩ : ∃ K, S.L i = K + 1 := ⟨S.L i - 1, by have := hS.one_le_L i; omega⟩
    simp only [g_st_zero]
    rw [hK, Finset.sum_range_succ']
    simp
  | succ s ih =>
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    refine (g_cons S hS π ω m i s).trans ?_
    have := ih m (by omega)
    rwa [show m + 1 - (s + 1) = m - s by omega]

/-! ## Part 11: measurability and non-anticipation for an arbitrary policy -/

theorem g_hist (S : System) (π : Policy S) (ω : Omega S) :
    ∀ n (k : Fin (n + 1)), history S π ω n k = stateAt S π ω k := by
  intro n
  induction n with
  | zero => intro k; rw [Fin.fin_one_eq_zero k]; rfl
  | succ n ih =>
    intro k
    refine Fin.lastCases ?_ (fun k' => ?_) k
    · rfl
    · simp only [history, Fin.snoc_castSucc, ih, Fin.coe_castSucc]

/-- a bound on all step counts -/
def gLm (S : System) : ℕ := ∑ i, S.L i

theorem g_L_le (S : System) (i : Fin S.I) : S.L i ≤ gLm S :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

/-- the countable type of reachable histories up to period `n + 1` -/
abbrev gR (S : System) (n : ℕ) : Type := Fin (n + 1) → Fin S.I → Fin (n + 1) → Fin (gLm S) → ℕ

def gρ (S : System) (n : ℕ) (h : Fin (n + 1) → State S) : gR S n := fun k i s l => h k i s l

def gι (S : System) (n : ℕ) (r : gR S n) : Fin (n + 1) → State S := fun k i s l =>
  if hs : s < n + 1 then if hl : l < gLm S then r k i ⟨s, hs⟩ ⟨l, hl⟩ else 0 else 0

theorem g_ιρ (S : System) (π : Policy S) (ω : Omega S) (n : ℕ) :
    gι S n (gρ S n (history S π ω n)) = history S π ω n := by
  funext k i s l
  simp only [gι, gρ]
  split_ifs with hs hl
  · rfl
  · rw [g_hist, g_st_ge S π ω _ i s l ((g_L_le S i).trans (not_lt.1 hl))]
  · rw [g_hist, g_st_old S π ω _ i s l (by have := k.2; omega)]

theorem g_meas_nat2 {α : Type*} [MeasurableSpace α] (F : ℕ → ℕ → ℕ) {X Y : α → ℕ}
    (hX : Measurable X) (hY : Measurable Y) : Measurable fun a => F (X a) (Y a) :=
  (measurable_of_countable (fun p : ℕ × ℕ => F p.1 p.2)).comp (hX.prodMk hY)

theorem g_meas_of_coord (S : System) (π : Policy S) (n : ℕ)
    (hc : ∀ (k : Fin (n + 1)) i s l, Measurable fun ω : Omega S => history S π ω n k i s l)
    (g : (Fin (n + 1) → State S) → ℕ) : Measurable fun ω => g (history S π ω n) := by
  have hρ : Measurable fun ω : Omega S => gρ S n (history S π ω n) :=
    measurable_pi_lambda _ fun k => measurable_pi_lambda _ fun i => measurable_pi_lambda _
      fun s => measurable_pi_lambda _ fun l => hc k i s l
  have : (fun ω => g (history S π ω n)) =
      (fun r => g (gι S n r)) ∘ (fun ω => gρ S n (history S π ω n)) := by
    funext ω; simp only [Function.comp, g_ιρ S π ω n]
  rw [this]
  exact (measurable_of_countable _).comp hρ

theorem g_meas_coord (S : System) (π : Policy S) :
    ∀ n (k : Fin (n + 1)) i s l, Measurable fun ω : Omega S => history S π ω n k i s l := by
  intro n
  induction n with
  | zero => intro k i s l; simp only [history]; exact measurable_const
  | succ n ih =>
    have hg := g_meas_of_coord S π n ih
    have hsu : ∀ i s l, Measurable fun ω : Omega S =>
        cellSucc S ω.2 (n + 1) i s l (π.a n (history S π ω n) i s l) := by
      intro i s l
      unfold cellSucc
      exact Finset.measurable_sum _ fun j _ =>
        c1_meas_cnt S (fun k => (i, n + 1, s, l, j, k)) (fun u => (u : ℝ) < S.β i j)
          (measurableSet_lt measurable_subtype_coe measurable_const) _
          (hg (fun h => π.a n h i s l j))
    have hfa : ∀ i s l, Measurable fun ω : Omega S =>
        cellFail S ω.2 (n + 1) i s l (π.a n (history S π ω n) i s l) := by
      intro i s l
      unfold cellFail
      exact g_meas_nat2 (fun x y => x - y)
        (Finset.measurable_sum _ fun j _ => hg (fun h => π.a n h i s l j)) (hsu i s l)
    have hst : ∀ i s l, Measurable fun ω : Omega S => stateAt S π ω (n + 1) i s l := by
      intro i s l
      rcases s with _ | s
      · by_cases h1 : S.L i ≤ l
        · simp only [g_st_zero, h1, if_true]; exact measurable_const
        · by_cases h2 : l = 0
          · subst h2
            simp only [g_st_zero, h1, if_false, if_true]
            exact (measurable_pi_apply _).comp measurable_fst
          · simp only [g_st_zero, h1, h2, if_false]; exact measurable_const
      · simp only [g_st_succ]
        by_cases h1 : S.L i ≤ l
        · simp only [h1, if_true]; exact measurable_const
        simp only [h1, if_false]
        refine Measurable.add ?_ (hfa i s l)
        by_cases h2 : l = 0
        · simp only [h2, if_true]; exact measurable_const
        · simp only [h2, if_false]; exact hsu i s (l - 1)
    intro k i s l
    refine Fin.lastCases ?_ (fun k' => ?_) k
    · exact hst i s l
    · simp only [history, Fin.snoc_castSucc]; exact ih k' i s l

/-- every functional of the history is measurable (`π.a` itself need not be) -/
theorem g_meas_hist (S : System) (π : Policy S) (n : ℕ) (g : (Fin (n + 1) → State S) → ℕ) :
    Measurable fun ω => g (history S π ω n) :=
  g_meas_of_coord S π n (g_meas_coord S π n) g

theorem g_succ_congr (S : System) (U U' : c1Idx S → unitInterval) (t : ℕ)
    (hU : ∀ p : c1Idx S, p.2.1 = t → U p = U' p) (i : Fin S.I) (s l : ℕ)
    (a : Fin (S.J + 1) → ℕ) : cellSucc S U t i s l a = cellSucc S U' t i s l a := by
  have : ∀ j k, U (i, t, s, l, j, k) = U' (i, t, s, l, j, k) := fun j k => hU _ rfl
  simp only [cellSucc, this]

theorem g_fail_congr (S : System) (U U' : c1Idx S → unitInterval) (t : ℕ)
    (hU : ∀ p : c1Idx S, p.2.1 = t → U p = U' p) (i : Fin S.I) (s l : ℕ)
    (a : Fin (S.J + 1) → ℕ) : cellFail S U t i s l a = cellFail S U' t i s l a := by
  simp only [cellFail, g_succ_congr S U U' t hU]

/-- non-anticipation: the history up to period `n + 1` uses only the uniforms of periods `≤ n` -/
theorem g_dep (S : System) (π : Policy S) :
    ∀ n (N : Fin S.I × ℕ → ℕ) (U U' : c1Idx S → unitInterval),
      (∀ p : c1Idx S, p.2.1 ≤ n → U p = U' p) →
      history S π (N, U) n = history S π (N, U') n := by
  intro n
  induction n with
  | zero => intro N U U' _; rfl
  | succ n ih =>
    intro N U U' h
    have e := ih N U U' (fun p hp => h p (by omega))
    have hU : ∀ p : c1Idx S, p.2.1 = n + 1 → U p = U' p := fun p hp => h p (by omega)
    simp only [history, e, g_succ_congr S U U' (n + 1) hU, g_fail_congr S U U' (n + 1) hU]

/-! ## Part 12: conditional means of the step outcomes under an arbitrary policy -/

theorem g_E_cnt_a (S : System) (hS : Standing S) (π : Policy S) (lam : Fin S.I → ℝ≥0)
    (n : ℕ) (i : Fin S.I) (s l : ℕ) (j : Fin (S.J + 1)) (P : unitInterval → Prop)
    [DecidablePred P] (hP : MeasurableSet {u | P u}) :
    ∫⁻ ω, ((((Finset.range (π.a n (history S π ω n) i s l j)).filter
        fun k => P (ω.2 (i, n + 1, s, l, j, k))).card : ℕ) : ℝ≥0∞) ∂(sampleMeasure S lam) =
      volume {u | P u} *
        ∫⁻ ω, (π.a n (history S π ω n) i s l j : ℝ≥0∞) ∂(sampleMeasure S lam) :=
  c1_E_cnt S lam n (fun k => (i, n + 1, s, l, j, k)) (fun _ => rfl) P hP
    (fun ω => π.a n (history S π ω n) i s l j) (g_meas_hist S π n (fun h => π.a n h i s l j))
    (fun N U U' h => by simp only [g_dep S π n N U U' h])

/-- `E[y] = Σⱼ β_{i,j} E[a_j]` -/
theorem g_E_succ (S : System) (hS : Standing S) (π : Policy S) (lam : Fin S.I → ℝ≥0)
    (n : ℕ) (i : Fin S.I) (s l : ℕ) :
    ∫⁻ ω, (cellSucc S ω.2 (n + 1) i s l (π.a n (history S π ω n) i s l) : ℝ≥0∞)
      ∂(sampleMeasure S lam) =
      ∑ j, ENNReal.ofReal (S.β i j) *
        ∫⁻ ω, (π.a n (history S π ω n) i s l j : ℝ≥0∞) ∂(sampleMeasure S lam) := by
  unfold cellSucc
  push_cast
  rw [lintegral_finset_sum _ (fun j _ => ?_)]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [g_E_cnt_a S hS π lam n i s l j (fun u => (u : ℝ) < S.β i j)
      (measurableSet_lt measurable_subtype_coe measurable_const), c1_vol_lt S hS i j]
  · exact measurable_from_nat.comp
      (c1_meas_cnt S (fun k => (i, n + 1, s, l, j, k)) (fun u => (u : ℝ) < S.β i j)
        (measurableSet_lt measurable_subtype_coe measurable_const) _
        (g_meas_hist S π n (fun h => π.a n h i s l j)))

/-- `E[ỹ] = Σⱼ (1 − β_{i,j}) E[a_j]` -/
theorem g_E_fail (S : System) (hS : Standing S) (π : Policy S) (lam : Fin S.I → ℝ≥0)
    (n : ℕ) (i : Fin S.I) (s l : ℕ) :
    ∫⁻ ω, (cellFail S ω.2 (n + 1) i s l (π.a n (history S π ω n) i s l) : ℝ≥0∞)
      ∂(sampleMeasure S lam) =
      ∑ j, ENNReal.ofReal (1 - S.β i j) *
        ∫⁻ ω, (π.a n (history S π ω n) i s l j : ℝ≥0∞) ∂(sampleMeasure S lam) := by
  have hf : ∀ ω : Omega S, cellFail S ω.2 (n + 1) i s l (π.a n (history S π ω n) i s l) =
      ∑ j, ((Finset.range (π.a n (history S π ω n) i s l j)).filter
        fun k => ¬ ((ω.2 (i, n + 1, s, l, j, k) : ℝ) < S.β i j)).card := by
    intro ω
    have hsplit : ∀ j, ((Finset.range (π.a n (history S π ω n) i s l j)).filter
        fun k => ((ω.2 (i, n + 1, s, l, j, k) : ℝ) < S.β i j)).card +
        ((Finset.range (π.a n (history S π ω n) i s l j)).filter
        fun k => ¬ ((ω.2 (i, n + 1, s, l, j, k) : ℝ) < S.β i j)).card =
        π.a n (history S π ω n) i s l j := fun j => by
      rw [Finset.card_filter_add_card_filter_not, Finset.card_range]
    rw [cellFail, ← Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hsplit j),
      Finset.sum_add_distrib]
    exact Nat.add_sub_cancel_left _ _
  simp only [hf]
  push_cast
  rw [lintegral_finset_sum _ (fun j _ => ?_)]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [g_E_cnt_a S hS π lam n i s l j (fun u => ¬ (u : ℝ) < S.β i j)
      (measurableSet_lt measurable_subtype_coe measurable_const).compl, c1_vol_nlt S hS i j]
  · exact measurable_from_nat.comp
      (c1_meas_cnt S (fun k => (i, n + 1, s, l, j, k)) (fun u => ¬ (u : ℝ) < S.β i j)
        (measurableSet_lt measurable_subtype_coe measurable_const).compl _
        (g_meas_hist S π n (fun h => π.a n h i s l j)))

/-! ## Part 13a: abstract analysis lemmas -/

theorem h_sum_le {ι Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (s : Finset ι)
    (f : ι → Ω → ℝ≥0∞) : ∑ k ∈ s, ∫⁻ ω, f k ω ∂μ ≤ ∫⁻ ω, ∑ k ∈ s, f k ω ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (add_le_add le_rfl ih).trans (le_lintegral_add _ _)

theorem h_liminf (c : ℕ → ℝ≥0∞) (Λ K B : ℝ≥0∞) (hΛ : Λ ≠ ⊤) (hK : K ≠ ⊤) (hB : B ≠ ⊤)
    (h : ∀ T : ℕ, (T : ℝ≥0∞) * Λ ≤ (∑ n ∈ Finset.range T, c n) + B + K * c T) :
    Λ ≤ Filter.liminf (fun T : ℕ => (∑ n ∈ Finset.range T, c n) / (T : ℝ≥0∞)) atTop := by
  set A : ℕ → ℝ≥0∞ := fun T => ∑ n ∈ Finset.range T, c n with hA
  have hmono : Monotone A := fun a b hab =>
    Finset.sum_le_sum_of_subset (Finset.range_mono hab)
  have hwin : ∀ m T : ℕ, (m : ℝ≥0∞) * T * Λ ≤ ((m : ℝ≥0∞) + K) * A (T + m) + m * B := by
    intro m T
    have hsplit : A (T + m) = A T + ∑ k ∈ Finset.range m, c (T + k) := by
      simp only [hA]; exact Finset.sum_range_add c T m
    calc (m : ℝ≥0∞) * T * Λ = ∑ k ∈ Finset.range m, (T : ℝ≥0∞) * Λ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
      _ ≤ ∑ k ∈ Finset.range m, ((T + k : ℕ) : ℝ≥0∞) * Λ :=
          Finset.sum_le_sum fun k _ => by gcongr; exact_mod_cast Nat.le_add_right T k
      _ ≤ ∑ k ∈ Finset.range m, (A (T + k) + B + K * c (T + k)) :=
          Finset.sum_le_sum fun k _ => h _
      _ = ∑ k ∈ Finset.range m, A (T + k) + m * B + K * ∑ k ∈ Finset.range m, c (T + k) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
            nsmul_eq_mul, Finset.mul_sum]
      _ ≤ ∑ k ∈ Finset.range m, A (T + m) + m * B + K * A (T + m) := by
          gcongr with k hk
          · exact hmono (by simp at hk; omega)
          · rw [hsplit]; exact le_add_self
      _ = ((m : ℝ≥0∞) + K) * A (T + m) + m * B := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  have hev : ∀ b, b < Λ → ∀ᶠ T : ℕ in atTop, b ≤ A T / (T : ℝ≥0∞) := by
    intro b hb
    by_cases htop : ∃ T0, A T0 = ⊤
    · obtain ⟨T0, hT0⟩ := htop
      filter_upwards [Filter.eventually_ge_atTop T0] with T hT
      have : A T = ⊤ := top_le_iff.1 (hT0 ▸ hmono hT)
      rw [this, ENNReal.top_div_of_ne_top (ENNReal.natCast_ne_top T)]
      exact le_top
    simp only [not_exists] at htop
    have hb' : b ≠ ⊤ := ne_top_of_lt hb
    set lam := Λ.toReal
    set k := K.toReal
    set β := B.toReal
    set b' := b.toReal
    have hk0 : 0 ≤ k := ENNReal.toReal_nonneg
    have hβ0 : 0 ≤ β := ENNReal.toReal_nonneg
    have hb0 : 0 ≤ b' := ENNReal.toReal_nonneg
    have hblt : b' < lam := (ENNReal.toReal_lt_toReal hb' hΛ).2 hb
    obtain ⟨m, hm⟩ := exists_nat_gt (b' * k / (lam - b'))
    have hm0 : 0 < (m : ℝ) := lt_of_le_of_lt (div_nonneg (mul_nonneg hb0 hk0)
      (by linarith)) hm
    set D := (m : ℝ) * lam - b' * (m + k) with hD
    have hDpos : 0 < D := by
      have h1 : b' * k < m * (lam - b') := by
        rwa [div_lt_iff₀ (by linarith)] at hm
      rw [hD]; nlinarith
    obtain ⟨T1, hT1⟩ := exists_nat_gt (((m : ℝ) ^ 2 * lam + m * β) / D)
    filter_upwards [Filter.eventually_ge_atTop (T1 + m)] with T hT
    obtain ⟨T', rfl⟩ : ∃ T', T = T' + m := ⟨T - m, by omega⟩
    have hw := hwin m T'
    have hAne : A (T' + m) ≠ ⊤ := htop _
    have hreal : (m : ℝ) * T' * lam ≤ (m + k) * (A (T' + m)).toReal + m * β := by
      have := ENNReal.toReal_mono (by
        exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (ENNReal.add_ne_top.2
          ⟨ENNReal.natCast_ne_top m, hK⟩) hAne, ENNReal.mul_ne_top (ENNReal.natCast_ne_top m) hB⟩)
        hw
      simpa [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.add_ne_top, ENNReal.mul_ne_top,
        hK, hB, hAne, hΛ] using this
    have hT1' : ((m : ℝ) ^ 2 * lam + m * β) < D * T' := by
      have h2 : (T1 : ℝ) ≤ T' := by exact_mod_cast (by omega : T1 ≤ T')
      rw [div_lt_iff₀ hDpos] at hT1; nlinarith
    have hfin : b' * ((T' + m : ℕ) : ℝ) ≤ (A (T' + m)).toReal := by
      have hmk : 0 < (m : ℝ) + k := by linarith
      have : (m + k) * (b' * ((T' + m : ℕ) : ℝ)) ≤ (m + k) * (A (T' + m)).toReal := by
        push_cast
        rw [hD] at hT1'
        nlinarith
      exact le_of_mul_le_mul_left this hmk
    have hmnat : 0 < m := by exact_mod_cast hm0
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast (by omega : (T' + m) ≠ 0)))
      (Or.inl (ENNReal.natCast_ne_top _))]
    rw [← ENNReal.toReal_le_toReal (ENNReal.mul_ne_top hb' (ENNReal.natCast_ne_top _)) hAne,
      ENNReal.toReal_mul, ENNReal.toReal_natCast]
    exact hfin
  refine le_of_forall_lt fun c hc => ?_
  obtain ⟨b, hcb, hbΛ⟩ := exists_between hc
  exact lt_of_lt_of_le hcb (Filter.le_liminf_of_le (by isBoundedDefault) (hev b hbΛ))

/-! ## Part 13b: the potential argument, `Λ ≤ avgCost π` for every policy -/

noncomputable def qF (S : System) (i : Fin S.I) (s l : ℕ) : ℝ≥0∞ := ENNReal.ofReal (fDP S i s l)

noncomputable def qc (S : System) (i : Fin S.I) (s : ℕ) (j : Fin (S.J + 1)) : ℝ≥0∞ :=
  ENNReal.ofReal (resCost S j) + (if S.δ i ≤ s then ENNReal.ofReal (S.W i) else 0)

noncomputable def qPhi (S : System) (π : Policy S) (ω : Omega S) (n : ℕ) : ℝ≥0∞ :=
  ∑ i, ∑ s ∈ Finset.range n, ∑ l ∈ Finset.range (S.L i),
    qF S i s l * (stateAt S π ω n i s l : ℝ≥0∞)

noncomputable def qA (S : System) (π : Policy S) (ω : Omega S) (n : ℕ) (i : Fin S.I) (s l : ℕ)
    (j : Fin (S.J + 1)) : ℝ≥0∞ := (π.a n (history S π ω n) i s l j : ℝ≥0∞)

noncomputable def qSu (S : System) (π : Policy S) (ω : Omega S) (n : ℕ) (i : Fin S.I) (s l : ℕ) :
    ℝ≥0∞ := (cellSucc S ω.2 (n + 1) i s l (π.a n (history S π ω n) i s l) : ℝ≥0∞)

noncomputable def qFa (S : System) (π : Policy S) (ω : Omega S) (n : ℕ) (i : Fin S.I) (s l : ℕ) :
    ℝ≥0∞ := (cellFail S ω.2 (n + 1) i s l (π.a n (history S π ω n) i s l) : ℝ≥0∞)

noncomputable def qK (S : System) : ℝ≥0∞ :=
  ∑ i, ENNReal.ofReal (d1K S i) / ENNReal.ofReal (S.W i)

noncomputable def qB (S : System) (lam : Fin S.I → ℝ≥0) : ℝ≥0∞ :=
  ∑ i, ENNReal.ofReal (d1K S i) * ((S.δ i : ℝ≥0∞) * lam i)

theorem q_cells_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (S : System) (n : ℕ)
    (f : Fin S.I → ℕ → ℕ → Ω → ℝ≥0∞) :
    ∑ i, ∑ s ∈ Finset.range n, ∑ l ∈ Finset.range (S.L i), ∫⁻ ω, f i s l ω ∂μ ≤
      ∫⁻ ω, ∑ i, ∑ s ∈ Finset.range n, ∑ l ∈ Finset.range (S.L i), f i s l ω ∂μ := by
  calc ∑ i, ∑ s ∈ Finset.range n, ∑ l ∈ Finset.range (S.L i), ∫⁻ ω, f i s l ω ∂μ
      ≤ ∑ i, ∑ s ∈ Finset.range n, ∫⁻ ω, ∑ l ∈ Finset.range (S.L i), f i s l ω ∂μ :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun s _ => h_sum_le μ _ _
    _ ≤ ∑ i, ∫⁻ ω, ∑ s ∈ Finset.range n, ∑ l ∈ Finset.range (S.L i), f i s l ω ∂μ :=
        Finset.sum_le_sum fun i _ => h_sum_le μ _ (fun s ω => ∑ l ∈ Finset.range (S.L i), f i s l ω)
    _ ≤ _ := h_sum_le μ _ (fun i ω => ∑ s ∈ Finset.range n, ∑ l ∈ Finset.range (S.L i), f i s l ω)

theorem q_bell (S : System) (hS : Standing S) (sel : Selection S) (i : Fin S.I)
    (s l : ℕ) (hl : l < S.L i) (j : Fin (S.J + 1)) :
    qF S i s l ≤ qc S i s j + ENNReal.ofReal (S.β i j) * qF S i (s + 1) (l + 1) +
      ENNReal.ofReal (1 - S.β i j) * qF S i (s + 1) l := by
  have h := d1_bell_le S hS sel i s l hl j
  have h0 := d1_resCost_nonneg S hS j
  have hb0 := hS.β_nonneg i j
  have hb1 : 0 ≤ 1 - S.β i j := by linarith [hS.β_le_one i j]
  have hf1 := d1_f_nonneg S hS sel i (s + 1) (l + 1)
  have hf2 := d1_f_nonneg S hS sel i (s + 1) l
  have hw : 0 ≤ (if S.δ i ≤ s then S.W i else 0) := by
    split_ifs <;> linarith [hS.W_pos i]
  have hite : (if S.δ i ≤ s then ENNReal.ofReal (S.W i) else 0) =
      ENNReal.ofReal (if S.δ i ≤ s then S.W i else 0) := by split_ifs <;> simp
  unfold qF qc
  rw [hite, ← ENNReal.ofReal_mul hb0, ← ENNReal.ofReal_mul hb1, ← ENNReal.ofReal_add h0 hw,
    ← ENNReal.ofReal_add (add_nonneg h0 hw) (mul_nonneg hb0 hf1),
    ← ENNReal.ofReal_add (add_nonneg (add_nonneg h0 hw) (mul_nonneg hb0 hf1)) (mul_nonneg hb1 hf2)]
  exact ENNReal.ofReal_le_ofReal h

/-- pathwise: the period cost dominates the per-assignment costs -/
theorem q_cost_ge (S : System) (π : Policy S) (ω : Omega S) (n : ℕ) :
    ∑ i, ∑ s ∈ Finset.range n, ∑ l ∈ Finset.range (S.L i), ∑ j,
      qc S i s j * qA S π ω n i s l j ≤ periodCost S S.R S.R π ω n := by
  have hsplit : ∀ i s l, ∑ j, qc S i s j * qA S π ω n i s l j =
      ∑ j : Fin S.J, ENNReal.ofReal (S.R j) * (π.a n (history S π ω n) i s l j.succ : ℝ≥0∞) +
      (if S.δ i ≤ s then ENNReal.ofReal (S.W i) else 0) *
        ((∑ j, π.a n (history S π ω n) i s l j : ℕ) : ℝ≥0∞) := by
    intro i s l
    simp only [qc, qA, add_mul, Finset.sum_add_distrib, Nat.cast_sum, Finset.mul_sum]
    congr 1
    rw [Fin.sum_univ_succ]
    simp [d1_resCost_zero, d1_resCost_succ]
  simp only [hsplit, Finset.sum_add_distrib]
  unfold periodCost
  refine add_le_add ?_ (le_of_eq ?_)
  · have hcap : ∀ j : Fin S.J, ((∑ i, ∑ l ∈ Finset.range (S.L i), ∑ s ∈ Finset.range n,
        π.a n (history S π ω n) i s l j.succ : ℕ) : ℝ≥0∞) ≤
        (π.M j : ℝ≥0∞) + (π.m n (history S π ω n) j : ℝ≥0∞) := by
      intro j
      have h1 := π.capacity n (history S π ω n) j
      have h2 : (((∑ i, ∑ l ∈ Finset.range (S.L i), ∑ s ∈ Finset.range n,
          π.a n (history S π ω n) i s l j.succ : ℕ) : ℝ≥0) : ℝ≥0∞) ≤
          ((π.M j + π.m n (history S π ω n) j : ℝ≥0) : ℝ≥0∞) := ENNReal.coe_le_coe.2 h1
      simpa using h2
    have hcomm : ∑ i, ∑ s ∈ Finset.range n, ∑ l ∈ Finset.range (S.L i), ∑ j : Fin S.J,
          ENNReal.ofReal (S.R j) * (π.a n (history S π ω n) i s l j.succ : ℝ≥0∞) =
        ∑ j : Fin S.J, ∑ i, ∑ l ∈ Finset.range (S.L i), ∑ s ∈ Finset.range n,
          ENNReal.ofReal (S.R j) * (π.a n (history S π ω n) i s l j.succ : ℝ≥0∞) := by
      rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm]
      rw [Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun l _ => Finset.sum_comm]
      rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm]
      rw [Finset.sum_comm]
    rw [hcomm]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [← mul_add]
    calc ∑ i, ∑ l ∈ Finset.range (S.L i), ∑ s ∈ Finset.range n,
          ENNReal.ofReal (S.R j) * (π.a n (history S π ω n) i s l j.succ : ℝ≥0∞)
        = ENNReal.ofReal (S.R j) * ((∑ i, ∑ l ∈ Finset.range (S.L i), ∑ s ∈ Finset.range n,
          π.a n (history S π ω n) i s l j.succ : ℕ) : ℝ≥0∞) := by
          simp only [Nat.cast_sum, Finset.mul_sum]
      _ ≤ _ := by gcongr; exact hcap j
  · refine Finset.sum_congr rfl fun i _ => ?_
    have hIco : Finset.Ico (S.δ i) n = (Finset.range n).filter (fun s => S.δ i ≤ s) := by
      ext s; simp only [Finset.mem_Ico, Finset.mem_filter, Finset.mem_range]; exact and_comm
    rw [hIco, Finset.sum_filter]
    refine Finset.sum_congr rfl fun s _ => ?_
    split_ifs with h
    · refine Finset.sum_congr rfl fun l hl => ?_
      rw [g_assign S π ω n i s l (Finset.mem_range.1 hl)]
    · simp

theorem q_meas_A (S : System) (π : Policy S) (n : ℕ) (i : Fin S.I) (s l : ℕ)
    (j : Fin (S.J + 1)) : Measurable fun ω => qA S π ω n i s l j :=
  measurable_from_nat.comp (g_meas_hist S π n (fun h => π.a n h i s l j))

theorem q_Phi_eq (S : System) (π : Policy S) (lam : Fin S.I → ℝ≥0) (n : ℕ) :
    ∫⁻ ω, qPhi S π ω n ∂(sampleMeasure S lam) =
      ∑ i, ∑ s ∈ Finset.range n, ∑ l ∈ Finset.range (S.L i),
        qF S i s l * ∑ j, ∫⁻ ω, qA S π ω n i s l j ∂(sampleMeasure S lam) := by
  have hpt : ∀ ω, qPhi S π ω n = ∑ i, ∑ s ∈ Finset.range n, ∑ l ∈ Finset.range (S.L i),
      ∑ j, qF S i s l * qA S π ω n i s l j := by
    intro ω
    unfold qPhi
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun s _ =>
      Finset.sum_congr rfl fun l hl => ?_
    rw [← g_assign S π ω n i s l (Finset.mem_range.1 hl), Nat.cast_sum, Finset.mul_sum]
    rfl
  have hm := q_meas_A S π n
  simp only [hpt]
  rw [lintegral_finsetSum _ (fun i _ => Finset.measurable_sum _ fun s _ =>
    Finset.measurable_sum _ fun l _ => Finset.measurable_sum _ fun j _ =>
      (hm i s l j).const_mul _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lintegral_finsetSum _ (fun s _ => Finset.measurable_sum _ fun l _ =>
    Finset.measurable_sum _ fun j _ => (hm i s l j).const_mul _)]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [lintegral_finsetSum _ (fun l _ => Finset.measurable_sum _ fun j _ =>
    (hm i s l j).const_mul _)]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [lintegral_finsetSum _ (fun j _ => (hm i s l j).const_mul _), Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => lintegral_const_mul _ (hm i s l j)

theorem q_cost_int (S : System) (π : Policy S) (lam : Fin S.I → ℝ≥0) (n : ℕ) :
    ∑ i, ∑ s ∈ Finset.range n, ∑ l ∈ Finset.range (S.L i), ∑ j,
      qc S i s j * ∫⁻ ω, qA S π ω n i s l j ∂(sampleMeasure S lam) ≤
      ∫⁻ ω, periodCost S S.R S.R π ω n ∂(sampleMeasure S lam) := by
  calc ∑ i, ∑ s ∈ Finset.range n, ∑ l ∈ Finset.range (S.L i), ∑ j,
        qc S i s j * ∫⁻ ω, qA S π ω n i s l j ∂(sampleMeasure S lam)
      ≤ ∑ i, ∑ s ∈ Finset.range n, ∑ l ∈ Finset.range (S.L i),
        ∫⁻ ω, ∑ j, qc S i s j * qA S π ω n i s l j ∂(sampleMeasure S lam) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun l _ =>
          (Finset.sum_le_sum fun j _ => lintegral_const_mul_le _ _).trans (h_sum_le _ _ _)
    _ ≤ ∫⁻ ω, ∑ i, ∑ s ∈ Finset.range n, ∑ l ∈ Finset.range (S.L i),
        ∑ j, qc S i s j * qA S π ω n i s l j ∂(sampleMeasure S lam) :=
        q_cells_le _ S n (fun i s l ω => ∑ j, qc S i s j * qA S π ω n i s l j)
    _ ≤ _ := lintegral_mono fun ω => q_cost_ge S π ω n

theorem q_cell_pt (S : System) (hS : Standing S) (π : Policy S) (ω : Omega S) (n : ℕ)
    (i : Fin S.I) (s : ℕ) :
    ∑ l ∈ Finset.range (S.L i), (qF S i (s + 1) (l + 1) * qSu S π ω n i s l +
      qF S i (s + 1) l * qFa S π ω n i s l) =
    ∑ l ∈ Finset.range (S.L i), qF S i (s + 1) l * (stateAt S π ω (n + 1) i (s + 1) l : ℝ≥0∞) := by
  obtain ⟨L', hL'⟩ : ∃ L', S.L i = L' + 1 := ⟨S.L i - 1, by have := hS.one_le_L i; omega⟩
  have hzero : qF S i (s + 1) (L' + 1) = 0 := by
    unfold qF; rw [d1_f_ge S i _ _ (by omega)]; simp
  have hX : ∀ l ∈ Finset.range (S.L i), qF S i (s + 1) l *
      (stateAt S π ω (n + 1) i (s + 1) l : ℝ≥0∞) =
      qF S i (s + 1) l * (if l = 0 then 0 else qSu S π ω n i s (l - 1)) +
      qF S i (s + 1) l * qFa S π ω n i s l := by
    intro l hl
    rw [g_st_succ, if_neg (by simp at hl; omega)]
    by_cases h0 : l = 0 <;> simp [h0, mul_add, qSu, qFa]
  rw [Finset.sum_congr rfl hX, Finset.sum_add_distrib, Finset.sum_add_distrib, hL']
  congr 1
  rw [Finset.sum_range_succ, Finset.sum_range_succ' _ L', hzero]
  simp

theorem q_phi_succ_pt (S : System) (hS : Standing S) (π : Policy S) (ω : Omega S) (n : ℕ) :
    ∑ i, qF S i 0 0 * (ω.1 (i, n + 1) : ℝ≥0∞) +
      ∑ i, ∑ s ∈ Finset.range n, ∑ l ∈ Finset.range (S.L i),
        (qF S i (s + 1) (l + 1) * qSu S π ω n i s l + qF S i (s + 1) l * qFa S π ω n i s l) ≤
      qPhi S π ω (n + 1) := by
  unfold qPhi
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.sum_range_succ', add_comm (qF S i 0 0 * _)]
  refine add_le_add (le_of_eq (Finset.sum_congr rfl fun s _ => q_cell_pt S hS π ω n i s)) ?_
  have h0 : 0 ∈ Finset.range (S.L i) := Finset.mem_range.2 (hS.one_le_L i)
  refine le_trans (le_of_eq ?_) (Finset.single_le_sum
    (f := fun l => qF S i 0 l * (stateAt S π ω (n + 1) i 0 l : ℝ≥0∞)) (fun _ _ => by simp) h0)
  show _ = qF S i 0 0 * (stateAt S π ω (n + 1) i 0 0 : ℝ≥0∞)
  rw [g_st_zero, if_neg (by have := hS.one_le_L i; omega), if_pos rfl]

theorem q_Phi_succ_int (S : System) (hS : Standing S) (π : Policy S) (lam : Fin S.I → ℝ≥0)
    (n : ℕ) :
    ∑ i, qF S i 0 0 * (lam i : ℝ≥0∞) +
      ∑ i, ∑ s ∈ Finset.range n, ∑ l ∈ Finset.range (S.L i),
        (qF S i (s + 1) (l + 1) * ∫⁻ ω, qSu S π ω n i s l ∂(sampleMeasure S lam) +
          qF S i (s + 1) l * ∫⁻ ω, qFa S π ω n i s l ∂(sampleMeasure S lam)) ≤
      ∫⁻ ω, qPhi S π ω (n + 1) ∂(sampleMeasure S lam) := by
  refine le_trans ?_ (lintegral_mono fun ω => q_phi_succ_pt S hS π ω n)
  refine le_trans (add_le_add ?_ ?_) (le_lintegral_add _ _)
  · refine le_trans (Finset.sum_le_sum fun i _ => ?_)
      (h_sum_le _ _ (fun i (ω : Omega S) => qF S i 0 0 * (ω.1 (i, n + 1) : ℝ≥0∞)))
    rw [← c1_E_N S lam i (n + 1)]
    exact lintegral_const_mul_le _ _
  · refine le_trans (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun s _ =>
      Finset.sum_le_sum fun l _ => ?_) (q_cells_le _ S n (fun i s l ω =>
        qF S i (s + 1) (l + 1) * qSu S π ω n i s l + qF S i (s + 1) l * qFa S π ω n i s l))
    exact le_trans (add_le_add (lintegral_const_mul_le _ _) (lintegral_const_mul_le _ _))
      (le_lintegral_add _ _)

theorem q_step (S : System) (hS : Standing S) (sel : Selection S) (π : Policy S)
    (lam : Fin S.I → ℝ≥0) (n : ℕ) :
    ∫⁻ ω, qPhi S π ω n ∂(sampleMeasure S lam) + ∑ i, qF S i 0 0 * (lam i : ℝ≥0∞) ≤
      ∫⁻ ω, periodCost S S.R S.R π ω n ∂(sampleMeasure S lam) +
        ∫⁻ ω, qPhi S π ω (n + 1) ∂(sampleMeasure S lam) := by
  rw [q_Phi_eq]
  refine le_trans ?_ (add_le_add (q_cost_int S π lam n) (q_Phi_succ_int S hS π lam n))
  have key : ∑ i, ∑ s ∈ Finset.range n, ∑ l ∈ Finset.range (S.L i),
        qF S i s l * ∑ j, ∫⁻ ω, qA S π ω n i s l j ∂(sampleMeasure S lam) ≤
      ∑ i, ∑ s ∈ Finset.range n, ∑ l ∈ Finset.range (S.L i), ∑ j,
        qc S i s j * ∫⁻ ω, qA S π ω n i s l j ∂(sampleMeasure S lam) +
      ∑ i, ∑ s ∈ Finset.range n, ∑ l ∈ Finset.range (S.L i),
        (qF S i (s + 1) (l + 1) * ∫⁻ ω, qSu S π ω n i s l ∂(sampleMeasure S lam) +
          qF S i (s + 1) l * ∫⁻ ω, qFa S π ω n i s l ∂(sampleMeasure S lam)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun s _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun l hl => ?_
    have hSu : ∫⁻ ω, qSu S π ω n i s l ∂(sampleMeasure S lam) =
        ∑ j, ENNReal.ofReal (S.β i j) * ∫⁻ ω, qA S π ω n i s l j ∂(sampleMeasure S lam) :=
      g_E_succ S hS π lam n i s l
    have hFa : ∫⁻ ω, qFa S π ω n i s l ∂(sampleMeasure S lam) =
        ∑ j, ENNReal.ofReal (1 - S.β i j) * ∫⁻ ω, qA S π ω n i s l j ∂(sampleMeasure S lam) :=
      g_E_fail S hS π lam n i s l
    rw [hSu, hFa, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    calc qF S i s l * ∫⁻ ω, qA S π ω n i s l j ∂(sampleMeasure S lam)
        ≤ (qc S i s j + ENNReal.ofReal (S.β i j) * qF S i (s + 1) (l + 1) +
            ENNReal.ofReal (1 - S.β i j) * qF S i (s + 1) l) *
            ∫⁻ ω, qA S π ω n i s l j ∂(sampleMeasure S lam) := by
          gcongr; exact q_bell S hS sel i s l (Finset.mem_range.1 hl) j
      _ = _ := by ring
  calc _ ≤ (∑ i, ∑ s ∈ Finset.range n, ∑ l ∈ Finset.range (S.L i), ∑ j,
        qc S i s j * ∫⁻ ω, qA S π ω n i s l j ∂(sampleMeasure S lam) +
      ∑ i, ∑ s ∈ Finset.range n, ∑ l ∈ Finset.range (S.L i),
        (qF S i (s + 1) (l + 1) * ∫⁻ ω, qSu S π ω n i s l ∂(sampleMeasure S lam) +
          qF S i (s + 1) l * ∫⁻ ω, qFa S π ω n i s l ∂(sampleMeasure S lam))) +
        ∑ i, qF S i 0 0 * (lam i : ℝ≥0∞) := add_le_add key le_rfl
    _ = _ := by ring

theorem q_cum (S : System) (hS : Standing S) (sel : Selection S) (π : Policy S)
    (lam : Fin S.I → ℝ≥0) : ∀ T : ℕ,
    (T : ℝ≥0∞) * ∑ i, qF S i 0 0 * (lam i : ℝ≥0∞) ≤
      ∑ n ∈ Finset.range T, ∫⁻ ω, periodCost S S.R S.R π ω n ∂(sampleMeasure S lam) +
        ∫⁻ ω, qPhi S π ω T ∂(sampleMeasure S lam) := by
  intro T
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_range_succ]
    push_cast
    calc ((T : ℝ≥0∞) + 1) * ∑ i, qF S i 0 0 * (lam i : ℝ≥0∞)
        = (T : ℝ≥0∞) * ∑ i, qF S i 0 0 * (lam i : ℝ≥0∞) + ∑ i, qF S i 0 0 * (lam i : ℝ≥0∞) := by
          ring
      _ ≤ (∑ n ∈ Finset.range T, ∫⁻ ω, periodCost S S.R S.R π ω n ∂(sampleMeasure S lam) +
            ∫⁻ ω, qPhi S π ω T ∂(sampleMeasure S lam)) +
            ∑ i, qF S i 0 0 * (lam i : ℝ≥0∞) := add_le_add ih le_rfl
      _ = ∑ n ∈ Finset.range T, ∫⁻ ω, periodCost S S.R S.R π ω n ∂(sampleMeasure S lam) +
            (∫⁻ ω, qPhi S π ω T ∂(sampleMeasure S lam) +
            ∑ i, qF S i 0 0 * (lam i : ℝ≥0∞)) := by ring
      _ ≤ ∑ n ∈ Finset.range T, ∫⁻ ω, periodCost S S.R S.R π ω n ∂(sampleMeasure S lam) +
            (∫⁻ ω, periodCost S S.R S.R π ω T ∂(sampleMeasure S lam) +
              ∫⁻ ω, qPhi S π ω (T + 1) ∂(sampleMeasure S lam)) :=
          add_le_add le_rfl (q_step S hS sel π lam T)
      _ = _ := by ring

/-! ## Part 13c: bounding the potential; the lower bound for every policy -/

theorem q_K_ne_top (S : System) (hS : Standing S) : qK S ≠ ⊤ :=
  ENNReal.sum_ne_top.2 fun i _ =>
    ENNReal.div_ne_top ENNReal.ofReal_ne_top (ENNReal.ofReal_pos.2 (hS.W_pos i)).ne'

theorem q_B_ne_top (S : System) (lam : Fin S.I → ℝ≥0) : qB S lam ≠ ⊤ :=
  ENNReal.sum_ne_top.2 fun _ _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.coe_ne_top)

theorem q_K_le (S : System) (hS : Standing S) (i : Fin S.I) :
    ENNReal.ofReal (d1K S i) ≤ qK S * ENNReal.ofReal (S.W i) := by
  have hW0 : ENNReal.ofReal (S.W i) ≠ 0 := (ENNReal.ofReal_pos.2 (hS.W_pos i)).ne'
  calc ENNReal.ofReal (d1K S i)
      = ENNReal.ofReal (d1K S i) / ENNReal.ofReal (S.W i) * ENNReal.ofReal (S.W i) :=
        (ENNReal.div_mul_cancel hW0 ENNReal.ofReal_ne_top).symm
    _ ≤ qK S * ENNReal.ofReal (S.W i) := by
        gcongr
        exact Finset.single_le_sum
          (f := fun i => ENNReal.ofReal (d1K S i) / ENNReal.ofReal (S.W i))
          (fun _ _ => by simp) (Finset.mem_univ i)

theorem q_phi_pt (S : System) (hS : Standing S) (sel : Selection S) (π : Policy S)
    (ω : Omega S) (T : ℕ) :
    qPhi S π ω T ≤ ∑ i, ∑ s ∈ (Finset.range T).filter (fun s => s < S.δ i),
        ENNReal.ofReal (d1K S i) * (ω.1 (i, T - s) : ℝ≥0∞) +
      qK S * periodCost S S.R S.R π ω T := by
  have hlate : ∑ i, ∑ s ∈ (Finset.range T).filter (fun s => ¬ s < S.δ i),
      ∑ l ∈ Finset.range (S.L i),
        qK S * (ENNReal.ofReal (S.W i) * (stateAt S π ω T i s l : ℝ≥0∞)) ≤
      qK S * periodCost S S.R S.R π ω T := by
    have hIco : ∀ i, (Finset.range T).filter (fun s => ¬ s < S.δ i) = Finset.Ico (S.δ i) T := by
      intro i; ext s
      simp only [Finset.mem_Ico, Finset.mem_filter, Finset.mem_range, not_lt]; exact and_comm
    have hpull : ∑ i, ∑ s ∈ (Finset.range T).filter (fun s => ¬ s < S.δ i),
        ∑ l ∈ Finset.range (S.L i),
          qK S * (ENNReal.ofReal (S.W i) * (stateAt S π ω T i s l : ℝ≥0∞)) =
        qK S * ∑ i, ∑ s ∈ Finset.Ico (S.δ i) T, ∑ l ∈ Finset.range (S.L i),
          ENNReal.ofReal (S.W i) * (stateAt S π ω T i s l : ℝ≥0∞) := by
      simp only [hIco, Finset.mul_sum]
    rw [hpull]
    unfold periodCost
    exact mul_le_mul' le_rfl le_add_self
  refine le_trans ?_ (add_le_add le_rfl hlate)
  unfold qPhi
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range T) (fun s => s < S.δ i)]
  refine add_le_add (Finset.sum_le_sum fun s hs => ?_)
    (Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun l _ => ?_)
  · have hsT : s < T := Finset.mem_range.1 (Finset.mem_filter.1 hs).1
    have hc := g_cohort_le S hS π ω i s T hsT
    have hc' : ((∑ l ∈ Finset.range (S.L i), stateAt S π ω T i s l : ℕ) : ℝ≥0∞) ≤
        (ω.1 (i, T - s) : ℝ≥0∞) := by exact_mod_cast hc
    calc ∑ l ∈ Finset.range (S.L i), qF S i s l * (stateAt S π ω T i s l : ℝ≥0∞)
        ≤ ∑ l ∈ Finset.range (S.L i),
            ENNReal.ofReal (d1K S i) * (stateAt S π ω T i s l : ℝ≥0∞) :=
          Finset.sum_le_sum fun l _ => by
            have := ENNReal.ofReal_le_ofReal (d1_f_le S hS sel i s l)
            unfold qF
            gcongr
      _ = ENNReal.ofReal (d1K S i) *
            ((∑ l ∈ Finset.range (S.L i), stateAt S π ω T i s l : ℕ) : ℝ≥0∞) := by
          rw [Nat.cast_sum, Finset.mul_sum]
      _ ≤ _ := by gcongr
  · have h1 : qF S i s l ≤ qK S * ENNReal.ofReal (S.W i) :=
      (ENNReal.ofReal_le_ofReal (d1_f_le S hS sel i s l)).trans (q_K_le S hS i)
    calc qF S i s l * (stateAt S π ω T i s l : ℝ≥0∞)
        ≤ (qK S * ENNReal.ofReal (S.W i)) * (stateAt S π ω T i s l : ℝ≥0∞) := by gcongr
      _ = _ := by ring

theorem q_phi_int (S : System) (hS : Standing S) (sel : Selection S) (π : Policy S)
    (lam : Fin S.I → ℝ≥0) (T : ℕ) :
    ∫⁻ ω, qPhi S π ω T ∂(sampleMeasure S lam) ≤
      qB S lam + qK S * ∫⁻ ω, periodCost S S.R S.R π ω T ∂(sampleMeasure S lam) := by
  have hmN : ∀ (i : Fin S.I) (t : ℕ), Measurable fun ω : Omega S => (ω.1 (i, t) : ℝ≥0∞) :=
    fun i t => measurable_from_nat.comp ((measurable_pi_apply (i, t)).comp measurable_fst)
  have hmP : Measurable fun ω : Omega S => ∑ i, ∑ s ∈ (Finset.range T).filter (fun s => s < S.δ i),
      ENNReal.ofReal (d1K S i) * (ω.1 (i, T - s) : ℝ≥0∞) :=
    Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun s _ => (hmN i _).const_mul _
  refine (lintegral_mono fun ω => q_phi_pt S hS sel π ω T).trans ?_
  rw [lintegral_add_left hmP, lintegral_const_mul' _ _ (q_K_ne_top S hS)]
  gcongr
  rw [lintegral_finsetSum _ fun i _ => Finset.measurable_sum _ fun s _ => (hmN i _).const_mul _]
  unfold qB
  refine Finset.sum_le_sum fun i _ => ?_
  rw [lintegral_finsetSum _ fun s _ => (hmN i _).const_mul _]
  have he : ∀ s, ∫⁻ ω, ENNReal.ofReal (d1K S i) * (ω.1 (i, T - s) : ℝ≥0∞)
      ∂(sampleMeasure S lam) = ENNReal.ofReal (d1K S i) * lam i := fun s => by
    rw [lintegral_const_mul _ (hmN i _), c1_E_N]
  simp only [he, Finset.sum_const, nsmul_eq_mul]
  have hcard : ((Finset.range T).filter (fun s => s < S.δ i)).card ≤ S.δ i := by
    calc _ ≤ (Finset.range (S.δ i)).card :=
          Finset.card_le_card (fun s hs => by simp only [Finset.mem_filter, Finset.mem_range] at hs ⊢; omega)
      _ = S.δ i := Finset.card_range _
  have hcard' : ((((Finset.range T).filter (fun s => s < S.δ i)).card : ℕ) : ℝ≥0∞) ≤
      (S.δ i : ℝ≥0∞) := by exact_mod_cast hcard
  calc ((((Finset.range T).filter (fun s => s < S.δ i)).card : ℕ) : ℝ≥0∞) *
        (ENNReal.ofReal (d1K S i) * lam i)
      ≤ (S.δ i : ℝ≥0∞) * (ENNReal.ofReal (d1K S i) * lam i) := by gcongr
    _ = _ := by ring

theorem q_LB (S : System) (hS : Standing S) (sel : Selection S) (lam : Fin S.I → ℝ≥0)
    (π : Policy S) : e8CF S sel lam ≤ avgCost S S.R S.R lam π := by
  refine (e9_CF_le S hS sel lam).trans ?_
  have hΛ : ∑ i, ENNReal.ofReal ((lam i : ℝ) * fDP S i 0 0) =
      ∑ i, qF S i 0 0 * (lam i : ℝ≥0∞) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold qF
    rw [ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal, mul_comm]
  rw [hΛ]
  unfold avgCost
  refine h_liminf (fun n => ∫⁻ ω, periodCost S S.R S.R π ω n ∂(sampleMeasure S lam)) _ (qK S)
    (qB S lam) ?_ (q_K_ne_top S hS) (q_B_ne_top S lam) fun T => ?_
  · exact ENNReal.sum_ne_top.2 fun i _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top
  · show (T : ℝ≥0∞) * ∑ i, qF S i 0 0 * (lam i : ℝ≥0∞) ≤
      ∑ n ∈ Finset.range T, ∫⁻ ω, periodCost S S.R S.R π ω n ∂(sampleMeasure S lam) + qB S lam +
        qK S * ∫⁻ ω, periodCost S S.R S.R π ω T ∂(sampleMeasure S lam)
    calc (T : ℝ≥0∞) * ∑ i, qF S i 0 0 * (lam i : ℝ≥0∞)
        ≤ ∑ n ∈ Finset.range T, ∫⁻ ω, periodCost S S.R S.R π ω n ∂(sampleMeasure S lam) +
            ∫⁻ ω, qPhi S π ω T ∂(sampleMeasure S lam) := q_cum S hS sel π lam T
      _ ≤ ∑ n ∈ Finset.range T, ∫⁻ ω, periodCost S S.R S.R π ω n ∂(sampleMeasure S lam) +
            (qB S lam + qK S * ∫⁻ ω, periodCost S S.R S.R π ω T ∂(sampleMeasure S lam)) :=
          add_le_add le_rfl (q_phi_int S hS sel π lam T)
      _ = _ := by ring
end CloudCostOpt

open MeasureTheory ProbabilityTheory Filter Topology NNReal ENNReal CloudCostOpt in
theorem solution (S : System) (hS : Standing S) (sel : Selection S)
    (lam : Fin S.I → ℝ≥0) (hlam : ∀ i, 0 < lam i) :
    IsStable S lam (piHat S sel) ∧
    avgCost S S.R S.R lam (piHat S sel) =
      ∑ j, ENNReal.ofReal (S.R j) * mu S sel lam j +
      ∑ i, ∑' k : ℕ, ∑ l ∈ Finset.range (S.L i),
        ENNReal.ofReal (S.W i) * (rateX S sel lam i (S.δ i + k) l : ℝ≥0∞) ∧
    opt S S.R S.R lam = avgCost S S.R S.R lam (piHat S sel) := by
  exact e8_of_lb S hS sel lam (fun π => q_LB S hS sel lam π)
