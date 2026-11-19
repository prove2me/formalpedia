-- Prove2me | solution 1 for BilateralProfitRegular.lemma_6_5
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-18T15:53:05.306356+00:00
-- url     : https://prove2.me/submissions/af8f41cd-d469-463a-82f8-a0ac77f65a33

import Mathlib
import Definitions.Def_BilateralProfitRegular_Proc
import Theorems.Thm_BilateralProfitMHR_positive_density_profit_facts
import Definitions.Def_BilateralProfitRegular_Stochastic
import Definitions.Def_BilateralProfitRegular_Auxiliary
import Definitions.Def_BilateralProfitRegular_InitRegular


section BundlePart000


namespace BilateralProfitRegular.Factory

/-- The upper endpoint of the walk at stage `j`. -/
private def boundary (j : ℕ) : ℕ := 24 * 2 ^ j

/-- The multiplier of the target odds at stage `j`. -/
private noncomputable def scale (j : ℕ) : ℝ := 3 / 2 - 1 / (2 * 2 ^ j)

@[simp]
private theorem boundary_succ (j : ℕ) : boundary (j + 1) = 2 * boundary j := by
  simp only [boundary, pow_succ]
  ring

private theorem boundary_pos (j : ℕ) : 0 < boundary j := by unfold boundary; positivity

@[simp]
private theorem scale_zero : scale 0 = 1 := by norm_num [scale]

private theorem scale_one_le (j : ℕ) : 1 ≤ scale j := by
  have h : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  unfold scale
  have h' : 1 / (2 * (2 : ℝ) ^ j) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num)
    linarith
  linarith

private theorem scale_le (j : ℕ) : scale j ≤ 3 / 2 := by
  unfold scale
  have : 0 ≤ 1 / (2 * (2 : ℝ) ^ j) := by positivity
  linarith

private theorem scale_pos (j : ℕ) : 0 < scale j := lt_of_lt_of_le zero_lt_one (scale_one_le j)

private theorem scale_succ_sub (j : ℕ) : scale (j + 1) - scale j = 1 / (4 * 2 ^ j) := by
  unfold scale
  rw [pow_succ]
  have h : (2 : ℝ) ^ j ≠ 0 := by positivity
  field_simp
  ring

/-- Probability of reaching the next stage, conditional on reaching the upper endpoint. -/
private noncomputable def survival (j : ℕ) : ℝ := (scale j / scale (j + 1)) ^ boundary j

private theorem survival_nonneg (j : ℕ) : 0 ≤ survival j := by
  unfold survival
  exact pow_nonneg (div_nonneg (scale_pos j).le (scale_pos (j + 1)).le) _

private theorem survival_le (j : ℕ) : survival j ≤ 1 / 5 := by
  have hpos := scale_pos j
  have hpos' := scale_pos (j + 1)
  have hpow : (0 : ℝ) < 2 ^ j := by positivity
  have hdelta : 1 / (6 * 2 ^ j) ≤ scale (j + 1) / scale j - 1 := by
    rw [le_sub_iff_add_le, le_div_iff₀ hpos, add_mul, one_mul]
    rw [← le_sub_iff_add_le, scale_succ_sub]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * 2 ^ j)).mpr
    calc
      1 / (6 * (2 : ℝ) ^ j) * scale j * (4 * 2 ^ j)
        = scale j * (2 / 3) := by field_simp; ring
      _ ≤ 1 := by linarith [scale_le j]
  have hd : 0 ≤ scale (j + 1) / scale j - 1 :=
    (by positivity : 0 ≤ 1 / (6 * (2 : ℝ) ^ j)).trans hdelta
  have hBern := one_add_mul_le_pow (by linarith : -2 ≤ scale (j + 1) / scale j - 1) (boundary j)
  have hb : (5 : ℝ) ≤ (scale (j + 1) / scale j) ^ boundary j := by
    calc
      5 = 1 + (boundary j : ℝ) * (1 / (6 * (2 : ℝ) ^ j)) := by
        simp only [boundary, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
        field_simp
        ring
      _ ≤ 1 + (boundary j : ℝ) * (scale (j + 1) / scale j - 1) := by gcongr
      _ ≤ _ := by simpa using hBern
  rw [survival, ← inv_div, inv_pow, one_div]
  exact (inv_le_inv₀ (pow_pos (div_pos hpos' hpos) _) (by norm_num)).2 hb

/-- States are completed answers or a stage and a walk position. -/
private abbrev State := Bool ⊕ (ℕ × ℕ)

private def admissible : State → Prop
  | .inl _ => True
  | .inr (j, k) => 0 < k ∧ k < boundary j

/-- Downward moves hit the successful endpoint at zero. -/
private def down (j k : ℕ) : State :=
  if k = 1 then .inl true else .inr (j, k - 1)

/-- Upward moves reaching the upper endpoint either go up a stage or terminate. -/
private def up (j k : ℕ) : State :=
  if k + 1 = boundary j then .inr (j + 1, k + 1) else .inr (j, k + 1)

private noncomputable def continueUp (j k : ℕ) : ℝ :=
  if k + 1 = boundary j then survival j else 1

private theorem continueUp_nonneg (j k : ℕ) : 0 ≤ continueUp j k := by
  unfold continueUp
  split
  · exact survival_nonneg j
  · norm_num

private theorem continueUp_le_one (j k : ℕ) : continueUp j k ≤ 1 := by
  unfold continueUp
  split
  · linarith [survival_le j]
  · rfl

private theorem admissible_down {j k : ℕ} (hk : admissible (.inr (j,k))) :
    admissible (down j k) := by
  rcases hk with ⟨hpos, hlt⟩
  unfold down
  split <;> simp only [admissible]
  exact ⟨by omega, by omega⟩

private theorem admissible_up {j k : ℕ} (hk : admissible (.inr (j,k))) :
    admissible (up j k) := by
  rcases hk with ⟨hpos, hlt⟩
  unfold up
  split <;> simp only [admissible, boundary_succ] <;> omega

/-- The function whose expectation is preserved at each update. -/
private noncomputable def value (a b : ℝ) : State → ℝ
  | .inl true => 1
  | .inl false => 0
  | .inr (j,k) => (scale j * a / b) ^ k

/-- A bound on remaining expected physical queries. -/
private noncomputable def budget (b : ℝ) : State → ℝ
  | .inl _ => 0
  | .inr (j,k) => 6 / b * (2 * boundary j - k)

private theorem value_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (s : State) :
    0 ≤ value a b s := by
  rcases s with (d | ⟨j,k⟩)
  · cases d <;> norm_num [value]
  · exact pow_nonneg (div_nonneg (mul_nonneg (scale_pos j).le ha) hb.le) _

private theorem value_le_one {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hab : 2 * a ≤ b)
    (s : State) : value a b s ≤ 1 := by
  rcases s with (d | ⟨j,k⟩)
  · cases d <;> norm_num [value]
  · simp only [value]
    apply pow_le_one₀ (div_nonneg (mul_nonneg (scale_pos j).le ha) hb.le)
    apply (div_le_iff₀ hb).mpr
    calc
      scale j * a ≤ (3 / 2) * a := mul_le_mul_of_nonneg_right (scale_le j) ha
      _ ≤ 1 * b := by linarith

private theorem budget_nonneg {b : ℝ} (hb : 0 < b) {s : State} (hs : admissible s) :
    0 ≤ budget b s := by
  rcases s with (_ | ⟨j,k⟩)
  · norm_num [budget]
  · have hk : (k : ℝ) ≤ boundary j := by exact_mod_cast hs.2.le
    have hN : (0 : ℝ) ≤ boundary j := by positivity
    exact mul_nonneg (by positivity) (by linarith)

private theorem value_down {a b : ℝ} {j k : ℕ} :
    value a b (down j k) = (scale j * a / b) ^ (k - 1) := by
  unfold down
  split
  · simp_all [value]
  · rfl

private theorem value_up {a b : ℝ} {j k : ℕ} :
    continueUp j k * value a b (up j k) = (scale j * a / b) ^ (k + 1) := by
  unfold continueUp up
  split
  · rename_i hk
    simp only [hk, survival, value]
    rw [← hk, ← mul_pow]
    have := (scale_pos (j + 1)).ne'
    congr 1
    field_simp
  · rename_i hk
    simp [value]

private theorem budget_down {b : ℝ} (hb : 0 < b) {j k : ℕ} :
    budget b (down j k) ≤ 6 / b * (2 * boundary j - (k - 1 : ℕ)) := by
  unfold down
  split
  · rename_i hk
    subst k
    simpa [budget] using (by positivity : 0 ≤ (6 / b) * (2 * (boundary j : ℝ)))
  · rfl

private theorem budget_up {b : ℝ} (hb : 0 < b) {j k : ℕ} :
    continueUp j k * budget b (up j k) ≤ 6 / b * (2 * boundary j - (k + 1 : ℕ)) := by
  unfold continueUp up
  split
  · rename_i hk
    simp only [hk, budget, Nat.cast_ofNat, boundary_succ, Nat.cast_mul]
    have hN : (0 : ℝ) ≤ boundary j := by positivity
    have hs := survival_le j
    have h₆ : 0 ≤ 6 / b := by positivity
    calc
      survival j * (6 / b * (2 * (2 * boundary j) - boundary j))
        ≤ (1 / 5) * (6 / b * (2 * (2 * boundary j) - boundary j)) := by
          gcongr
          exact mul_nonneg h₆ (by linarith)
      _ ≤ _ := by
        nlinarith [mul_nonneg h₆ hN]
  · rename_i hk
    simp [budget]

/-- Real-valued one-step expectation for the stopped walk. -/
private noncomputable def expectation (a b : ℝ) (f : State → ℝ) : State → ℝ
  | .inl d => f (.inl d)
  | .inr (j,k) =>
    a * f (down j k) +
    b / scale j * (continueUp j k * f (up j k) + (1 - continueUp j k) * f (.inl false)) +
    (1 - a - b / scale j) * f (.inr (j,k))

private theorem expectation_value {a b : ℝ} (hb : 0 < b) {s : State} (hs : admissible s) :
    expectation a b (value a b) s = value a b s := by
  rcases s with (_ | ⟨j,k⟩)
  · rfl
  · have hk : 0 < k := hs.1
    rw [expectation, value_down]
    simp only [show value a b (.inl false) = 0 from rfl, mul_zero, add_zero, value_up]
    change _ * _ + _ * _ + _ * (scale j * a / b) ^ k = (scale j * a / b) ^ k
    have hh : (scale j * a / b) ^ k =
        (scale j * a / b) ^ (k - 1) * (scale j * a / b) := by
      conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
    rw [pow_succ, hh]
    have hsj := (scale_pos j).ne'
    field_simp
    ring

private noncomputable def running : State → ℝ
  | .inl _ => 0
  | .inr _ => 1

private theorem expectation_budget {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hab : 2 * a ≤ b)
    {s : State} (hs : admissible s) :
    expectation a b (budget b) s + running s ≤ budget b s := by
  rcases s with (_ | ⟨j,k⟩)
  · simp [expectation, budget, running]
  · have hk : 0 < k := hs.1
    have hq : 0 ≤ b / scale j := div_nonneg hb.le (scale_pos j).le
    have hdiff : b / 6 ≤ b / scale j - a := by
      have h : (2 / 3 : ℝ) * b ≤ b / scale j := by
        apply (le_div_iff₀ (scale_pos j)).mpr
        calc
          (2 / 3) * b * scale j ≤ (2 / 3) * b * (3 / 2) := by gcongr; exact scale_le j
          _ = b := by ring
      linarith
    rw [expectation]
    simp only [running, show budget b (.inl false) = 0 from rfl, mul_zero, add_zero]
    change _ * _ + _ * _ + _ * (6 / b * (2 * boundary j - k)) + 1 ≤
      6 / b * (2 * boundary j - k)
    have h₁ := mul_le_mul_of_nonneg_left (budget_down (j := j) (k := k) hb) ha
    have h₂ := mul_le_mul_of_nonneg_left (budget_up (j := j) (k := k) hb) hq
    have hkm : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      simpa using (Nat.cast_sub (R := ℝ) (show 1 ≤ k by omega))
    rw [hkm] at h₁
    push_cast at h₂
    have hbudget : 1 ≤ 6 / b * (b / scale j - a) := by
      calc
        1 = 6 / b * (b / 6) := by field_simp
        _ ≤ _ := by gcongr
    calc
      _ ≤ a * (6 / b * (2 * boundary j - ((k : ℝ) - 1))) +
          b / scale j * (6 / b * (2 * boundary j - (k + 1))) +
          (1 - a - b / scale j) * (6 / b * (2 * boundary j - k)) + 1 := by linarith
      _ = 6 / b * (2 * boundary j - k) - 6 / b * (b / scale j - a) + 1 := by ring
      _ ≤ _ := by linarith

end BilateralProfitRegular.Factory
end BundlePart000


section BundlePart001



namespace BilateralProfitRegular.Factory

open MeasureTheory ProbabilityTheory

private abbrev Uniform := unitInterval
private abbrev Stream := ℕ → Uniform
private abbrev Input := Uniform × Uniform

private instance : MeasurableSingletonClass State where
  measurableSet_singleton s := by
    rcases s with (d | jk) <;> simp [measurableSet_sum_iff, Set.preimage]


private noncomputable def inputLaw : Measure Input :=
  (volume : Measure Uniform).prod volume

private instance : IsProbabilityMeasure inputLaw := by
  unfold inputLaw
  infer_instance

private instance : IsProbabilityMeasure Proc.coinLaw := by
  unfold Proc.coinLaw
  infer_instance

private def pairAt (x : Stream × Stream) (n : ℕ) : Input := (x.1 n, x.2 n)

@[fun_prop]
private theorem measurable_pairAt : Measurable pairAt := by
  unfold pairAt
  fun_prop

private theorem paired_law : (Proc.law Proc.coinLaw).map pairAt =
    Measure.infinitePi (fun _ : ℕ => inputLaw) := by
  have e₁ := (measurePreserving_finTwoArrow Proc.coinLaw).map_eq
  rw [← Measure.infinitePi_eq_pi] at e₁
  rw [Proc.law, ← e₁, Measure.map_map measurable_pairAt (by fun_prop)]
  have hcomp : pairAt ∘ MeasurableEquiv.finTwoArrow =
      (fun (x : ℕ → Fin 2 → Uniform) n => MeasurableEquiv.finTwoArrow (x n)) ∘
      (MeasurableEquiv.curry ℕ (Fin 2) Uniform) ∘
      (MeasurableEquiv.piCongrLeft (fun _ => Uniform) (Equiv.prodComm (Fin 2) ℕ)) ∘
      (MeasurableEquiv.curry (Fin 2) ℕ Uniform).symm := by
    ext x n <;> rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_map (by fun_prop) (by fun_prop)]
  unfold Proc.coinLaw
  rw [Measure.infinitePi_map_curry_symm,
    Measure.infinitePi_map_piCongrLeft (fun _ : ℕ × Fin 2 => (volume : Measure Uniform))
      (Equiv.prodComm (Fin 2) ℕ),
    Measure.infinitePi_map_curry (fun (_ : ℕ) (_ : Fin 2) => (volume : Measure Uniform)),
    Measure.infinitePi_map_pi (f := fun (_ : ℕ) => MeasurableEquiv.finTwoArrow) _ (by fun_prop)]
  congr 1
  funext n
  rw [Measure.infinitePi_eq_pi]
  exact (measurePreserving_finTwoArrow (volume : Measure Uniform)).map_eq

/-- A mixing rule takes a fresh observed bit and specifies the weights for the two
possible directions before applying the stage-dependent scaling. -/
private structure Mixing where
  downWeight : Bool → ℝ
  upWeight : Bool → ℝ
  down_nonneg : ∀ t, 0 ≤ downWeight t
  up_nonneg : ∀ t, 0 ≤ upWeight t
  sum_le_one : ∀ t, downWeight t + upWeight t ≤ 1

private noncomputable def mix (p : ℝ) (f : Bool → ℝ) : ℝ := p * f true + (1 - p) * f false

/-- Use one seed uniform to select the move and implement the thinning at a boundary. -/
private noncomputable def select (m : Mixing) (r : Uniform) (t : Bool) : State → State
  | .inl d => .inl d
  | .inr (j,k) =>
    let d := m.downWeight t
    let u := m.upWeight t / scale j
    if (r : ℝ) < d then down j k
    else if (r : ℝ) < d + u * continueUp j k then up j k
    else if (r : ℝ) < d + u then .inl false
    else .inr (j,k)

private theorem select_admissible (m : Mixing) (r : Uniform) (t : Bool) {s : State}
    (hs : admissible s) : admissible (select m r t s) := by
  rcases s with (d | ⟨j,k⟩)
  · trivial
  · simp only [select]
    split
    · exact admissible_down hs
    · split
      · exact admissible_up hs
      · split
        · trivial
        · exact hs

@[fun_prop]
private theorem measurable_select (m : Mixing) (t : Bool) (s : State) :
    Measurable (fun r => select m r t s) := by
  rcases s with (_ | ⟨j,k⟩)
  · exact measurable_const
  · simp only [select]
    refine Measurable.ite ?_ measurable_const (Measurable.ite ?_ measurable_const
      (Measurable.ite ?_ measurable_const measurable_const))
    all_goals exact measurableSet_lt (by fun_prop) measurable_const

/-- Interpret a uniform input as one seed value and one trade bit. -/
private noncomputable def update (m : Mixing) (p : ℝ) (s : State) (r : Input) : State :=
  select m r.1 (decide ((r.2 : ℝ) < p)) s

@[fun_prop]
private theorem measurable_update (m : Mixing) (p : ℝ) :
    Measurable (fun sr : State × Input => update m p sr.1 sr.2) := by
  refine measurable_from_prod_countable_right ?_
  intro s
  have heq : (fun r => update m p s r) =
      fun r : Input => if (r.2 : ℝ) < p then select m r.1 true s else select m r.1 false s := by
    funext r
    by_cases h : (r.2 : ℝ) < p <;> simp [update, h]
  rw [heq]
  exact Measurable.ite (measurableSet_lt (by fun_prop) measurable_const) (by fun_prop) (by fun_prop)

private theorem volume_lt {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1) :
    (volume : Measure Uniform) {r | (r : ℝ) < a} = ENNReal.ofReal a :=
  unitInterval.volume_Iio (⟨a, ha, ha'⟩ : Uniform)

private theorem integral_indicator_lt {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1) (v : ℝ) :
    ∫ r : Uniform, (if (r : ℝ) < a then v else 0) = a * v := by
  change ∫ r : Uniform, ({r : Uniform | (r : ℝ) < a} : Set Uniform).indicator (fun _ => v) r = _
  rw [integral_indicator (measurableSet_lt (by fun_prop) measurable_const), setIntegral_const,
    Measure.real, volume_lt ha ha', ENNReal.toReal_ofReal ha, smul_eq_mul]

private theorem integrable_select (m : Mixing) (t : Bool) (s : State) (f : State → ℝ) :
    Integrable (fun r : Uniform => f (select m r t s)) volume := by
  have hf : Measurable (fun r : Uniform => f (select m r t s)) :=
    (measurable_of_countable f).comp (measurable_select m t s)
  rcases s with (d | ⟨j,k⟩)
  · simpa only [select] using (integrable_const (μ := volume) (f (.inl d)) : Integrable _ (volume : Measure Uniform))
  · apply Integrable.of_bound hf.aestronglyMeasurable
      (max (max ‖f (down j k)‖ ‖f (up j k)‖) (max ‖f (.inl false)‖ ‖f (.inr (j,k))‖))
    refine Filter.Eventually.of_forall fun r => ?_
    simp only [select]
    split
    · exact (le_max_left _ _).trans (le_max_left _ _)
    · split
      · exact (le_max_right _ _).trans (le_max_left _ _)
      · split
        · exact (le_max_left _ _).trans (le_max_right _ _)
        · exact (le_max_right _ _).trans (le_max_right _ _)

private theorem integral_select (m : Mixing) (t : Bool) (f : State → ℝ) (s : State) :
    (∫ r : Uniform, f (select m r t s)) =
      expectation (m.downWeight t) (m.upWeight t) f s := by
  rcases s with (d | ⟨j,k⟩)
  · simp [select, expectation]
  · let d := m.downWeight t
    let u := m.upWeight t / scale j
    let h := continueUp j k
    have hd : 0 ≤ d := m.down_nonneg t
    have hu : 0 ≤ u := div_nonneg (m.up_nonneg t) (scale_pos j).le
    have hh : 0 ≤ h := continueUp_nonneg j k
    have hh' : h ≤ 1 := continueUp_le_one j k
    have hdu : d + u ≤ 1 := by
      have hu' : u ≤ m.upWeight t := div_le_self (m.up_nonneg t) (scale_one_le j)
      linarith [m.sum_le_one t]
    have hh₁ : d ≤ d + u*h := by nlinarith
    have hh₂ : d + u*h ≤ d+u := by nlinarith
    let k₁ := f (down j k) - f (up j k)
    let k₂ := f (up j k) - f (.inl false)
    let k₃ := f (.inl false) - f (.inr (j,k))
    have heq : (fun r : Uniform => f (select m r t (.inr (j,k)))) = fun r : Uniform =>
        (if (r : ℝ) < d then k₁ else 0) + (if (r : ℝ) < d + u*h then k₂ else 0) +
        (if (r : ℝ) < d + u then k₃ else 0) + f (.inr (j,k)) := by
      funext r
      change f (if (r : ℝ) < d then down j k else if (r : ℝ) < d + u*h then up j k
        else if (r : ℝ) < d+u then .inl false else .inr (j,k)) = _
      by_cases h₁ : (r : ℝ) < d
      · simp [h₁, h₁.trans_le hh₁, h₁.trans_le (hh₁.trans hh₂), k₁, k₂, k₃]
      · by_cases h₂ : (r : ℝ) < d+u*h
        · simp [h₁, h₂, h₂.trans_le hh₂, k₂, k₃]
        · by_cases h₃ : (r : ℝ) < d+u <;> simp [h₁, h₂, h₃, k₃]
    have hi (a v : ℝ) : Integrable (fun r : Uniform => if (r : ℝ) < a then v else 0) volume := by
      change Integrable (({r : Uniform | (r : ℝ) < a} : Set Uniform).indicator (fun _ => v)) volume
      exact (integrable_const v).indicator (measurableSet_lt (by fun_prop) measurable_const)
    have hAdd₁ := integral_add (hi d k₁) (hi (d+u*h) k₂)
    have hAdd₂ := integral_add ((hi d k₁).add (hi (d+u*h) k₂)) (hi (d+u) k₃)
    have hAdd₃ := integral_add ((hi d k₁).add (hi (d+u*h) k₂) |>.add (hi (d+u) k₃))
      (integrable_const (f (.inr (j,k))))
    simp only [Pi.add_apply] at hAdd₁ hAdd₂ hAdd₃
    rw [heq, hAdd₃, hAdd₂, hAdd₁]
    rw [integral_indicator_lt hd ((hh₁.trans hh₂).trans hdu),
      integral_indicator_lt (hd.trans hh₁) (hh₂.trans hdu),
      integral_indicator_lt (hd.trans (hh₁.trans hh₂)) hdu]
    simp only [integral_const, probReal_univ, one_smul, expectation]
    change d*k₁ + (d+u*h)*k₂ + (d+u)*k₃ + f (.inr (j,k)) = _
    change _ = d * f (down j k) + u * (h * f (up j k) + (1 - h) * f (.inl false)) +
      (1 - d - u) * f (.inr (j,k))
    dsimp [k₁, k₂, k₃]
    ring

private theorem integral_update (m : Mixing) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (f : State → ℝ)
    (s : State) :
    (∫ r, f (update m p s r) ∂inputLaw) =
      expectation (mix p m.downWeight) (mix p m.upWeight) f s := by
  let F := fun r : Input => f (select m r.1 true s)
  let G := fun r : Input => f (select m r.1 false s)
  have hF : Integrable F inputLaw := (integrable_select m true s f).comp_fst volume
  have hG : Integrable G inputLaw := (integrable_select m false s f).comp_fst volume
  have heq : (fun r => f (update m p s r)) =
      fun r : Input => (if (r.2 : ℝ) < p then F r - G r else 0) + G r := by
    funext r
    by_cases h : (r.2 : ℝ) < p <;> simp [update, h, F, G]
  have hdiff : Integrable (fun r : Input => if (r.2 : ℝ) < p then F r - G r else 0) inputLaw := by
    change Integrable (({r : Input | (r.2 : ℝ) < p} : Set Input).indicator (fun r => F r - G r)) inputLaw
    exact (hF.sub hG).indicator (measurableSet_lt (by fun_prop) measurable_const)
  have hfg : Integrable (fun r => f (update m p s r)) inputLaw := heq ▸ (hdiff.add hG)
  unfold inputLaw at hfg ⊢
  rw [integral_prod _ hfg]
  have inner (r : Uniform) :
      (∫ t : Uniform, f (update m p s (r,t))) =
        p * f (select m r true s) + (1 - p) * f (select m r false s) := by
    change (∫ t : Uniform, (fun r => f (update m p s r)) (r,t)) = _
    rw [heq]
    simp only [F, G]
    rw [integral_add _ (integrable_const _), integral_indicator_lt hp hp']
    · simp [integral_const]; ring
    · change Integrable (({t : Uniform | (t : ℝ) < p} : Set Uniform).indicator (fun _ =>
        f (select m r true s) - f (select m r false s))) volume
      exact (integrable_const _).indicator (measurableSet_lt (by fun_prop) measurable_const)
  simp_rw [inner]
  rw [integral_add ((integrable_select m true s f).const_mul p)
    ((integrable_select m false s f).const_mul (1 - p)),
    integral_const_mul, integral_const_mul, integral_select, integral_select]
  rcases s with (d | ⟨j,k⟩) <;> simp only [expectation, mix] <;> ring

end BilateralProfitRegular.Factory
end BundlePart001


section BundlePart002


namespace BilateralProfitRegular.Factory

open Classical MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

/-- The real indicator for a trade bit with bias `p`. -/
private noncomputable def hit (p : ℝ) (u : Uniform) : ℝ := if (u : ℝ) < p then 1 else 0

@[fun_prop]
private theorem measurable_hit (p : ℝ) : Measurable (hit p) :=
  Measurable.ite (measurableSet_lt measurable_subtype_coe measurable_const)
    measurable_const measurable_const

private theorem hit_nonneg (p : ℝ) (u : Uniform) : 0 ≤ hit p u := by unfold hit; split <;> norm_num

private theorem hit_le_one (p : ℝ) (u : Uniform) : hit p u ≤ 1 := by unfold hit; split <;> norm_num

private theorem bernoulli_mgf_le {p lam : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (hlam : |lam| ≤ 1) :
    (∫ u : Uniform, Real.exp (lam * (hit p u - p))) ≤ Real.exp (p * lam^2) := by
  let a := Real.exp (lam * (1-p))
  let b := Real.exp (lam * (0-p))
  have heq : (fun u : Uniform => Real.exp (lam * (hit p u - p))) =
      fun u : Uniform => (if (u : ℝ) < p then a-b else 0) + b := by
    funext u
    by_cases h : (u : ℝ) < p <;> simp [hit, h, a,b]
  have hi : Integrable (fun u : Uniform => if (u : ℝ) < p then a-b else 0) volume := by
    change Integrable (({u : Uniform | (u : ℝ) < p} : Set Uniform).indicator (fun _ => a-b)) volume
    exact (integrable_const _).indicator (measurableSet_lt measurable_subtype_coe measurable_const)
  rw [heq]
  have hAdd := integral_add hi (integrable_const b)
  rw [hAdd, integral_indicator_lt hp hp', integral_const, probReal_univ, one_smul]
  have h := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hlam)).2
  calc
    _ = Real.exp (-lam*p) * (1+p*(Real.exp lam-1)) := by
      dsimp [a,b]
      rw [show lam*(1-p) = -lam*p + lam by ring, Real.exp_add]
      simp only [zero_sub]
      rw [show lam * -p = -lam*p by ring]
      ring
    _ ≤ Real.exp (-lam*p) * Real.exp (p * (lam+lam^2)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      calc
        _ ≤ 1 + p * (lam + lam^2) := by
          nlinarith [mul_nonneg hp (show 0 ≤ lam^2 - (Real.exp lam - 1 - lam) by linarith)]
        _ ≤ _ := by linarith only [Real.add_one_le_exp (p * (lam + lam^2))]
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- Number of trades in a block indexed by distinct coordinates of the uniform stream. -/
private noncomputable def hitCount {n : ℕ} (p : ℝ) (coord : Fin n → ℕ) (U : Stream) : ℝ :=
  ∑ i, hit p (U (coord i))

@[fun_prop]
private theorem measurable_hitCount {n : ℕ} (p : ℝ) (coord : Fin n → ℕ) :
    Measurable (hitCount p coord) := by
  unfold hitCount
  exact Finset.measurable_fun_sum _ fun i _ => (measurable_hit p).comp (measurable_pi_apply _)

private theorem hitCount_bounds {n : ℕ} (p : ℝ) (coord : Fin n → ℕ) (U : Stream) :
    0 ≤ hitCount p coord U ∧ hitCount p coord U ≤ n := by
  constructor
  · exact Finset.sum_nonneg fun _ _ => hit_nonneg _ _
  · calc
      _ ≤ ∑ _ : Fin n, (1 : ℝ) := Finset.sum_le_sum fun _ _ => hit_le_one _ _
      _ = _ := by simp

private theorem hitCount_mgf_le {n : ℕ} {p lam : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (hlam : |lam| ≤ 1)
    (coord : Fin n → ℕ) (hc : Function.Injective coord) :
    (∫ U, Real.exp (lam * (hitCount p coord U - n*p)) ∂Proc.coinLaw) ≤
      Real.exp (n*p*lam^2) := by
  have hi : iIndepFun (fun i (U : Stream) => U (coord i)) Proc.coinLaw :=
    (iIndepFun_infinitePi (X := fun (_ : ℕ) (u : Uniform) => u) (by fun_prop)).precomp hc
  let f := fun u : Uniform => Real.exp (lam * (hit p u - p))
  have hfm : Measurable f := Real.measurable_exp.comp ((measurable_hit p).sub_const p |>.const_mul lam)
  have heq : (fun U : Stream => Real.exp (lam * (hitCount p coord U - n*p))) =
      fun U => ∏ i, f (U (coord i)) := by
    funext U
    change _ = ∏ i, Real.exp (lam * (hit p (U (coord i)) - p))
    rw [← Real.exp_sum]
    congr 1
    simp only [hitCount, mul_sub, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [heq, hi.integral_fun_prod_comp
    (fun i => (measurable_pi_apply (coord i)).aemeasurable)
    (fun _ => hfm.aestronglyMeasurable)]
  have hiaval (i : Fin n) :
      (∫ U, f (U (coord i)) ∂Proc.coinLaw) = ∫ u, f u ∂(volume : Measure Uniform) := by
    rw [← integral_map (measurable_pi_apply (coord i)).aemeasurable hfm.aestronglyMeasurable]
    exact congrArg (fun μ => ∫ u, f u ∂μ) (Measure.infinitePi_map_eval _ _)
  simp_rw [hiaval]
  calc
    _ ≤ ∏ _ : Fin n, Real.exp (p*lam^2) :=
      Finset.prod_le_prod (fun _ _ => integral_nonneg fun _ => Real.exp_nonneg _)
        (fun _ _ => bernoulli_mgf_le hp hp' hlam)
    _ = _ := by simp [Real.exp_nat_mul, mul_assoc]

private theorem hitCount_tail_one_side {n : ℕ} {p ε s : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (hε : 0 ≤ ε) (hε' : ε ≤ 1) (hs : s = 1 ∨ s = -1)
    (coord : Fin n → ℕ) (hc : Function.Injective coord) :
    Proc.coinLaw {U | ε * n * p ≤ s * (hitCount p coord U - n*p)} ≤
      ENNReal.ofReal (Real.exp (-(n*p*ε^2/4))) := by
  let lam := s * ε / 2
  let Z := fun U : Stream => Real.exp (lam * (hitCount p coord U - n*p))
  let t := Real.exp (n*p*ε^2/2)
  have ht : 0 < t := Real.exp_pos _
  have hlam : |lam| ≤ 1 := by rcases hs with rfl | rfl <;>
    simp [lam, abs_div, abs_of_nonneg hε] <;> linarith
  have hZ : Measurable Z :=
    Real.measurable_exp.comp ((measurable_hitCount p coord).sub_const _ |>.const_mul lam)
  have hZint : Integrable Z Proc.coinLaw := by
    apply Integrable.of_bound hZ.aestronglyMeasurable (Real.exp (|lam| * n))
    refine Filter.Eventually.of_forall fun U => ?_
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
    have hcount := hitCount_bounds p coord U
    have hn : 0 ≤ (n : ℝ) := by positivity
    have hn' : (n : ℝ) * p ≤ n := by nlinarith
    have hb : |hitCount p coord U - n*p| ≤ n := abs_le.mpr ⟨by nlinarith, by nlinarith⟩
    exact (le_abs_self _).trans (by rw [abs_mul]; gcongr)
  have hmgf := hitCount_mgf_le hp hp' hlam coord hc
  have hlamsq : lam^2 = ε^2/4 := by rcases hs with rfl | rfl <;> dsimp [lam] <;> ring
  have hset : {U | ε * n * p ≤ s * (hitCount p coord U - n*p)} ⊆
      {U | ENNReal.ofReal t ≤ ENNReal.ofReal (Z U)} := by
    intro U hU
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hU (show 0 ≤ ε/2 by positivity)
    dsimp [lam]
    nlinarith
  calc
    _ ≤ Proc.coinLaw {U | ENNReal.ofReal t ≤ ENNReal.ofReal (Z U)} := measure_mono hset
    _ ≤ (∫⁻ U, ENNReal.ofReal (Z U) ∂Proc.coinLaw) / ENNReal.ofReal t :=
      meas_ge_le_lintegral_div (ENNReal.measurable_ofReal.comp hZ).aemeasurable
        (by simpa using ht) ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (Real.exp (n*p*lam^2)) / ENNReal.ofReal t := by
      rw [← ofReal_integral_eq_lintegral_ofReal hZint (Filter.Eventually.of_forall (fun U => Real.exp_nonneg _))]
      exact ENNReal.div_le_div_right (ENNReal.ofReal_le_ofReal hmgf) _
    _ = _ := by
      rw [← ENNReal.ofReal_div_of_pos ht, hlamsq]
      dsimp [t]
      rw [← Real.exp_sub]
      congr 2
      ring

private theorem hitCount_relative_tail {n : ℕ} {p ε : ℝ} (hn : 0 < n) (hp : 0 < p) (hp' : p ≤ 1)
    (hε : 0 ≤ ε) (hε' : ε ≤ 1) (coord : Fin n → ℕ) (hc : Function.Injective coord) :
    Proc.coinLaw {U | ε < |(hitCount p coord U / n) / p - 1|} ≤
      2 * ENNReal.ofReal (Real.exp (-(n*p*ε^2/4))) := by
  let A : Set Stream := {U | ε * n * p ≤ (1 : ℝ) * (hitCount p coord U - n*p)}
  let B : Set Stream := {U | ε * n * p ≤ (-1 : ℝ) * (hitCount p coord U - n*p)}
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hset : {U | ε < |(hitCount p coord U / n) / p - 1|} ⊆ A ∪ B := by
    intro U hU
    change ε < |(hitCount p coord U / n) / p - 1| at hU
    have den : 0 < (n : ℝ)*p := mul_pos hn' hp
    rw [div_div, show hitCount p coord U / ((n : ℝ)*p) - 1 =
      (hitCount p coord U - n*p) / (n*p) by field_simp, abs_div, abs_of_pos den,
      lt_div_iff₀ den] at hU
    rcases lt_abs.mp hU with h | h
    · left
      change ε * n * p ≤ (1 : ℝ) * (hitCount p coord U - n*p)
      nlinarith
    · right
      change ε * n * p ≤ (-1 : ℝ) * (hitCount p coord U - n*p)
      nlinarith
  calc
    _ ≤ Proc.coinLaw (A ∪ B) := measure_mono hset
    _ ≤ Proc.coinLaw A + Proc.coinLaw B := measure_union_le _ _
    _ ≤ _ := by
      rw [two_mul]
      exact add_le_add (hitCount_tail_one_side hp.le hp' hε hε' (.inl rfl) coord hc)
        (hitCount_tail_one_side hp.le hp' hε hε' (.inr rfl) coord hc)

end BilateralProfitRegular.Factory
end BundlePart002


section BundlePart003




namespace BilateralProfitRegular

open Set MechanismDesign.BilateralTrade BilateralProfit MeasureTheory

private theorem intT_subset_unitSq : intT ⊆ BilateralProfitMHR.unitSq := by
  intro x hx
  exact ⟨⟨hx.1.le, (hx.2.1.trans hx.2.2).le⟩,
    ⟨(hx.1.trans hx.2.1).le, hx.2.2.le⟩⟩

private theorem onUnit_facts (E : Environment) (hE : OnUnit E) :
    (∀ a, 0 ≤ P E a ∧ P E a ≤ 1) ∧
    (∀ a ∈ BilateralProfitMHR.unitSq, P E a = E.cdfS a.1 * (1 - E.cdfB a.2)) ∧
    (∀ a ∈ BilateralProfitMHR.unitSq, 0 < mu E a ↔ a ∈ intT) ∧
    (0 < muStar E ∧ muStar E ≤ 1) ∧
    (∀ a ∈ BilateralProfitMHR.unitSq, mu E a ≤ muStar E) ∧
    (∃ a ∈ intT, mu E a = muStar E) := by
  obtain ⟨_, _, hp, hf, _, _, _, _, hm, hs, hu, he, _⟩ :=
    BilateralProfitMHR.positive_density_profit_facts E hE
  exact ⟨hp, hf, hm, hs, hu, he⟩

private theorem P_factor (E : Environment) (hE : OnUnit E) {x : ℝ × ℝ}
    (hx : x ∈ BilateralProfitMHR.unitSq) :
    P E x = E.cdfS x.1 * (1 - E.cdfB x.2) :=
  (onUnit_facts E hE).2.1 x hx

private theorem mu_formula (E : Environment) (x : ℝ × ℝ) :
    mu E x = (x.2 - x.1) * P E x := rfl

private theorem mu_le_muStar (E : Environment) (hE : OnUnit E) {x : ℝ × ℝ}
    (hx : x ∈ BilateralProfitMHR.unitSq) : mu E x ≤ muStar E :=
  (onUnit_facts E hE).2.2.2.2.1 x hx

private theorem cdfS_pos (E : Environment) (hE : OnUnit E) {p : ℝ} (hp : p ∈ Ioc 0 1) :
    0 < E.cdfS p := by
  have hf := E.fS_intervalIntegrable
  rw [hE.1, hE.2.1] at hf
  unfold Environment.cdfS
  rw [hE.1]
  apply intervalIntegral.intervalIntegral_pos_of_pos_on _ _ hp.1
  · apply hf.mono_set
    rw [uIcc_of_le hp.1.le, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc le_rfl hp.2
  · intro t ht
    exact E.fS_pos t (by rw [hE.1, hE.2.1]; exact ⟨ht.1.le, ht.2.le.trans hp.2⟩)

private theorem tailB_eq_integral (E : Environment) (hE : OnUnit E) {q : ℝ} (hq : q ∈ Icc 0 1) :
    1 - E.cdfB q = ∫ t in q..1, E.fB t := by
  have hf := E.fB_intervalIntegrable
  have ht := E.fB_integral
  rw [hE.2.2.1, hE.2.2.2] at hf ht
  have h₁ := hf.mono_set (show uIcc 0 q ⊆ uIcc 0 1 by
    rw [uIcc_of_le hq.1, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc le_rfl hq.2)
  have h₂ := hf.mono_set (show uIcc q 1 ⊆ uIcc 0 1 by
    rw [uIcc_of_le hq.2, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc hq.1 le_rfl)
  rw [Environment.cdfB, hE.2.2.1]
  linarith [intervalIntegral.integral_add_adjacent_intervals h₁ h₂]

private theorem tailB_pos (E : Environment) (hE : OnUnit E) {q : ℝ} (hq : q ∈ Ico 0 1) :
    0 < 1 - E.cdfB q := by
  rw [tailB_eq_integral E hE ⟨hq.1, hq.2.le⟩]
  have hf := E.fB_intervalIntegrable
  rw [hE.2.2.1, hE.2.2.2] at hf
  apply intervalIntegral.intervalIntegral_pos_of_pos_on _ _ hq.2
  · apply hf.mono_set
    rw [uIcc_of_le hq.2.le, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc hq.1 le_rfl
  · intro t ht
    exact E.fB_pos t (by rw [hE.2.2.1, hE.2.2.2]; exact ⟨hq.1.trans ht.1.le, ht.2.le⟩)

private theorem intT_cdf_pos (E : Environment) (hE : OnUnit E) {x : ℝ × ℝ} (hx : x ∈ intT) :
    0 < E.cdfS x.1 ∧ 0 < 1 - E.cdfB x.2 :=
  ⟨cdfS_pos E hE ⟨hx.1, (intT_subset_unitSq hx).1.2⟩,
    tailB_pos E hE ⟨(intT_subset_unitSq hx).2.1, hx.2.2⟩⟩

private theorem balance_pos (E : Environment) (hE : OnUnit E) {x : ℝ × ℝ} (hx : x ∈ intT) :
    0 < balance E x :=
  Real.sqrt_pos.2 (div_pos (intT_cdf_pos E hE hx).1 (intT_cdf_pos E hE hx).2)

private theorem balance_sq (E : Environment) (hE : OnUnit E) {x : ℝ × ℝ} (hx : x ∈ intT) :
    balance E x ^ 2 = E.cdfS x.1 / (1 - E.cdfB x.2) :=
  Real.sq_sqrt (div_pos (intT_cdf_pos E hE hx).1 (intT_cdf_pos E hE hx).2).le

private theorem auxProfit_pos (E : Environment) (hE : OnUnit E) {lam : ℝ} (hlam : 0 < lam)
    {x : ℝ × ℝ} (hx : x ∈ intT) : 0 < auxProfit E lam x := by
  have hm := intT_cdf_pos E hE hx
  unfold auxProfit
  exact div_pos (mul_pos (by norm_num) (sub_pos.mpr hx.2.1))
    (pow_pos (add_pos (div_pos hlam hm.1) (div_pos (inv_pos.mpr hlam) hm.2)) _)

private theorem eq_42 (E : Environment) (hE : RegularUnit E) (x z : ℝ × ℝ) (hx : x ∈ intT)
    (hz : z ∈ intT) (ρ : ℝ) (hρ : 0 < ρ) :
    1 / auxProfit E (ρ * balance E z) x =
      P E z / (4 * (x.2 - x.1)) * (ρ / P E (x.1, z.2) + ρ⁻¹ / P E (z.1, x.2)) ^ 2 := by
  have hX := intT_subset_unitSq hx
  have hZ := intT_subset_unitSq hz
  rw [P_factor E hE.1 hZ, P_factor E hE.1 (x := (x.1,z.2)) ⟨hX.1,hZ.2⟩,
    P_factor E hE.1 (x := (z.1,x.2)) ⟨hZ.1,hX.2⟩]
  have hsX := (intT_cdf_pos E hE.1 hx).1.ne'
  have hbX := (intT_cdf_pos E hE.1 hx).2.ne'
  have hsZ := (intT_cdf_pos E hE.1 hz).1.ne'
  have hbZ := (intT_cdf_pos E hE.1 hz).2.ne'
  have hlZ := (balance_pos E hE.1 hz).ne'
  have hs := balance_sq E hE.1 hz
  have hei : (balance E z)⁻¹ = balance E z * (1 - E.cdfB z.2) / E.cdfS z.1 := by
    apply inv_eq_of_mul_eq_one_left
    calc
      balance E z * (1 - E.cdfB z.2) / E.cdfS z.1 * balance E z =
          (balance E z ^ 2 * (1 - E.cdfB z.2)) / E.cdfS z.1 := by ring
      _ = 1 := by rw [hs, div_mul_cancel₀ _ hbZ, div_self hsZ]
  have he :
      ρ * balance E z / E.cdfS x.1 + (ρ * balance E z)⁻¹ / (1 - E.cdfB x.2) =
      (balance E z * (1 - E.cdfB z.2)) *
        (ρ / (E.cdfS x.1 * (1 - E.cdfB z.2)) + ρ⁻¹ / (E.cdfS z.1 * (1 - E.cdfB x.2))) := by
    rw [mul_inv, hei]
    field_simp
  have hsq : (balance E z * (1 - E.cdfB z.2)) ^ 2 =
      E.cdfS z.1 * (1 - E.cdfB z.2) := by
    rw [mul_pow, hs, pow_two, ← mul_assoc, div_mul_cancel₀ _ hbZ]
  simp only [auxProfit, one_div, inv_div]
  rw [he, mul_pow, hsq]
  ring

private theorem eq_47 (E : Environment) (hE : RegularUnit E) (x z : ℝ × ℝ) (hx : x ∈ intT)
    (hz : z ∈ intT) :
    Real.log (balance E x / balance E z) =
      1 / 2 * Real.log (P E (x.1, z.2) / P E (z.1, x.2)) := by
  have hX := intT_subset_unitSq hx
  have hZ := intT_subset_unitSq hz
  have hbX := (intT_cdf_pos E hE.1 hx).2.ne'
  have hsZ := (intT_cdf_pos E hE.1 hz).1.ne'
  have hbZ := (intT_cdf_pos E hE.1 hz).2.ne'
  have he : (balance E x / balance E z)^2 = P E (x.1, z.2) / P E (z.1, x.2) := by
    rw [div_pow, balance_sq E hE.1 hx, balance_sq E hE.1 hz,
      P_factor E hE.1 (x := (x.1,z.2)) ⟨hX.1,hZ.2⟩,
      P_factor E hE.1 (x := (z.1,x.2)) ⟨hZ.1,hX.2⟩]
    dsimp
    field_simp
  rw [← he, Real.log_pow]
  ring

end BilateralProfitRegular
end BundlePart003


section BundlePart004


namespace BilateralProfitRegular

open MechanismDesign.BilateralTrade

private theorem hasDerivAt_tanh (t : ℝ) : HasDerivAt Real.tanh (1 / Real.cosh t ^ 2) t := by
  have hd := (Real.hasDerivAt_sinh t).div (Real.hasDerivAt_cosh t) (Real.cosh_pos t).ne'
  have he : Real.tanh = Real.sinh / Real.cosh := funext Real.tanh_eq_sinh_div_cosh
  rw [he]
  simpa only [← pow_two, Real.cosh_sq_sub_sinh_sq] using hd

private theorem tanh_lipschitz : LipschitzWith 1 Real.tanh := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun t => (hasDerivAt_tanh t).differentiableAt)
  intro t
  rw [(hasDerivAt_tanh t).deriv]
  change ‖(1 / Real.cosh t ^ 2 : ℝ)‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply (div_le_iff₀ (pow_pos (Real.cosh_pos t) _)).mpr
  nlinarith only [Real.one_le_cosh t, sq_nonneg (Real.cosh t - 1)]

private theorem sech_sq_add_tanh_sq (t : ℝ) :
    (2 / (Real.exp t + Real.exp (-t))) ^ 2 + Real.tanh t ^ 2 = 1 := by
  rw [Real.tanh_eq_sinh_div_cosh]
  -- The exponential denominator is twice the hyperbolic cosine.
  have hc : Real.exp t + Real.exp (-t) = 2 * Real.cosh t := by rw [Real.cosh_eq]; ring
  rw [hc]
  have ht := (Real.cosh_pos t).ne'
  field_simp
  nlinarith only [Real.cosh_sq_sub_sinh_sq t]

private theorem auxProfit_sech (E : Environment) (hE : OnUnit E) {lam : ℝ} (hlam : 0 < lam)
    {x : ℝ × ℝ} (hx : x ∈ intT) :
    auxProfit E lam x =
      mu E x * (2 / (Real.exp (Real.log (lam / balance E x)) +
        Real.exp (-Real.log (lam / balance E x)))) ^ 2 := by
  obtain ⟨hs, hb⟩ := intT_cdf_pos E hE hx
  have hl := balance_pos E hE hx
  have hsq := balance_sq E hE hx
  let t := Real.log (lam / balance E x)
  have he : Real.exp t + Real.exp (-t) = lam / balance E x + balance E x / lam := by
    rw [Real.exp_neg, show Real.exp t = lam / balance E x from Real.exp_log (div_pos hlam hl),
      inv_div]
  have hdivide :
      balance E x ^ 2 / E.cdfS x.1 = (1 - E.cdfB x.2)⁻¹ := by
    rw [hsq]
    field_simp [hs.ne']
  have hinv :
      lam / E.cdfS x.1 + lam⁻¹ / (1 - E.cdfB x.2) =
        balance E x / E.cdfS x.1 * (Real.exp t + Real.exp (-t)) := by
    rw [he, mul_add]
    congr 1
    · field_simp
    · calc
        lam⁻¹ / (1 - E.cdfB x.2) = (balance E x ^ 2 / E.cdfS x.1) / lam := by
          rw [hdivide]
          ring
        _ = balance E x / E.cdfS x.1 * (balance E x / lam) := by ring
  have hnorm : (balance E x / E.cdfS x.1) ^ 2 = (E.cdfS x.1 * (1 - E.cdfB x.2))⁻¹ := by
    calc
      (balance E x / E.cdfS x.1) ^ 2 =
          (balance E x ^ 2 / E.cdfS x.1) / E.cdfS x.1 := by ring
      _ = _ := by rw [hdivide, mul_inv]; ring
  change auxProfit E lam x = mu E x * (2 / (Real.exp t + Real.exp (-t))) ^ 2
  rw [auxProfit, hinv, mul_pow, hnorm, mu_formula, P_factor E hE (intT_subset_unitSq hx),
    inv_mul_eq_div, div_div_eq_mul_div, div_pow]
  ring

private theorem auxProfit_tanh_gap (E : Environment) (hE : OnUnit E) {lam : ℝ}
    (hlam : 0 < lam) {x : ℝ × ℝ} (hx : x ∈ intT) :
    mu E x - auxProfit E lam x = mu E x * Real.tanh (Real.log (lam / balance E x)) ^ 2 := by
  rw [auxProfit_sech E hE hlam hx]
  have he := sech_sq_add_tanh_sq (Real.log (lam / balance E x))
  nlinarith only [congrArg (fun t => mu E x * t) he]

private theorem auxProfit_values (E : Environment) (hE : OnUnit E) {lam : ℝ} (hlam : 0 < lam)
    {x : ℝ × ℝ} (hx : x ∈ intT) :
    0 ≤ mu E x - auxProfit E lam x ∧
    mu E x - auxProfit E lam x ≤ mu E x * Real.log (lam / balance E x) ^ 2 ∧
    0 < auxProfit E lam x ∧ auxProfit E lam x ≤ mu E x ∧
    auxProfit E (balance E x) x = mu E x := by
  have hmu := ((onUnit_facts E hE).2.2.1 x (intT_subset_unitSq hx)).mpr hx
  have he := auxProfit_tanh_gap E hE hlam hx
  have hg : 0 ≤ mu E x - auxProfit E lam x := he.symm ▸ mul_nonneg hmu.le (sq_nonneg _)
  refine ⟨hg, ?_, auxProfit_pos E hE hlam hx, sub_nonneg.mp hg, ?_⟩
  · rw [he]
    let t := Real.log (lam / balance E x)
    have hd : |Real.tanh t| ≤ |t| := by
      simpa [Real.dist_eq] using tanh_lipschitz.dist_le_mul t 0
    apply mul_le_mul_of_nonneg_left _ hmu.le
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (Real.tanh t)) hd 2
  · have hb := balance_pos E hE hx
    have ht := auxProfit_tanh_gap E hE hb hx
    rw [div_self hb.ne', Real.log_one, Real.tanh_zero] at ht
    linarith

private theorem auxProfit_perturbation (E : Environment) (hE : OnUnit E) {lam : ℝ} (hlam : 0 < lam)
    {x : ℝ × ℝ} (hx : x ∈ intT) (θ : ℝ) :
    muStar E - auxProfit E (lam * Real.exp θ) x ≤
      2 * (muStar E - auxProfit E lam x) + 2 * muStar E * θ ^ 2 := by
  let t := Real.log (lam / balance E x)
  have hb := balance_pos E hE hx
  have hmu := ((onUnit_facts E hE).2.2.1 x (intT_subset_unitSq hx)).mpr hx
  have hmuStar := mu_le_muStar E hE (intT_subset_unitSq hx)
  have he : Real.log ((lam * Real.exp θ) / balance E x) = t + θ := by
    rw [mul_div_right_comm, Real.log_mul (div_pos hlam hb).ne' (Real.exp_pos _).ne', Real.log_exp]
  have hgap := auxProfit_tanh_gap E hE (mul_pos hlam (Real.exp_pos θ)) hx
  rw [he] at hgap
  have hbase := auxProfit_tanh_gap E hE hlam hx
  change mu E x - auxProfit E lam x = mu E x * Real.tanh t ^ 2 at hbase
  have hdiff : |Real.tanh (t + θ) - Real.tanh t| ≤ |θ| := by
    simpa [Real.dist_eq] using tanh_lipschitz.dist_le_mul (t + θ) t
  have hsq : (Real.tanh (t + θ) - Real.tanh t)^2 ≤ θ^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hdiff 2
  have hsq' : Real.tanh (t + θ) ^ 2 ≤ 2 * Real.tanh t ^ 2 + 2 * θ ^ 2 := by
    nlinarith only [hsq, sq_nonneg (Real.tanh (t + θ) - 2 * Real.tanh t)]
  have hquad := mul_le_mul_of_nonneg_left hsq' hmu.le
  have hscale := mul_le_mul_of_nonneg_right hmuStar (sq_nonneg θ)
  linarith only [hgap, hbase, hmuStar, hquad, hscale]

/-- High auxiliary profit bounds the logarithmic displacement of the balance. -/
private theorem auxProfit_implies_balance_bound (E : Environment) (hE : OnUnit E) {lam : ℝ}
    (hlam : 0 < lam) {x : ℝ × ℝ} (hx : x ∈ intT) {d : ℝ} (hd : 0 ≤ d) (hd₁ : d < 1)
    (hr : (1 - d ^ 2) * muStar E ≤ auxProfit E lam x) :
    |Real.log (balance E x / lam)| ≤ Real.artanh d := by
  let t := Real.log (lam / balance E x)
  have hmu := ((onUnit_facts E hE).2.2.1 x (intT_subset_unitSq hx)).mpr hx
  have hmuStar := mu_le_muStar E hE (intT_subset_unitSq hx)
  have hd₂ : 0 ≤ 1 - d ^ 2 := by
    have hh := pow_le_pow_left₀ hd hd₁.le 2
    linarith only [hh]
  have hbase : mu E x - auxProfit E lam x = mu E x * Real.tanh t ^ 2 :=
    auxProfit_tanh_gap E hE hlam hx
  have hbound : Real.tanh t ^ 2 ≤ d ^ 2 := by
    apply le_of_mul_le_mul_left _ hmu
    linarith only [hbase, hr, mul_le_mul_of_nonneg_left hmuStar hd₂]
  rw [← sq_abs (Real.tanh t)] at hbound
  obtain ⟨htl, htr⟩ := abs_le.mp (le_of_pow_le_pow_left₀ (by decide) hd hbound)
  have htu : t ≤ Real.artanh d := by
    rw [← Real.artanh_tanh t]
    exact Real.artanh_le_artanh (Real.neg_one_lt_tanh t) hd₁ htr
  have htl' : -t ≤ Real.artanh d := by
    have hneg : Real.tanh (-t) ≤ d := by rw [Real.tanh_neg]; linarith only [htl]
    rw [← Real.artanh_tanh (-t)]
    exact Real.artanh_le_artanh (Real.neg_one_lt_tanh _) hd₁ hneg
  rw [← inv_div, Real.log_inv]
  exact abs_le.mpr ⟨by linarith only [htu], htl'⟩

/-- The offset interval used to form the regular candidates has a universal numerical bound. -/
private theorem regular_offset_halfwidth :
    0 < Real.artanh (1 / Real.sqrt 2000) ∧ Real.artanh (1 / Real.sqrt 2000) ≤ 1 / 40 := by
  let d := 1 / Real.sqrt 2000
  have hroot : 41 ≤ Real.sqrt 2000 := (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
  have hpos : 0 < d := by dsimp [d]; positivity
  have hdu : d ≤ 1 / 41 := one_div_le_one_div_of_le (by norm_num) hroot
  have hdlt : d < 1 := by linarith only [hdu]
  change 0 < Real.artanh d ∧ Real.artanh d ≤ 1 / 40
  refine ⟨Real.artanh_pos ⟨hpos, hdlt⟩, ?_⟩
  have h1 : 0 < 1 - d := sub_pos.mpr hdlt
  have harg : 0 < (1 + d) / (1 - d) := div_pos (by linarith only [hpos]) h1
  rw [Real.artanh_eq_half_log ⟨by linarith only [hpos], hdlt.le⟩]
  have hlog := Real.log_le_sub_one_of_pos harg
  have hquot : (1 + d) / (1 - d) - 1 ≤ 1 / 20 := by
    apply sub_le_iff_le_add.mpr
    apply (div_le_iff₀ h1).mpr
    linarith only [hdu]
  linarith only [hlog, hquot]

end BilateralProfitRegular
end BundlePart004


section BundlePart005


namespace BilateralProfitRegular

open Set MechanismDesign.BilateralTrade

private theorem lemma_6_3 (E : Environment) (hE : RegularUnit E) (lam : ℝ) (hlam : 0 < lam)
    (x z : ℝ × ℝ) (hx : x ∈ intT) (hz : z ∈ intT)
    (hrx : 99 / 100 * muStar E ≤ auxProfit E lam x)
    (hrz : 99 / 100 * muStar E ≤ auxProfit E lam z) :
    (x.1, z.2) ∈ triT ∧ (z.1, x.2) ∈ triT ∧
    muStar E - mu E (x.1, z.2) ≤
      4 * (muStar E - auxProfit E lam x + (muStar E - auxProfit E lam z)) ∧
    muStar E - mu E (z.1, x.2) ≤
      4 * (muStar E - auxProfit E lam x + (muStar E - auxProfit E lam z)) ∧
    ∀ a ∈ ({x, z, (x.1, z.2), (z.1, x.2)} : Set (ℝ × ℝ)),
      ∀ b ∈ ({x, z, (x.1, z.2), (z.1, x.2)} : Set (ℝ × ℝ)), P E a ≤ 3 * P E b := by
  let M := muStar E
  have hM : 0 < M := (onUnit_facts E hE.1).2.2.2.1.1
  let A (t : ℝ × ℝ) := lam / E.cdfS t.1
  let B (t : ℝ × ℝ) := lam⁻¹ / (1 - E.cdfB t.2)
  let H (t : ℝ × ℝ) := (A t + B t) / 2
  let D (t : ℝ × ℝ) := (A t - B t) / 2
  let Δ (t : ℝ × ℝ) := M - auxProfit E lam t
  have hA {t : ℝ × ℝ} (ht : t ∈ intT) : 0 < A t :=
    div_pos hlam (intT_cdf_pos E hE.1 ht).1
  have hB {t : ℝ × ℝ} (ht : t ∈ intT) : 0 < B t :=
    div_pos (inv_pos.mpr hlam) (intT_cdf_pos E hE.1 ht).2
  have hH {t : ℝ × ℝ} (ht : t ∈ intT) : 0 < H t :=
    div_pos (add_pos (hA ht) (hB ht)) (by norm_num)
  have hmem {s t : ℝ × ℝ} (hs : s ∈ intT) (ht : t ∈ intT) :
      (s.1, t.2) ∈ BilateralProfitMHR.unitSq :=
    ⟨(intT_subset_unitSq hs).1, (intT_subset_unitSq ht).2⟩
  have hP {s t : ℝ × ℝ} (hs : s ∈ intT) (ht : t ∈ intT) :
      P E (s.1,t.2) * (A s * B t) = 1 := by
    rw [P_factor E hE.1 (hmem hs ht)]
    dsimp [A, B]
    have hs' := (intT_cdf_pos E hE.1 hs).1.ne'
    have ht' := (intT_cdf_pos E hE.1 ht).2.ne'
    field_simp [hlam.ne']
  have hPpos {s t : ℝ × ℝ} (hs : s ∈ intT) (ht : t ∈ intT) :
      0 < P E (s.1,t.2) := by
    rw [P_factor E hE.1 (hmem hs ht)]
    exact mul_pos (intT_cdf_pos E hE.1 hs).1 (intT_cdf_pos E hE.1 ht).2
  have hspread {t : ℝ × ℝ} (ht : t ∈ intT) :
      auxProfit E lam t * H t ^ 2 = t.2 - t.1 := by
    change (4 * (t.2 - t.1) / (A t + B t) ^ 2) * ((A t + B t) / 2) ^ 2 = _
    have hp := (add_pos (hA ht) (hB ht)).ne'
    field_simp
    ring
  have hdev {t : ℝ × ℝ} (ht : t ∈ intT) : M * D t ^ 2 ≤ Δ t * H t ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right (mu_le_muStar E hE.1 (intT_subset_unitSq ht))
      (mul_pos (hA ht) (hB ht)).le
    rw [mu_formula, mul_assoc, hP ht ht, mul_one] at hh
    have he : A t * B t = H t ^ 2 - D t ^ 2 := by unfold H D; ring
    rw [he, ← hspread ht] at hh
    dsimp [Δ]
    linarith only [hh]
  have hΔ {t : ℝ × ℝ} (ht : t ∈ intT) : 0 ≤ Δ t :=
    nonneg_of_mul_nonneg_left
      ((mul_nonneg hM.le (sq_nonneg _)).trans (hdev ht)) (pow_pos (hH ht) _)
  have hbds {t : ℝ × ℝ} (ht : t ∈ intT) (hr : 99 / 100 * M ≤ auxProfit E lam t) :
      9 / 10 * H t ≤ A t ∧ A t ≤ 11 / 10 * H t ∧
      9 / 10 * H t ≤ B t ∧ B t ≤ 11 / 10 * H t := by
    have hd : Δ t ≤ M / 100 := by dsimp [Δ]; linarith
    have hs := (hdev ht).trans (mul_le_mul_of_nonneg_right hd (sq_nonneg (H t)))
    have hh : D t ^ 2 ≤ (H t / 10) ^ 2 := by
      apply le_of_mul_le_mul_left _ hM
      nlinarith only [hs]
    have habs : |D t| ≤ H t / 10 := by
      rw [← sq_abs (D t)] at hh
      exact le_of_pow_le_pow_left₀ (by decide) (by linarith only [hH ht]) hh
    obtain ⟨hl, hu⟩ := abs_le.mp habs
    unfold D H at hl hu
    unfold H
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  let G (s t : ℝ × ℝ) := M - mu E (s.1,t.2)
  have hG {s t : ℝ × ℝ} (hs : s ∈ intT) (ht : t ∈ intT) : 0 ≤ G s t :=
    sub_nonneg.mpr (mu_le_muStar E hE.1 (hmem hs ht))
  have hG_eq {s t : ℝ × ℝ} (hs : s ∈ intT) (ht : t ∈ intT) :
      G s t * (A s * B t) = M * (A s * B t) - (t.2 - s.1) := by
    change (M - mu E (s.1,t.2)) * _ = _
    rw [sub_mul, mu_formula, mul_assoc, hP hs ht, mul_one]
  let S := G x z * (A x * B z) + G z x * (A z * B x)
  have hS0 : 0 ≤ S := add_nonneg (mul_nonneg (hG hx hz) (mul_pos (hA hx) (hB hz)).le)
    (mul_nonneg (hG hz hx) (mul_pos (hA hz) (hB hx)).le)
  have hS :
      S = Δ x * H x ^ 2 + Δ z * H z ^ 2 - M * (H x - H z) ^ 2 - 2 * M * D x * D z := by
    unfold S
    rw [hG_eq hx hz, hG_eq hz hx]
    have he : (z.2 - x.1) + (x.2 - z.1) = (x.2 - x.1) + (z.2 - z.1) := by ring
    rw [sub_add_sub_comm, he, ← hspread hx, ← hspread hz]
    unfold Δ D H
    ring
  have hcross : -(2 * M * D x * D z) ≤ M * D x ^ 2 + M * D z ^ 2 := by
    nlinarith only [mul_nonneg hM.le (sq_nonneg (D x + D z))]
  let m := max (H x) (H z)
  have hm : 0 < m := (hH hx).trans_le (le_max_left _ _)
  have hm₁ : H x ≤ m := le_max_left _ _
  have hm₂ : H z ≤ m := le_max_right _ _
  have hΔm : Δ x + Δ z ≤ M / 50 := by dsimp [Δ]; linarith only [hrx, hrz]
  have hSle : S ≤ 2 * (Δ x + Δ z) * m ^ 2 - M * (H x - H z) ^ 2 := by
    have hh₁ : H x ^ 2 ≤ m ^ 2 := pow_le_pow_left₀ (hH hx).le hm₁ 2
    have hh₂ : H z ^ 2 ≤ m ^ 2 := pow_le_pow_left₀ (hH hz).le hm₂ 2
    rw [hS]
    linarith only [hcross, hdev hx, hdev hz, mul_le_mul_of_nonneg_left hh₁ (hΔ hx),
      mul_le_mul_of_nonneg_left hh₂ (hΔ hz)]
  have hdiff : |H x - H z| ≤ m / 5 := by
    have hb := mul_le_mul_of_nonneg_right hΔm (sq_nonneg m)
    have ht : (H x - H z)^2 ≤ (m / 5)^2 := by
      apply le_of_mul_le_mul_left _ hM
      nlinarith only [hS0, hSle, hb]
    rw [← sq_abs (H x - H z)] at ht
    exact le_of_pow_le_pow_left₀ (by decide) (by linarith only [hm]) ht
  obtain ⟨hmd₁, hmd₂⟩ := abs_le.mp hdiff
  have hmin₁ : 4 / 5 * m ≤ H x := by
    dsimp [m] at hmd₁ ⊢
    rcases le_total (H x) (H z) with h | h
    · rw [max_eq_right h] at hmd₁ ⊢
      linarith only [hmd₁]
    · rw [max_eq_left h]
      linarith only [hH hx]
  have hmin₂ : 4 / 5 * m ≤ H z := by
    dsimp [m] at hmd₂ ⊢
    rcases le_total (H x) (H z) with h | h
    · rw [max_eq_right h]
      linarith only [hH hz]
    · rw [max_eq_left h] at hmd₂ ⊢
      linarith only [hmd₂]
  have hprod : 4 / 5 * m ^ 2 ≤ H x * H z := by
    by_cases h : H x ≤ H z
    · have he : m = H z := max_eq_right h
      calc
        (4 / 5) * m ^ 2 = (4 / 5 * m) * H z := by rw [he]; ring
        _ ≤ H x * H z := mul_le_mul_of_nonneg_right hmin₁ (hH hz).le
    · have he : m = H x := max_eq_left (le_of_not_ge h)
      calc
        (4 / 5) * m ^ 2 = H x * (4 / 5 * m) := by rw [he]; ring
        _ ≤ H x * H z := mul_le_mul_of_nonneg_left hmin₂ (hH hx).le
  obtain ⟨hax₁, hax₂, hbx₁, hbx₂⟩ := hbds hx hrx
  obtain ⟨haz₁, haz₂, hbz₁, hbz₂⟩ := hbds hz hrz
  have hab₁ : 16 / 25 * m ^ 2 ≤ A x * B z := by
    have he := mul_le_mul hax₁ hbz₁ (by linarith only [hH hz]) (hA hx).le
    nlinarith only [he, hprod]
  have hab₂ : 16 / 25 * m ^ 2 ≤ A z * B x := by
    have he := mul_le_mul haz₁ hbx₁ (by linarith only [hH hx]) (hA hz).le
    nlinarith only [he, hprod]
  have hGle {s t : ℝ × ℝ} (hs : s ∈ intT) (ht : t ∈ intT)
      (hab : 16 / 25 * m ^ 2 ≤ A s * B t) (hg : G s t * (A s * B t) ≤ S) :
      G s t ≤ 4 * (Δ x + Δ z) := by
    have hlow := mul_le_mul_of_nonneg_left hab (hG hs ht)
    have hpos : 0 < m ^ 2 := pow_pos hm _
    have hd := add_nonneg (hΔ hx) (hΔ hz)
    apply le_of_mul_le_mul_right _ hpos
    nlinarith only [hlow, hg, hSle, mul_nonneg hM.le (sq_nonneg (H x - H z)),
      mul_nonneg hd hpos.le]
  have hG₁ := hGle hx hz hab₁
    (le_add_of_nonneg_right (mul_nonneg (hG hz hx) (mul_pos (hA hz) (hB hx)).le))
  have hG₂ := hGle hz hx hab₂
    (le_add_of_nonneg_left (mul_nonneg (hG hx hz) (mul_pos (hA hx) (hB hz)).le))
  have htri {s t : ℝ × ℝ} (hs : s ∈ intT) (ht : t ∈ intT)
      (hg : G s t ≤ 4 * (Δ x + Δ z)) : (s.1, t.2) ∈ triT := by
    have hp : 0 < mu E (s.1,t.2) := by dsimp [G] at hg; linarith only [hM, hg, hΔm]
    exact ⟨hs.1.le, le_of_lt ((onUnit_facts E hE.1).2.2.1 _ (hmem hs ht) |>.mp hp).2.1,
      ht.2.2.le⟩
  refine ⟨htri hx hz hG₁, htri hz hx hG₂, hG₁, hG₂, ?_⟩
  have hProb {s t : ℝ × ℝ} (hs : s ∈ intT) (ht : t ∈ intT)
      (ha₁ : 9 / 10 * H s ≤ A s) (ha₂ : A s ≤ 11 / 10 * H s)
      (hb₁ : 9 / 10 * H t ≤ B t) (hb₂ : B t ≤ 11 / 10 * H t)
      (hm_s : 4 / 5 * m ≤ H s) (hm_t : 4 / 5 * m ≤ H t)
      (hs_m : H s ≤ m) (ht_m : H t ≤ m) :
      1 / ((11 / 10 * m) ^ 2) ≤ P E (s.1,t.2) ∧
        P E (s.1,t.2) ≤ 1 / ((18 / 25 * m) ^ 2) := by
    have hloA : 18 / 25 * m ≤ A s := by linarith only [ha₁, hm_s]
    have hloB : 18 / 25 * m ≤ B t := by linarith only [hb₁, hm_t]
    have hhiA : A s ≤ 11 / 10 * m := by linarith only [ha₂, hs_m]
    have hhiB : B t ≤ 11 / 10 * m := by linarith only [hb₂, ht_m]
    have he := hP hs ht
    have hv := (hPpos hs ht).le
    constructor
    · have hbound := mul_le_mul hhiA hhiB (hB ht).le (by linarith only [hm])
      apply (div_le_iff₀ (pow_pos (by linarith only [hm] : 0 < 11 / 10 * m) _)).mpr
      simpa only [sq, mul_comm (P E (s.1,t.2))] using
        he.symm.le.trans (mul_le_mul_of_nonneg_left hbound hv)
    · have hbound := mul_le_mul hloA hloB (by linarith only [hm]) (hA hs).le
      apply (le_div_iff₀ (pow_pos (by linarith only [hm] : 0 < 18 / 25 * m) _)).mpr
      simpa only [sq] using
        (mul_le_mul_of_nonneg_left hbound hv).trans he.le
  have hPall (a : ℝ × ℝ) (ha : a ∈ ({x, z, (x.1, z.2), (z.1, x.2)} : Set (ℝ × ℝ))) :
      1 / ((11 / 10 * m) ^ 2) ≤ P E a ∧ P E a ≤ 1 / ((18 / 25 * m) ^ 2) := by
    simp only [mem_insert_iff, mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact hProb hx hx hax₁ hax₂ hbx₁ hbx₂ hmin₁ hmin₁ hm₁ hm₁
    · exact hProb hz hz haz₁ haz₂ hbz₁ hbz₂ hmin₂ hmin₂ hm₂ hm₂
    · exact hProb hx hz hax₁ hax₂ hbz₁ hbz₂ hmin₁ hmin₂ hm₁ hm₂
    · exact hProb hz hx haz₁ haz₂ hbx₁ hbx₂ hmin₂ hmin₁ hm₂ hm₁
  intro a ha b hb
  apply (hPall a ha).2.trans
  apply le_trans _ (mul_le_mul_of_nonneg_left (hPall b hb).1 (by norm_num))
  rw [mul_one_div]
  apply (div_le_div_iff₀ (pow_pos (by linarith only [hm] : 0 < 18 / 25 * m) _)
    (pow_pos (by linarith only [hm] : 0 < 11 / 10 * m) _)).mpr
  nlinarith only [sq_nonneg m]

end BilateralProfitRegular
end BundlePart005


section BundlePart006



namespace BilateralProfitRegular

open Set MechanismDesign.BilateralTrade

/-- The known factor multiplying the product of the three Bernoulli outputs in (53). -/
private noncomputable def observationScale (c : Candidate) (ρ : ℝ) (x : ℝ × ℝ) : ℝ :=
  2000 * (ρ + ρ⁻¹)^2 / ((x.2 - x.1) * c.est)

/-- The conditional mean of one reciprocal bit, after selection between the crossed pairs. -/
private noncomputable def observationReciprocalMean (E : Environment) (c : Candidate) (ρ : ℝ)
    (x z : ℝ × ℝ) : ℝ :=
  (ρ / (ρ + ρ⁻¹)) * (c.est / (20 * P E (x.1,z.2))) +
  (1 - ρ / (ρ + ρ⁻¹)) * (c.est / (20 * P E (z.1,x.2)))

private theorem calibrated_candidate_profit (E : Environment) (hE : RegularUnit E)
    (c : Candidate) (η δ : ℝ) (hη : 0 < η) (hηδ : η < δ)
    (hc : c.Valid E δ) (z : ℝ × ℝ) (hz : z ∈ c.region)
    (ρ : ℝ) (hρ : CalibValid E η δ c z ρ) :
    ∀ x ∈ c.region, 99 / 100 * muStar E ≤ auxProfit E (ρ * balance E z) x ∧
      auxProfit E (ρ * balance E z) x ≤ mu E x ∧ mu E x ≤ muStar E := by
  rcases hc with ⟨hK, _, _, hw, haux, _⟩
  have hlam : 0 < ρ * balance E z := mul_pos hρ.1 (balance_pos E hE.1 (hK hz))
  have hp : 0 < c.param E := mul_pos (Real.exp_pos _) (balance_pos E hE.1 (hK hw))
  have hδ := hη.trans hηδ
  have hs : Real.sqrt (η / δ) ≤ 1 := by
    apply (Real.sqrt_le_iff).2
    exact ⟨zero_le_one, by norm_num; exact (div_le_one hδ).2 hηδ.le⟩
  let u := Real.log (ρ * balance E z / c.param E)
  have hu : |u| ≤ 1 / 1000 := by
    have := hρ.2
    change |u| ≤ 1 / 1000 * Real.sqrt (η / δ) at this
    linarith
  have he : c.param E * Real.exp u = ρ * balance E z := by
    rw [Real.exp_log (div_pos hlam hp)]
    field_simp
  intro x hx
  exact ⟨he ▸ haux u hu x hx, (auxProfit_values E hE.1 hlam (hK hx)).2.2.2.1,
    mu_le_muStar E hE.1 (intT_subset_unitSq (hK hx))⟩

private theorem observation_mean_identity (E : Environment) (hE : RegularUnit E)
    (δ : ℝ) (hδ : 0 < δ) (c : Candidate) (hc : c.Valid E δ)
    (ρ : ℝ) (hρ : 0 < ρ) (x z : ℝ × ℝ) (hx : x ∈ c.region) (hz : z ∈ c.region) :
    observationScale c ρ x * (P E z / (20 * c.est)) *
      observationReciprocalMean E c ρ x z ^ 2 = 1 / auxProfit E (ρ * balance E z) x := by
  rcases hc with ⟨hK, _, _, _, _, hcross, hest, _⟩
  have hest' : 0 < c.est := hδ.trans_le hest
  have hspread : 0 < x.2 - x.1 := sub_pos.mpr (hK hx).2.1
  have hp₁ : 0 < P E (x.1,z.2) := lt_of_lt_of_le (by positivity)
    ((hcross x hx z hz).2.2 _ (by simp)).1
  have hp₂ : 0 < P E (z.1,x.2) := lt_of_lt_of_le (by positivity)
    ((hcross x hx z hz).2.2 _ (by simp)).1
  have ht : 0 < ρ + ρ⁻¹ := by positivity
  rw [eq_42 E hE x z (hK hx) (hK hz) ρ hρ]
  unfold observationScale observationReciprocalMean
  field_simp [hp₁.ne', hp₂.ne', hest'.ne', ht.ne', hρ.ne', hspread.ne']
  ring

private theorem observationScale_bounds (E : Environment) (hE : RegularUnit E)
    (c : Candidate) (η δ : ℝ) (hη : 0 < η) (hηδ : η < δ) (hc : c.Valid E δ)
    (z : ℝ × ℝ) (hz : z ∈ c.region) (ρ : ℝ) (hρ : CalibValid E η δ c z ρ)
    (x : ℝ × ℝ) (hx : x ∈ c.region) :
    0 ≤ observationScale c ρ x ∧ observationScale c ρ x ≤ 81000 / δ := by
  have hCal := calibrated_candidate_profit E hE c η δ hη hηδ hc z hz ρ hρ z hz
  rcases hc with ⟨hK, _, _, _, _, _, hest, _, hwidth⟩
  have hδ := hη.trans hηδ
  have hest' := hδ.trans_le hest
  have hspread : 0 < x.2 - x.1 := sub_pos.mpr (hK hx).2.1
  have hb := balance_pos E hE.1 (hK hz)
  have hlam := mul_pos hρ.1 hb
  have hsech := auxProfit_sech E hE.1 hlam (hK hz)
  have hr : ρ * balance E z / balance E z = ρ := mul_div_cancel_right₀ _ hb.ne'
  rw [hr, Real.exp_neg, Real.exp_log hρ.1] at hsech
  have ht : 0 < ρ + ρ⁻¹ := by have := hρ.1; positivity
  have hiden : auxProfit E (ρ * balance E z) z * (ρ + ρ⁻¹)^2 = 4 * mu E z := by
    rw [hsech]
    field_simp [hρ.1.ne'] <;> ring
  have hm := (onUnit_facts E hE.1).2.2.2.1.1
  have hsq : (ρ + ρ⁻¹)^2 ≤ 400 / 99 := by
    have hmul := mul_le_mul_of_nonneg_right hCal.1 (sq_nonneg (ρ + ρ⁻¹))
    rw [hiden] at hmul
    apply (le_of_mul_le_mul_right ?_ hm)
    nlinarith [hCal.2.2]
  have hW : 1 / ((x.2 - x.1) * c.est) ≤ 10 / δ := by
    have hineq := (div_le_iff₀ hspread).1 (hwidth x hx)
    apply (div_le_div_iff₀ (mul_pos hspread hest') hδ).2
    linarith
  constructor
  · unfold observationScale
    positivity
  · unfold observationScale
    calc
      _ = 2000 * ((ρ + ρ⁻¹)^2 * (1 / ((x.2 - x.1) * c.est))) := by ring
      _ ≤ 2000 * ((400 / 99) * (10 / δ)) := by gcongr
      _ ≤ _ := by
        rw [show 2000 * (400 / 99 * (10 / δ)) = (8000000 / 99) / δ by ring]
        exact (div_le_div_iff_of_pos_right hδ).2 (by norm_num)

private theorem observation_query_gap (E : Environment) (hE : RegularUnit E)
    (c : Candidate) (η δ : ℝ) (hη : 0 < η) (hηδ : η < δ)
    (hδmax : muStar E < 6 * δ) (hc : c.Valid E δ)
    (z : ℝ × ℝ) (hz : z ∈ c.region) (ρ : ℝ) (hρ : CalibValid E η δ c z ρ)
    (x : ℝ × ℝ) (hx : x ∈ c.region) :
    ∀ y ∈ ({z, (x.1,z.2), (z.1,x.2)} : Set (ℝ × ℝ)),
      y ∈ triT ∧ muStar E - mu E y ≤
        8 * (muStar E - auxProfit E (ρ * balance E z) z) +
        144 * δ^2 * (1 / auxProfit E (ρ * balance E z) x -
          sInf ((fun a => 1 / auxProfit E (ρ * balance E z) a) '' c.region)) := by
  have hCal := calibrated_candidate_profit E hE c η δ hη hηδ hc z hz ρ hρ
  have hK := hc.1
  have hlam := mul_pos hρ.1 (balance_pos E hE.1 (hK hz))
  let r := auxProfit E (ρ * balance E z)
  let L := fun y => 1 / r y
  let Lmin := sInf (L '' c.region)
  have hrpos : ∀ y ∈ c.region, 0 < r y := fun y hy => auxProfit_pos E hE.1 hlam (hK hy)
  have hrub : ∀ y ∈ c.region, r y ≤ muStar E := fun y hy => (hCal y hy).2.1.trans (hCal y hy).2.2
  have hLmin : ∀ y ∈ c.region, Lmin ≤ L y := by
    intro y hy
    apply csInf_le _ (mem_image_of_mem L hy)
    refine ⟨0, ?_⟩
    rintro _ ⟨a,ha,rfl⟩
    exact (one_div_pos.mpr (hrpos a ha)).le
  have hg : 0 ≤ L x - Lmin := sub_nonneg.mpr (hLmin x hx)
  have hr : r z - r x ≤ 36 * δ^2 * (L x - Lmin) := by
    have hid : r z - r x = r x * r z * (L x - L z) := by
      dsimp only [L]
      field_simp [(hrpos x hx).ne', (hrpos z hz).ne']
    have hδ := hη.trans hηδ
    have hprod : r x * r z ≤ 36 * δ^2 := by
      calc
        _ ≤ (6 * δ) * (6 * δ) := by
          exact mul_le_mul ((hrub x hx).trans hδmax.le) ((hrub z hz).trans hδmax.le)
            (hrpos z hz).le (by positivity)
        _ = _ := by ring
    rw [hid]
    calc
      _ ≤ r x * r z * (L x - Lmin) :=
        mul_le_mul_of_nonneg_left (by linarith [hLmin z hz]) (mul_nonneg (hrpos x hx).le (hrpos z hz).le)
      _ ≤ _ := mul_le_mul_of_nonneg_right hprod hg
  have hcross := lemma_6_3 E hE _ hlam x z (hK hx) (hK hz) (hCal x hx).1 (hCal z hz).1
  have hg' : 0 ≤ 144 * δ^2 * (L x - Lmin) := by positivity
  change ∀ y ∈ ({z, (x.1,z.2), (z.1,x.2)} : Set (ℝ × ℝ)),
    y ∈ triT ∧ muStar E - mu E y ≤ 8 * (muStar E - r z) + 144 * δ^2 * (L x - Lmin)
  intro y hy
  simp only [mem_insert_iff, mem_singleton_iff] at hy
  rcases hy with (rfl | rfl | rfl)
  · exact ⟨⟨(hK hz).1.le, (hK hz).2.1.le, (hK hz).2.2.le⟩,
      by linarith [(hCal y hz).2.1, hrub y hz]⟩
  · exact ⟨hcross.1, by linarith [hcross.2.2.1]⟩
  · exact ⟨hcross.2.1, by linarith [hcross.2.2.2.1]⟩

end BilateralProfitRegular
end BundlePart006


section BundlePart007




namespace BilateralProfitRegular.Factory

open Classical MeasureTheory Set MechanismDesign.BilateralTrade
open scoped BigOperators ENNReal

set_option maxHeartbeats 600000

private abbrev CalibrationPrices := ℝ × ℝ
private abbrev CalibrationHistory := List (CalibrationPrices × Bool)

private noncomputable def calibrationSamples (T : ℕ) (η δ est : ℝ) : ℕ :=
  ⌈1000000000 * δ * Real.log (2 * (T : ℝ)) / (η * est)⌉₊

private noncomputable def historyFrequency (n j : ℕ) (h : CalibrationHistory) : ℝ :=
  (∑ i : Fin n, if (h[j+i.val]?.getD ((0,0),false)).2 then (1 : ℝ) else 0) / n

private noncomputable def calibrationValue (off f₁ f₂ : ℝ) : ℝ :=
  Real.exp (off - (1 / 2) * Real.log (f₁ / f₂))

private noncomputable def calibrationStep (n : ℕ) (off : ℝ) (y₁ y₂ : CalibrationPrices)
    (h : CalibrationHistory) : CalibrationPrices ⊕ ℝ :=
  if h.length < n then .inl y₁
  else if h.length < 2*n then .inl y₂
  else .inr (calibrationValue off (historyFrequency n 0 h) (historyFrequency n n h))

private noncomputable def calibrationProc (T : ℕ) (η δ est off : ℝ) (w z : CalibrationPrices) :
    Proc CalibrationPrices ℝ Unit where
  step _ h := calibrationStep (calibrationSamples T η δ est) off (z.1,w.2) (w.1,z.2) h
  measurable_step _ := measurable_const

private theorem calibration_queries (T : ℕ) (η δ est off : ℝ) (w z : CalibrationPrices) :
    (calibrationProc T η δ est off w z).QueriesIn {(z.1,w.2),(w.1,z.2)} := by
  intro ω h y hy
  change calibrationStep _ _ _ _ h = Sum.inl y at hy
  unfold calibrationStep at hy
  split at hy
  · cases hy
    exact mem_insert _ _
  · split at hy
    · cases hy
      exact mem_insert_of_mem _ (mem_singleton _)
    · contradiction

private theorem measurable_calibrationValue :
    Measurable (fun a : ℝ × ℝ × ℝ => calibrationValue a.1 a.2.1 a.2.2) := by
  unfold calibrationValue
  fun_prop

private theorem measurable_calibrationStep (h : CalibrationHistory) :
    Measurable (fun a : ℕ × ℝ × CalibrationPrices × CalibrationPrices =>
      calibrationStep a.1 a.2.1 a.2.2.1 a.2.2.2 h) := by
  refine measurable_from_prod_countable_right ?_
  intro n
  unfold calibrationStep
  dsimp only
  by_cases hn : h.length < n
  · simp only [if_pos hn]
    exact measurable_inl.comp (measurable_fst.comp measurable_snd)
  · by_cases hn' : h.length < 2*n
    · simp only [if_neg hn, if_pos hn']
      exact measurable_inl.comp (measurable_snd.comp measurable_snd)
    · simp only [if_neg hn, if_neg hn']
      exact measurable_inr.comp (measurable_calibrationValue.comp
        (measurable_fst.prodMk (measurable_const : Measurable
          (fun _ : ℝ × CalibrationPrices × CalibrationPrices =>
            (historyFrequency n 0 h, historyFrequency n n h)))))

private theorem measurable_calibration (T : ℕ) (η : ℝ) (h : CalibrationHistory) :
    Measurable (fun a : ℝ × ℝ × ℝ × CalibrationPrices × CalibrationPrices =>
      (calibrationProc T η a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2).step () h) := by
  have hn : Measurable (fun a : ℝ × ℝ × ℝ × CalibrationPrices × CalibrationPrices =>
      calibrationSamples T η a.1 a.2.1) := by
    unfold calibrationSamples
    apply Nat.measurable_ceil.comp
    fun_prop
  have hoff : Measurable (fun a : ℝ × ℝ × ℝ × CalibrationPrices × CalibrationPrices =>
      a.2.2.1) := measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hy₁ : Measurable (fun a : ℝ × ℝ × ℝ × CalibrationPrices × CalibrationPrices =>
      (a.2.2.2.2.1,a.2.2.2.1.2)) := by fun_prop
  have hy₂ : Measurable (fun a : ℝ × ℝ × ℝ × CalibrationPrices × CalibrationPrices =>
      (a.2.2.2.1.1,a.2.2.2.2.2)) := by fun_prop
  exact (measurable_calibrationStep h).comp (hn.prodMk (hoff.prodMk (hy₁.prodMk hy₂)))

private noncomputable def calibrationHistory (n k : ℕ) (y₁ y₂ : CalibrationPrices)
    (prob : CalibrationPrices → ℝ) (U : Stream) : CalibrationHistory :=
  List.ofFn fun i : Fin k =>
    let y := if i.val < n then y₁ else y₂
    (y, decide ((U i.val : ℝ) < prob y))

private theorem calibration_history (T : ℕ) (η δ est off : ℝ) (w z : CalibrationPrices)
    (prob : CalibrationPrices → ℝ) (U : Stream) (k : ℕ) :
    let n := calibrationSamples T η δ est
    (calibrationProc T η δ est off w z).hist prob () U k =
      calibrationHistory n (min k (2*n)) (z.1,w.2) (w.1,z.2) prob U := by
  let n := calibrationSamples T η δ est
  let F := calibrationProc T η δ est off w z
  let y₁ := (z.1,w.2)
  let y₂ := (w.1,z.2)
  have hfstep (hh : CalibrationHistory) : F.step () hh = calibrationStep n off y₁ y₂ hh := rfl
  change F.hist prob () U k = calibrationHistory n (min k (2*n)) y₁ y₂ prob U
  induction k with
  | zero => simp [calibrationHistory, Proc.hist]
  | succ k ih =>
    rw [Proc.hist, ih, hfstep]
    have hh : (calibrationHistory n (min k (2*n)) y₁ y₂ prob U).length = min k (2*n) := by
      simp [calibrationHistory]
    by_cases hk : k < 2*n
    · have hk' : min (k+1) (2*n) = k+1 := min_eq_left (by omega)
      have hh' : min k (2*n) = k := min_eq_left hk.le
      rw [hk', hh']
      rw [hh'] at hh
      unfold calibrationStep
      simp only [hh, if_pos hk]
      by_cases hkn : k < n
      · simp only [if_pos hkn, calibrationHistory]
        rw [List.ofFn_succ_last]
        simp only [Fin.val_castSucc, Fin.val_last, hkn, if_true]
      · simp only [if_neg hkn, calibrationHistory]
        rw [List.ofFn_succ_last]
        simp only [Fin.val_castSucc, Fin.val_last, hkn, if_false]
    · have h₁ : min k (2*n) = 2*n := min_eq_right (Nat.le_of_not_gt hk)
      have h₂ : min (k+1) (2*n) = 2*n := min_eq_right (by omega)
      rw [h₁] at hh
      rw [h₁,h₂]
      unfold calibrationStep
      simp only [hh, if_neg (show ¬ (2*n < n) by omega), lt_irrefl, if_false]

private theorem calibration_stopped (T : ℕ) (η δ est off : ℝ) (w z : CalibrationPrices)
    (prob : CalibrationPrices → ℝ) (U : Stream) (k : ℕ) :
    (calibrationProc T η δ est off w z).stopped prob () U k ↔
      2 * calibrationSamples T η δ est ≤ k := by
  let n := calibrationSamples T η δ est
  unfold Proc.stopped
  rw [calibration_history]
  change (calibrationStep n off (z.1,w.2) (w.1,z.2)
    (calibrationHistory n (min k (2*n)) (z.1,w.2) (w.1,z.2) prob U)).isRight = true ↔ 2*n ≤ k
  have hlen : (calibrationHistory n (min k (2*n)) (z.1,w.2) (w.1,z.2) prob U).length =
      min k (2*n) := by simp [calibrationHistory]
  unfold calibrationStep
  simp only [hlen]
  split
  · have : ¬ 2*n ≤ k := by omega
    simp [this]
  · split
    · have : ¬ 2*n ≤ k := by omega
      simp [this]
    · have : 2*n ≤ k := by omega
      simp [this]

private theorem calibration_out (T : ℕ) (η δ est off : ℝ) (w z : CalibrationPrices)
    (prob : CalibrationPrices → ℝ) (U : Stream) :
    let n := calibrationSamples T η δ est
    let p₁ := prob (z.1,w.2)
    let p₂ := prob (w.1,z.2)
    (calibrationProc T η δ est off w z).out prob () U =
      some (calibrationValue off
        (hitCount p₁ (fun i : Fin n => i.val) U / n)
        (hitCount p₂ (fun i : Fin n => n+i.val) U / n)) := by
  dsimp only
  let n := calibrationSamples T η δ est
  let F := calibrationProc T η δ est off w z
  let y₁ := (z.1,w.2)
  let y₂ := (w.1,z.2)
  have hs := calibration_stopped T η δ est off w z prob U
  have he : ∃ k, F.stopped prob () U k := ⟨2*n, (hs _).2 le_rfl⟩
  have hfind : Nat.find he = 2*n :=
    le_antisymm (Nat.find_min' he ((hs _).2 le_rfl)) ((hs _).1 (Nat.find_spec he))
  change F.out prob () U = _
  rw [Proc.out, dif_pos he, hfind, calibration_history]
  change (F.step () (calibrationHistory n (min (2*n) (2*n)) y₁ y₂ prob U)).getRight? = _
  rw [min_self]
  have hstep (h : CalibrationHistory) : F.step () h = calibrationStep n off y₁ y₂ h := rfl
  rw [hstep]
  have hlen : (calibrationHistory n (2*n) y₁ y₂ prob U).length = 2*n := by simp [calibrationHistory]
  unfold calibrationStep
  simp only [hlen, if_neg (show ¬ (2*n < n) by omega), lt_irrefl, if_false, Sum.getRight?]
  have hf (j : ℕ) (hj : j = 0 ∨ j = n) :
      historyFrequency n j (calibrationHistory n (2*n) y₁ y₂ prob U)
        = hitCount (prob (if j = 0 then y₁ else y₂)) (fun i : Fin n => j+i.val) U / n := by
    unfold historyFrequency hitCount
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    have hi := i.isLt
    have hji : j + i.val < (calibrationHistory n (2*n) y₁ y₂ prob U).length := by
      rw [hlen]
      rcases hj with rfl | rfl <;> omega
    rw [List.getElem?_eq_getElem hji, Option.getD_some]
    simp only [calibrationHistory, List.getElem_ofFn, hit]
    rcases hj with rfl | rfl
    · simp [hi]
    · have hn : ¬ n + i.val < n := by omega
      have hn' : n ≠ 0 := by omega
      simp [hn, hn']
  rw [hf 0 (.inl rfl)]
  by_cases hn : n = 0
  · simp [hn, show calibrationSamples T η δ est = 0 from hn, historyFrequency, hitCount]
  · rw [hf n (.inr rfl)]
    simp only [hn, if_false, if_true, zero_add]
    rfl

end BilateralProfitRegular.Factory
end BundlePart007


section BundlePart008


namespace BilateralProfitRegular.Factory

open Classical MeasureTheory Set MechanismDesign.BilateralTrade
open scoped BigOperators ENNReal

set_option maxHeartbeats 900000

private theorem calibration_T_ge_two (T : ℕ) (η : ℝ) (hη : 0 < η) (hη' : η < 1)
    (hT : gridK η ≤ T) : 2 ≤ T := by
  have hK : 1 < gridK η := by
    by_contra! hK
    have hd : 1 < 1/η := (lt_div_iff₀ hη).2 (by linarith)
    exact (not_le_of_gt hd) (le_trans (Nat.le_ceil (1/η)) (by exact_mod_cast hK))
  omega

private theorem calibration_samples_pos (T : ℕ) (hT : 2 ≤ T) (η δ est : ℝ)
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < est) : 0 < calibrationSamples T η δ est := by
  have hTr : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hlog : 0 < Real.log (2 * (T : ℝ)) := Real.log_pos (by linarith)
  have hceil := Nat.le_ceil (1000000000 * δ * Real.log (2 * (T : ℝ)) / (η * est))
  have hpos : (0 : ℝ) < calibrationSamples T η δ est :=
    (by positivity : 0 < 1000000000 * δ * Real.log (2 * (T : ℝ)) / (η * est)).trans_le hceil
  exact_mod_cast hpos

private theorem calibration_samples_le (T : ℕ) (hT : 2 ≤ T) (η δ est : ℝ)
    (hη : 0 < η) (hη' : η < 1) (hδ : 0 < δ) (he : δ ≤ est) :
    2 * (calibrationSamples T η δ est : ℝ) ≤ 5000000000 * Real.log T / η := by
  have hTr : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hTpos : 0 < (T : ℝ) := by linarith
  have hlog : 0 < Real.log (2 * (T : ℝ)) := Real.log_pos (by linarith)
  have hlogT : (1/2 : ℝ) ≤ Real.log T := (by
    linarith [Real.log_two_gt_d9] : (1/2 : ℝ) ≤ Real.log 2).trans
      (Real.log_le_log (by norm_num) hTr)
  have hlog' : Real.log (2 * (T : ℝ)) ≤ 2 * Real.log T := by
    rw [Real.log_mul (by norm_num) hTpos.ne']
    linarith [Real.log_le_log (show (0 : ℝ) < 2 by norm_num) hTr]
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ 1000000000 * δ *
    Real.log (2 * (T : ℝ)) / (η * est) by have := hδ.trans_le he; positivity)
  have hfrac : 1000000000 * δ * Real.log (2 * (T : ℝ)) / (η * est) ≤
      2000000000 * Real.log T / η := by
    apply (div_le_div_iff₀ (mul_pos hη (hδ.trans_le he)) hη).mpr
    have hmain : δ * Real.log (2 * (T : ℝ)) ≤ est * (2 * Real.log T) :=
      mul_le_mul he hlog' hlog.le (hδ.trans_le he).le
    nlinarith [mul_le_mul_of_nonneg_right hmain hη.le]
  have hone : (1 / 2 : ℝ) ≤ Real.log T / η := by
    apply (le_div_iff₀ hη).mpr
    linarith
  have hceil' : (calibrationSamples T η δ est : ℝ) <
      1000000000 * δ * Real.log (2 * (T : ℝ)) / (η * est) + 1 := hceil
  apply le_trans (show 2 * (calibrationSamples T η δ est : ℝ) ≤
      2 * (2000000000 * Real.log T / η + 1) by linarith)
  rw [show (5000000000 : ℝ) * Real.log T / η = 5000000000 * (Real.log T / η) by ring]
  rw [show (2000000000 : ℝ) * Real.log T / η = 2000000000 * (Real.log T / η) by ring]
  linarith

private theorem log_ratio_close {f p ε : ℝ} (hp : 0 < p) (hε : ε ≤ 1/2)
    (h : |f/p-1| ≤ ε) : 0 < f ∧ |Real.log (f/p)| ≤ 2*ε := by
  have hfp : 0 < f/p := by linarith [(abs_le.mp h).1]
  have hf : 0 < f := (div_pos_iff.mp hfp).resolve_right (fun hneg => (not_lt_of_gt hp) hneg.2) |>.1
  let t := f/p - 1
  have ht : |t| ≤ ε := h
  have hlt : |-t| < 1 := by rw [abs_neg]; linarith
  have hb := Real.abs_log_sub_add_sum_range_le hlt 0
  simp only [Finset.range_zero, Finset.sum_empty, zero_add, zero_add, pow_one, abs_neg] at hb
  have he : 1 - -t = f/p := by unfold t; ring
  rw [he] at hb
  refine ⟨hf, hb.trans ?_⟩
  have hden : 0 < 1 - |t| := by linarith
  apply (div_le_iff₀ hden).mpr
  have hε₀ : 0 ≤ ε := (abs_nonneg t).trans ht
  have hden' : (1/2 : ℝ) ≤ 1 - |t| := by linarith
  have hmul := mul_le_mul_of_nonneg_left hden' (by positivity : 0 ≤ 2*ε)
  linarith

private theorem calibration_valid_of_relative (E : Environment) (hE : RegularUnit E)
    (c : Candidate) (δ η : ℝ) (hc : c.Valid E δ) (z : CalibrationPrices)
    (hz : z ∈ c.region) (ε : ℝ) (hε : ε ≤ 1/2)
    (hε' : 2*ε ≤ 1/1000 * Real.sqrt (η/δ))
    (f₁ f₂ : ℝ)
    (hp₁ : 0 < P E (z.1,c.root.2)) (hp₂ : 0 < P E (c.root.1,z.2))
    (h₁ : |f₁ / P E (z.1,c.root.2) - 1| ≤ ε)
    (h₂ : |f₂ / P E (c.root.1,z.2) - 1| ≤ ε) :
    CalibValid E η δ c z (calibrationValue c.offset f₁ f₂) := by
  let p₁ := P E (z.1,c.root.2)
  let p₂ := P E (c.root.1,z.2)
  have hz' := hc.1 hz
  have hw' := hc.1 hc.2.2.2.1
  have bz := balance_pos E hE.1 hz'
  have bw := balance_pos E hE.1 hw'
  rcases log_ratio_close hp₁ hε h₁ with ⟨hf₁,hl₁⟩
  rcases log_ratio_close hp₂ hε h₂ with ⟨hf₂,hl₂⟩
  let ρ := calibrationValue c.offset f₁ f₂
  have hρ : 0 < ρ := Real.exp_pos _
  refine ⟨hρ,?_⟩
  have hEq := eq_47 E hE z c.root hz' hw'
  change |Real.log (ρ * balance E z / c.param E)| ≤ _
  have hlog : Real.log (ρ * balance E z / c.param E) =
      (1/2) * (Real.log (f₂/p₂) - Real.log (f₁/p₁)) := by
    rw [Candidate.param, Real.log_div (mul_pos hρ bz).ne' (mul_pos (Real.exp_pos _) bw).ne',
      Real.log_mul hρ.ne' bz.ne', Real.log_mul (Real.exp_pos _).ne' bw.ne', Real.log_exp]
    have hdiff : Real.log (balance E z) - Real.log (balance E c.root) =
        (1/2) * Real.log (p₁/p₂) := by
      rw [← Real.log_div bz.ne' bw.ne']
      exact hEq
    change Real.log (Real.exp (c.offset-(1/2)*Real.log (f₁/f₂))) +
      Real.log (balance E z) - (c.offset + Real.log (balance E c.root)) = _
    rw [Real.log_exp, Real.log_div hf₁.ne' hf₂.ne', Real.log_div hf₂.ne' hp₂.ne',
      Real.log_div hf₁.ne' hp₁.ne']
    rw [Real.log_div hp₁.ne' hp₂.ne'] at hdiff
    linarith
  rw [hlog, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)]
  calc
    _ ≤ (1/2) * (|Real.log (f₂/p₂)| + |Real.log (f₁/p₁)|) :=
      mul_le_mul_of_nonneg_left (by simpa using abs_sub_le (Real.log (f₂/p₂)) 0 (Real.log (f₁/p₁))) (by norm_num)
    _ ≤ 2*ε := by linarith
    _ ≤ _ := hε'

private theorem calibration_tail_exp {T : ℕ} (hT : 2 ≤ T) {η δ est p : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < est) (hp : est / 10 ≤ p) :
    Real.exp (-((calibrationSamples T η δ est : ℝ)*p*(Real.sqrt (η/δ)/2000)^2/4)) ≤
      1 / (4 * (T : ℝ)) := by
  let n := calibrationSamples T η δ est
  let L := Real.log (2 * (T : ℝ))
  have hTr : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hT₀ : 0 < (T : ℝ) := by linarith
  have hL : 0 ≤ L := (Real.log_pos (by linarith : 1 < 2 * (T : ℝ))).le
  have hn := Nat.le_ceil (1000000000 * δ * L / (η * est))
  change _ ≤ (n : ℝ) at hn
  have hmul := (div_le_iff₀ (mul_pos hη he)).1 hn
  have hmul' : (n : ℝ)*η*est ≤ (n : ℝ)*η*(10*p) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hbound : (100000000 : ℝ) * δ * L ≤ (n : ℝ)*η*p := by nlinarith
  have heps : (Real.sqrt (η/δ) / 2000)^2 = (η/δ)/4000000 := by
    rw [div_pow, Real.sq_sqrt (by positivity)]
    norm_num
  have hbig : 2 * L ≤ (n : ℝ)*p*(Real.sqrt (η/δ)/2000)^2/4 := by
    rw [heps]
    have hr : (n : ℝ) * p * (η / δ / 4000000) / 4 =
        ((n : ℝ)*η*p) / (16000000*δ) := by ring
    rw [hr]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 16000000*δ)).2
    nlinarith [mul_nonneg hδ.le hL]
  calc
    _ ≤ Real.exp (-(2 * L)) := Real.exp_le_exp.mpr (by exact neg_le_neg hbig)
    _ = 1 / (2 * (T : ℝ))^2 := by
      rw [Real.exp_neg, show 2*L = L+L by ring, Real.exp_add, show Real.exp L = 2*(T : ℝ)
        from Real.exp_log (by positivity), one_div, pow_two]
    _ ≤ _ := by
      gcongr
      nlinarith [mul_nonneg (show 0 ≤ (T : ℝ) by positivity)
        (show 0 ≤ (T : ℝ) - 1 by linarith)]

private theorem calibration_failure_le (T : ℕ) (η : ℝ) (hη : 0 < η) (hη' : η < 1) (hT : gridK η ≤ T)
    (E : Environment) (hE : RegularUnit E) (δ : ℝ) (hηδ : η < δ)
    (c : Candidate) (hc : c.Valid E δ) (z : CalibrationPrices) (hz : z ∈ c.region) :
    Proc.law (Measure.dirac ()) {s | ¬ ∃ r,
      (calibrationProc T η δ c.est c.offset c.root z).out (P E) s.1 s.2 = some r ∧
        CalibValid E η δ c z r} ≤ ENNReal.ofReal (1 / (T : ℝ)) := by
  let F := calibrationProc T η δ c.est c.offset c.root z
  let n := calibrationSamples T η δ c.est
  let p₁ := P E (z.1,c.root.2)
  let p₂ := P E (c.root.1,z.2)
  let ε := Real.sqrt (η/δ) / 2000
  have hδ := hη.trans hηδ
  have he := hδ.trans_le hc.2.2.2.2.2.2.1
  have hT' := calibration_T_ge_two T η hη hη' hT
  have hn : 0 < n := calibration_samples_pos T hT' η δ c.est hη hδ he
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hεhalf : ε ≤ 1/2 := by
    have hS : Real.sqrt (η/δ) ≤ 1 := by
      apply Real.sqrt_le_iff.mpr
      exact ⟨by norm_num, by norm_num; exact (div_le_one hδ).2 hηδ.le⟩
    unfold ε
    linarith
  have hε' : 2*ε ≤ (1/1000)*Real.sqrt (η/δ) := by unfold ε; ring_nf; rfl
  have cross := hc.2.2.2.2.2.1 z hz c.root hc.2.2.2.1
  have hp₁ : c.est/10 ≤ p₁ := (cross.2.2 _ (by simp)).1
  have hp₂ : c.est/10 ≤ p₂ := (cross.2.2 _ (by simp)).1
  have hp₁' : 0 < p₁ := (by positivity : 0 < c.est/10).trans_le hp₁
  have hp₂' : 0 < p₂ := (by positivity : 0 < c.est/10).trans_le hp₂
  let coord₁ := fun i : Fin n => i.val
  let coord₂ := fun i : Fin n => n+i.val
  have hcoord₁ : Function.Injective coord₁ := fun i j h => Fin.ext h
  have hcoord₂ : Function.Injective coord₂ := fun i j h => Fin.ext (Nat.add_left_cancel h)
  let A := {U : Stream | ε < |(hitCount p₁ coord₁ U / n) / p₁ - 1|}
  let B := {U : Stream | ε < |(hitCount p₂ coord₂ U / n) / p₂ - 1|}
  have hA : MeasurableSet A := by
    unfold A
    exact measurableSet_lt measurable_const
      (((measurable_hitCount p₁ coord₁).div_const _).div_const _ |>.sub_const _ |>.abs)
  have hB : MeasurableSet B := by
    unfold B
    exact measurableSet_lt measurable_const
      (((measurable_hitCount p₂ coord₂).div_const _).div_const _ |>.sub_const _ |>.abs)
  have hbound (p : ℝ) (hpl : c.est / 10 ≤ p) (hpu : p ≤ 1)
      (coord : Fin n → ℕ) (hj : Function.Injective coord) :
      Proc.coinLaw {U | ε < |(hitCount p coord U / n) / p - 1|} ≤
        2 * ENNReal.ofReal (1 / (4*(T : ℝ))) := by
    have hp : 0 < p := (by positivity : 0 < c.est/10).trans_le hpl
    apply (hitCount_relative_tail hn hp hpu hε (by linarith) coord hj).trans
    gcongr
    exact calibration_tail_exp hT' hη hδ he hpl
  have hset : {s | ¬ ∃ r, F.out (P E) s.1 s.2 = some r ∧ CalibValid E η δ c z r} ⊆
      Prod.snd ⁻¹' (A ∪ B) := by
    rintro ⟨⟨⟩,U⟩ hU
    by_contra hbad
    have h_A : U ∉ A := fun h => hbad (.inl h)
    have h_B : U ∉ B := fun h => hbad (.inr h)
    have h₁ : |(hitCount p₁ coord₁ U / n) / p₁ - 1| ≤ ε := le_of_not_gt h_A
    have h₂ : |(hitCount p₂ coord₂ U / n) / p₂ - 1| ≤ ε := le_of_not_gt h_B
    exact hU ⟨_,calibration_out T η δ c.est c.offset c.root z (P E) U,
      calibration_valid_of_relative E hE c δ η hc z hz ε hεhalf hε' _ _ hp₁' hp₂' h₁ h₂⟩
  change Proc.law (Measure.dirac ()) {s | ¬ ∃ r, F.out (P E) s.1 s.2 = some r ∧
    CalibValid E η δ c z r} ≤ _
  calc
    _ ≤ Proc.law (Measure.dirac ()) (Prod.snd ⁻¹' (A ∪ B)) := measure_mono hset
    _ = Proc.coinLaw (A ∪ B) := by
      rw [Proc.law, ← Measure.map_apply measurable_snd (hA.union hB), Measure.map_snd_prod]
      simp
    _ ≤ _ := by
      have ht : 0 ≤ 1 / (4 * (T : ℝ)) := by positivity
      calc
        _ ≤ Proc.coinLaw A + Proc.coinLaw B := measure_union_le _ _
        _ ≤ _ + _ := add_le_add
          (hbound p₁ hp₁ ((onUnit_facts E hE.1).1 _).2 coord₁ hcoord₁)
          (hbound p₂ hp₂ ((onUnit_facts E hE.1).1 _).2 coord₂ hcoord₂)
        _ = _ := by
          have htwo : (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) := by norm_num
          rw [htwo, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring

end BilateralProfitRegular.Factory
end BundlePart008


section BundlePart009


namespace BilateralProfitRegular.Factory

open Classical MeasureTheory ProbabilityTheory
open scoped BigOperators

private abbrev Inputs := ℕ → Input

private noncomputable def streamLaw : Measure Inputs := Measure.infinitePi fun _ => inputLaw

private instance : IsProbabilityMeasure streamLaw := by
  unfold streamLaw
  infer_instance

private def initial : State := .inr (0, 1)

private theorem initial_admissible : admissible initial := by norm_num [admissible, initial, boundary]

private noncomputable def follow (m : Mixing) (p : ℝ) :
    (n : ℕ) → (Fin n → Input) → State
  | 0, _ => initial
  | n + 1, v => update m p (follow m p n (fun i => v i.castSucc)) (v (Fin.last n))

@[fun_prop]
private theorem measurable_follow (m : Mixing) (p : ℝ) (n : ℕ) :
    Measurable (follow m p n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (measurable_update m p).comp ((ih.comp (by fun_prop)).prodMk (by fun_prop))

private noncomputable def run (m : Mixing) (p : ℝ) (n : ℕ) (x : Inputs) : State :=
  follow m p n (fun i => x i)

private theorem run_zero (m : Mixing) (p : ℝ) (x : Inputs) : run m p 0 x = initial := rfl

private theorem run_succ (m : Mixing) (p : ℝ) (n : ℕ) (x : Inputs) :
    run m p (n + 1) x = update m p (run m p n x) (x n) := rfl

@[fun_prop]
private theorem measurable_run (m : Mixing) (p : ℝ) (n : ℕ) :
    Measurable (run m p n) := by
  unfold run
  exact (measurable_follow m p n).comp (by fun_prop)

private theorem run_admissible (m : Mixing) (p : ℝ) (x : Inputs) (n : ℕ) :
    admissible (run m p n x) := by
  induction n with
  | zero => exact initial_admissible
  | succ n ih =>
    rw [run_succ]
    exact select_admissible _ _ _ ih

private theorem run_absorbed (m : Mixing) (p : ℝ) (x : Inputs) {n : ℕ} {d : Bool}
    (h : run m p n x = .inl d) {k : ℕ} (hnk : n ≤ k) : run m p k x = .inl d := by
  induction k, hnk using Nat.le_induction with
  | base => exact h
  | succ k hk ih => rw [run_succ, ih]; rfl

private theorem run_stage_le (m : Mixing) (p : ℝ) (x : Inputs) (n : ℕ) {j k : ℕ}
    (h : run m p n x = .inr (j,k)) : j ≤ n := by
  induction n generalizing j k with
  | zero =>
    simp only [run_zero, initial, Sum.inr.injEq, Prod.mk.injEq] at h
    omega
  | succ n ih =>
    rw [run_succ] at h
    cases hs : run m p n x with
    | inl d => simp [hs, update, select] at h
    | inr jk =>
      rcases jk with ⟨j',k'⟩
      have hj := ih hs
      rw [hs] at h
      simp only [update, select] at h
      split at h
      · unfold down at h
        split at h <;> simp_all
        omega
      · split at h
        · unfold up at h
          split at h <;> simp_all <;> omega
        · split at h <;> simp_all
          omega

private theorem run_indep (m : Mixing) (p : ℝ) (n : ℕ) :
    IndepFun (run m p n) (fun x : Inputs => x n) streamLaw := by
  have hi : iIndepFun (fun i (x : Inputs) => x i) streamLaw :=
    iIndepFun_infinitePi (X := fun _ x => x) (by fun_prop)
  have hd : Disjoint (Finset.range n) ({n} : Finset ℕ) := by simp
  have h := hi.indepFun_finset (Finset.range n) {n} hd (by fun_prop)
  let f : ((i : Finset.range n) → Input) → State :=
    fun r => follow m p n (fun (i : Fin n) => r ⟨i, Finset.mem_range.mpr i.isLt⟩)
  let g : ((i : ({n} : Finset ℕ)) → Input) → Input :=
    fun r => r ⟨n, Finset.mem_singleton_self n⟩
  have hf : Measurable f := (measurable_follow m p n).comp (by fun_prop)
  have hg : Measurable g := by unfold g; fun_prop
  exact h.comp hf hg

private theorem integral_run_succ (m : Mixing) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (n : ℕ)
    (f : State → ℝ) (hf : Integrable (fun x => f (run m p (n+1) x)) streamLaw) :
    (∫ x, f (run m p (n+1) x) ∂streamLaw) =
      ∫ x, expectation (mix p m.downWeight) (mix p m.upWeight) f (run m p n x) ∂streamLaw := by
  let G := fun x : Inputs => (run m p n x, x n)
  let F := fun sr : State × Input => f (update m p sr.1 sr.2)
  have hG : Measurable G := by unfold G; fun_prop
  have hF : Measurable F := (measurable_of_countable f).comp (measurable_update m p)
  have hcomp : Integrable (F ∘ G) streamLaw := by simpa [F, G, Function.comp_def, run_succ] using hf
  have hprod : streamLaw.map G = (streamLaw.map (run m p n)).prod inputLaw := by
    rw [(run_indep m p n).map_prod_eq_prod_map_map (measurable_run m p n).aemeasurable
      (measurable_pi_apply n).aemeasurable]
    exact congrArg _ (Measure.infinitePi_map_eval _ _)
  have hFint : Integrable F ((streamLaw.map (run m p n)).prod inputLaw) := by
    rw [← hprod]
    exact (integrable_map_measure hF.aestronglyMeasurable hG.aemeasurable).2 hcomp
  calc
    _ = ∫ sr, F sr ∂(streamLaw.map G) := by
      rw [integral_map hG.aemeasurable hF.aestronglyMeasurable]
      simp only [G, F, run_succ]
    _ = ∫ s, (∫ r, f (update m p s r) ∂inputLaw) ∂(streamLaw.map (run m p n)) := by
      rw [hprod, integral_prod _ hFint]
    _ = _ := by
      simp_rw [integral_update m hp hp']
      rw [integral_map (by fun_prop) (measurable_of_countable _).aestronglyMeasurable]

private noncomputable def historyStep (m : Mixing) (ω : Stream) :
    State × ℕ → Unit × Bool → State × ℕ :=
  fun z q => (select m (ω z.2) q.2 z.1, z.2 + 1)

private noncomputable def replay (m : Mixing) (ω : Stream) (h : List (Unit × Bool)) : State :=
  (h.foldl (historyStep m ω) (initial, 0)).1

private theorem fold_length (m : Mixing) (ω : Stream) (z : State × ℕ) (h : List (Unit × Bool)) :
    (h.foldl (historyStep m ω) z).2 = z.2 + h.length := by
  induction h generalizing z with
  | nil => simp
  | cons q h ih => rw [List.foldl_cons, ih]; simp [historyStep]; omega

private theorem replay_append (m : Mixing) (ω : Stream) (h : List (Unit × Bool)) (t : Bool) :
    replay m ω (h ++ [((),t)]) = select m (ω h.length) t (replay m ω h) := by
  simp [replay, List.foldl_append, historyStep, fold_length]

@[fun_prop]
private theorem measurable_replay (m : Mixing) (h : List (Unit × Bool)) :
    Measurable (fun ω => replay m ω h) := by
  induction h using List.reverseRecOn with
  | nil => exact measurable_const
  | append_singleton h q ih =>
    rcases q with ⟨⟨⟩,t⟩
    simp only [replay_append]
    exact (measurable_from_prod_countable_right (f := fun sr : State × Uniform =>
      select m sr.2 t sr.1) (fun s => measurable_select m t s)).comp
      (ih.prodMk (measurable_pi_apply h.length))

private def queryOrFinish : State → Unit ⊕ Bool
  | .inl d => .inr d
  | .inr _ => .inl ()

private noncomputable def procedure (m : Mixing) : Proc Unit Bool Stream where
  step ω h := queryOrFinish (replay m ω h)
  measurable_step h := (measurable_of_countable queryOrFinish).comp (measurable_replay m h)

private theorem run_eq_replay (m : Mixing) (p : ℝ) (ω U : Stream) (n : ℕ) :
    let h := (procedure m).hist (fun _ => p) ω U n
    let s := run m p n (pairAt (ω,U))
    replay m ω h = s ∧ (s.isRight = true → h.length = n) := by
  induction n with
  | zero => simp [Proc.hist, replay, run_zero]
  | succ n ih =>
    dsimp only at ih ⊢
    rcases ih with ⟨ih,hlen⟩
    have hstep : (procedure m).step ω ((procedure m).hist (fun _ => p) ω U n) =
        queryOrFinish (run m p n (pairAt (ω,U))) := by
      change queryOrFinish (replay m ω ((procedure m).hist (fun _ => p) ω U n)) = _
      rw [ih]
    rw [Proc.hist, run_succ, hstep]
    cases hs : run m p n (pairAt (ω,U)) with
    | inl d =>
      simp [queryOrFinish, update, select, ih]
      exact hs
    | inr jk =>
      have hl := hlen (by simp [hs])
      rw [queryOrFinish, replay_append, hl]
      simp [update, pairAt, ih, hs, hl]
      rfl

private theorem stopped_iff (m : Mixing) (p : ℝ) (ω U : Stream) (n : ℕ) :
    (procedure m).stopped (fun _ => p) ω U n ↔
      ∃ d, run m p n (pairAt (ω,U)) = .inl d := by
  unfold Proc.stopped
  change (queryOrFinish (replay m ω ((procedure m).hist (fun _ => p) ω U n))).isRight = true ↔ _
  rw [(run_eq_replay m p ω U n).1]
  cases run m p n (pairAt (ω,U)) <;> simp [queryOrFinish]

private theorem rounds_eq_find (m : Mixing) (p : ℝ) (ω U : Stream)
    (h : ∃ n, (procedure m).stopped (fun _ => p) ω U n) :
    (procedure m).rounds (fun _ => p) ω U = (Nat.find h : ℕ∞) := by
  unfold Proc.rounds
  apply le_antisymm
  · exact iInf_le_of_le (Nat.find h) (iInf_le _ (Nat.find_spec h))
  · refine le_iInf fun n => le_iInf fun hn => ?_
    exact_mod_cast Nat.find_min' h hn

private theorem rounds_eq_top (m : Mixing) (p : ℝ) (ω U : Stream)
    (h : ¬ ∃ n, (procedure m).stopped (fun _ => p) ω U n) :
    (procedure m).rounds (fun _ => p) ω U = ⊤ := by
  unfold Proc.rounds
  simp [not_exists.mp h]

private theorem rounds_eq_sum (m : Mixing) (p : ℝ) (ω U : Stream) :
    ((procedure m).rounds (fun _ => p) ω U : ENNReal) =
      ∑' n : ℕ, ENNReal.ofReal (running (run m p n (pairAt (ω,U)))) := by
  by_cases h : ∃ n, (procedure m).stopped (fun _ => p) ω U n
  · rw [rounds_eq_find m p ω U h]
    have hr (n : ℕ) : ENNReal.ofReal (running (run m p n (pairAt (ω,U)))) =
        if n < Nat.find h then 1 else 0 := by
      by_cases hn : n < Nat.find h
      · have hstop := Nat.find_min h hn
        rw [stopped_iff] at hstop
        cases hs : run m p n (pairAt (ω,U)) with
        | inl d => exact (hstop ⟨d,hs⟩).elim
        | inr jk => simp [running, hn]
      · rcases (stopped_iff m p ω U _).mp (Nat.find_spec h) with ⟨d,hd⟩
        rw [run_absorbed _ _ _ hd (Nat.le_of_not_gt hn)]
        simp [running, hn]
    simp_rw [hr]
    have hr' : (fun n => if n < Nat.find h then (1 : ENNReal) else 0) =
        (Finset.range (Nat.find h) : Set ℕ).indicator (fun _ => 1) := by
      ext n
      simp [Set.indicator]
    rw [hr']
    have hsum (k : ℕ) :
        (∑' n, (Finset.range k : Set ℕ).indicator (fun _ => (1 : ENNReal)) n) = k := by
      rw [tsum_eq_sum (s := Finset.range k)]
      · calc
          _ = ∑ j ∈ Finset.range k, (1 : ENNReal) := by
            exact Finset.sum_congr rfl (fun j hj => Set.indicator_of_mem hj _)
          _ = k := by simp
      · exact fun j hj => Set.indicator_of_notMem hj _
    rw [hsum]
    simp
  · rw [rounds_eq_top m p ω U h]
    have hr (n : ℕ) : ENNReal.ofReal (running (run m p n (pairAt (ω,U)))) = 1 := by
      cases hs : run m p n (pairAt (ω,U)) with
      | inl d => exact (h ⟨n, (stopped_iff _ _ _ _ _).mpr ⟨d,hs⟩⟩).elim
      | inr jk => simp [running]
    simp_rw [hr]
    exact (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm

end BilateralProfitRegular.Factory
end BundlePart009


section BundlePart010


namespace BilateralProfitRegular.Factory

open Classical MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal BigOperators

private theorem boundary_mono : Monotone boundary :=
  monotone_nat_of_le_succ (fun j => by rw [boundary_succ]; omega)

private theorem run_budget_bound (m : Mixing) (p : ℝ) {b : ℝ} (hb : 0 < b) (n : ℕ) (x : Inputs) :
    budget b (run m p n x) ≤ 6 / b * (2 * boundary n) := by
  cases hs : run m p n x with
  | inl d =>
    simp only [budget]
    positivity
  | inr jk =>
    rcases jk with ⟨j,k⟩
    have hj := boundary_mono (run_stage_le m p x n hs)
    have : (boundary j : ℝ) ≤ boundary n := by exact_mod_cast hj
    simp only [budget]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hk : 0 ≤ (k : ℝ) := by positivity
    linarith

private theorem running_nonneg (s : State) : 0 ≤ running s := by cases s <;> norm_num [running]
private theorem running_le_one (s : State) : running s ≤ 1 := by cases s <;> norm_num [running]

private theorem integrable_bounded_run (m : Mixing) (p : ℝ) (n : ℕ) (f : State → ℝ) (K : ℝ)
    (h : ∀ x : Inputs, 0 ≤ f (run m p n x) ∧ f (run m p n x) ≤ K) :
    Integrable (fun x => f (run m p n x)) streamLaw := by
  have hf : Measurable (fun x => f (run m p n x)) :=
    (measurable_of_countable f).comp (measurable_run m p n)
  apply Integrable.of_bound hf.aestronglyMeasurable K
  exact Eventually.of_forall fun x => by simpa [Real.norm_eq_abs, abs_of_nonneg (h x).1] using (h x).2

private theorem expectation_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1)
    (f : State → ℝ) (hf : ∀ s, admissible s → 0 ≤ f s)
    {s : State} (hs : admissible s) : 0 ≤ expectation a b f s := by
  rcases s with (d | ⟨j,k⟩)
  · exact hf _ hs
  · have hu : 0 ≤ b / scale j := div_nonneg hb (scale_pos j).le
    have hu' : b / scale j ≤ b := div_le_self hb (scale_one_le j)
    rw [expectation]
    exact add_nonneg
      (add_nonneg (mul_nonneg ha (hf _ (admissible_down hs)))
        (mul_nonneg hu
          (add_nonneg (mul_nonneg (continueUp_nonneg j k) (hf _ (admissible_up hs)))
            (mul_nonneg (sub_nonneg.mpr (continueUp_le_one j k)) (hf _ trivial)))))
      (mul_nonneg (by linarith) (hf _ hs))

private noncomputable def totalRounds (m : Mixing) (p : ℝ) (x : Inputs) : ENNReal :=
  ∑' n, ENNReal.ofReal (running (run m p n x))

@[fun_prop]
private theorem measurable_totalRounds (m : Mixing) (p : ℝ) :
    Measurable (totalRounds m p) := by
  unfold totalRounds
  exact Measurable.tsum fun n =>
    ENNReal.measurable_ofReal.comp ((measurable_of_countable running).comp (measurable_run m p n))

private theorem never_finishes_iff (m : Mixing) (p : ℝ) (x : Inputs) :
    (¬ ∃ n d, run m p n x = .inl d) ↔ totalRounds m p x = ⊤ := by
  constructor
  · intro h
    have hn (n : ℕ) : ENNReal.ofReal (running (run m p n x)) = 1 := by
      cases hs : run m p n x with
      | inl d => exact (h ⟨n,d,hs⟩).elim
      | inr jk => simp [running]
    unfold totalRounds
    simp_rw [hn]
    exact ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero
  · intro h hx
    rcases hx with ⟨n,d,hd⟩
    have hm : totalRounds m p x ≤ n := by
      unfold totalRounds
      rw [tsum_eq_sum (s := Finset.range n)]
      · calc
          _ ≤ ∑ _ ∈ Finset.range n, (1 : ENNReal) := by
            gcongr with j _
            simpa using ENNReal.ofReal_le_ofReal (running_le_one (run m p j x))
          _ = n := by simp
      · intro k hk
        have hnk : n ≤ k := by simpa [Finset.mem_range] using hk
        rw [run_absorbed _ _ _ hd hnk]
        simp [running]
    simp [h] at hm

private theorem lintegral_rounds_le (m : Mixing) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (hb : 0 < mix p m.upWeight) (hab : 2 * mix p m.downWeight ≤ mix p m.upWeight) :
    (∫⁻ x, totalRounds m p x ∂streamLaw) ≤ ENNReal.ofReal (282 / mix p m.upWeight) := by
  let a := mix p m.downWeight
  let b := mix p m.upWeight
  have ha : 0 ≤ a := add_nonneg (mul_nonneg hp (m.down_nonneg true))
    (mul_nonneg (sub_nonneg.mpr hp') (m.down_nonneg false))
  have hab' : a + b ≤ 1 := by
    change mix p m.downWeight + mix p m.upWeight ≤ 1
    have ht := mul_le_mul_of_nonneg_left (m.sum_le_one true) hp
    have hf := mul_le_mul_of_nonneg_left (m.sum_le_one false) (sub_nonneg.mpr hp')
    unfold mix
    linarith
  let R := fun n x => running (run m p n x)
  let B := fun n x => budget b (run m p n x)
  have hR₀ (n : ℕ) (x : Inputs) : 0 ≤ R n x := running_nonneg _
  have hB₀ (n : ℕ) (x : Inputs) : 0 ≤ B n x :=
    budget_nonneg hb (run_admissible m p x n)
  have hR (n : ℕ) : Integrable (R n) streamLaw :=
    integrable_bounded_run m p n running 1 (fun _ => ⟨running_nonneg _, running_le_one _⟩)
  have hB (n : ℕ) : Integrable (B n) streamLaw :=
    integrable_bounded_run m p n (budget b) _ (fun x => ⟨hB₀ n x, run_budget_bound m p hb n x⟩)
  have hstep (n : ℕ) :
      (∫ x, B (n+1) x ∂streamLaw) + (∫ x, R n x ∂streamLaw) ≤ ∫ x, B n x ∂streamLaw := by
    rw [integral_run_succ m hp hp' n (budget b) (hB (n+1))]
    have hE : Integrable (fun x => expectation a b (budget b) (run m p n x)) streamLaw := by
      refine integrable_bounded_run m p n _ (6 / b * (2 * boundary n)) fun x => ⟨?_,?_⟩
      · exact expectation_nonneg ha hb.le hab' _ (fun _ hs => budget_nonneg hb hs)
          (run_admissible m p x n)
      · have hd := expectation_budget ha hb hab (run_admissible m p x n)
        have hbound := run_budget_bound m p hb n x
        linarith [hR₀ n x]
    rw [← integral_add hE (hR n)]
    apply integral_mono (hE.add (hR n)) (hB n)
    intro x
    exact expectation_budget ha hb hab (run_admissible m p x n)
  have hbase : (∫ x, B 0 x ∂streamLaw) = 282 / b := by
    simp only [B, run_zero, initial, budget, boundary, pow_zero, mul_one, Nat.cast_ofNat,
      Nat.cast_one, integral_const, probReal_univ, one_smul]
    ring
  have hsum (n : ℕ) :
      (∑ i ∈ Finset.range n, ∫ x, R i x ∂streamLaw) + (∫ x, B n x ∂streamLaw) ≤ 282 / b := by
    induction n with
    | zero => simp [hbase]
    | succ n ih =>
      rw [Finset.sum_range_succ]
      linarith [hstep n]
  unfold totalRounds
  rw [lintegral_tsum (fun n => ((hR n).aemeasurable.ennreal_ofReal)), ENNReal.tsum_eq_iSup_nat]
  apply iSup_le
  intro n
  simp_rw [← ofReal_integral_eq_lintegral_ofReal (hR _) (Eventually.of_forall (hR₀ _))]
  have hRInt₀ (i : ℕ) : 0 ≤ ∫ x, R i x ∂streamLaw := integral_nonneg (hR₀ i)
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hRInt₀ i)]
  apply ENNReal.ofReal_le_ofReal
  have hBI : 0 ≤ ∫ x, B n x ∂streamLaw := integral_nonneg (hB₀ n)
  linarith [hsum n]

private theorem stream_finishes_ae (m : Mixing) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (hb : 0 < mix p m.upWeight) (hab : 2 * mix p m.downWeight ≤ mix p m.upWeight) :
    ∀ᵐ x ∂streamLaw, ∃ n d, run m p n x = .inl d := by
  have hbound := lintegral_rounds_le m hp hp' hb hab
  have hfinite : (∫⁻ x, totalRounds m p x ∂streamLaw) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound
  filter_upwards [ae_lt_top (measurable_totalRounds m p) hfinite] with x hx
  by_contra h
  exact hx.ne ((never_finishes_iff m p x).mp h)

private def success (m : Mixing) (p : ℝ) : Set Inputs := {x | ∃ n, run m p n x = .inl true}

private theorem measurable_success (m : Mixing) (p : ℝ) : MeasurableSet (success m p) := by
  have he : success m p = ⋃ n, (run m p n) ⁻¹' {Sum.inl true} := by
    ext x
    simp [success]
  rw [he]
  exact MeasurableSet.iUnion fun n => (measurable_run m p n) (measurableSet_singleton _)

private theorem stream_success (m : Mixing) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (hb : 0 < mix p m.upWeight) (hab : 2 * mix p m.downWeight ≤ mix p m.upWeight) :
    streamLaw (success m p) = ENNReal.ofReal (mix p m.downWeight / mix p m.upWeight) := by
  let a := mix p m.downWeight
  let b := mix p m.upWeight
  have ha : 0 ≤ a := add_nonneg (mul_nonneg hp (m.down_nonneg true))
    (mul_nonneg (sub_nonneg.mpr hp') (m.down_nonneg false))
  let F := fun n x => value a b (run m p n x)
  have hFm (n : ℕ) : Measurable (F n) :=
    (measurable_of_countable (value a b)).comp (measurable_run m p n)
  have hFnorm (n : ℕ) (x : Inputs) : ‖F n x‖ ≤ 1 := by
    have h₀ : 0 ≤ F n x := value_nonneg ha hb (run m p n x)
    rw [Real.norm_eq_abs, abs_of_nonneg h₀]
    exact value_le_one ha hb hab (run m p n x)
  have hFin (n : ℕ) : Integrable (F n) streamLaw :=
    Integrable.of_bound (hFm n).aestronglyMeasurable 1 (Eventually.of_forall (hFnorm n))
  have hmean (n : ℕ) : (∫ x, F n x ∂streamLaw) = a/b := by
    induction n with
    | zero => simp [F, run_zero, initial, value]
    | succ n ih =>
      rw [integral_run_succ m hp hp' n _ (hFin (n+1)), ← ih]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => expectation_value hb (run_admissible m p x n)
  let f : Inputs → ℝ := (success m p).indicator (fun _ => 1)
  have hpoint : ∀ᵐ x ∂streamLaw, Tendsto (fun n => F n x) atTop (𝓝 (f x)) := by
    filter_upwards [stream_finishes_ae m hp hp' hb hab] with x hx
    rcases hx with ⟨n,d,hd⟩
    have he : ∀ k ≥ n, F k x = f x := by
      intro k hk
      rw [show F k x = value a b (run m p k x) from rfl, run_absorbed _ _ _ hd hk]
      cases d
      · have hx' : x ∉ success m p := by
          rintro ⟨j,hj⟩
          have hf₁ := run_absorbed m p x hd (le_max_left n j)
          have hf₂ := run_absorbed m p x hj (le_max_right n j)
          rw [hf₁] at hf₂
          cases hf₂
        simp [f, hx', value]
      · have hx' : x ∈ success m p := ⟨n,hd⟩
        simp [f, hx', value]
    apply Filter.Tendsto.congr' _ tendsto_const_nhds
    exact (eventually_ge_atTop n).mono (fun k hk => (he k hk).symm)
  have hl := tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    (fun n => (hFm n).aestronglyMeasurable) (integrable_const _) (fun n => Eventually.of_forall (hFnorm n))
    hpoint
  simp only [hmean] at hl
  have hm := tendsto_nhds_unique tendsto_const_nhds hl
  have hfm : (∫ x, f x ∂streamLaw) = (streamLaw (success m p)).toReal := by
    simp [f, integral_indicator (measurable_success m p), Measure.real]
  rw [hfm] at hm
  rw [hm, ENNReal.ofReal_toReal (measure_ne_top streamLaw _)]

end BilateralProfitRegular.Factory
end BundlePart010


section BundlePart011


namespace BilateralProfitRegular

open Classical MeasureTheory
open scoped ENNReal

namespace Factory

private theorem out_none_iff (m : Mixing) (p : ℝ) (ω U : Stream) :
    (procedure m).out (fun _ => p) ω U = none ↔ totalRounds m p (pairAt (ω,U)) = ⊤ := by
  rw [← never_finishes_iff]
  constructor
  · intro h hx
    rcases hx with ⟨n,d,hd⟩
    have hstop : ∃ k, (procedure m).stopped (fun _ => p) ω U k :=
      ⟨n, (stopped_iff _ _ _ _ _).mpr ⟨d,hd⟩⟩
    rw [Proc.out, dif_pos hstop] at h
    change (queryOrFinish (replay m ω ((procedure m).hist (fun _ => p) ω U (Nat.find hstop)))).getRight? = none at h
    rw [(run_eq_replay m p ω U (Nat.find hstop)).1] at h
    obtain ⟨b,hb⟩ := (stopped_iff _ _ _ _ _).mp (Nat.find_spec hstop)
    simp [hb, queryOrFinish] at h
  · intro h
    have hstop : ¬ ∃ k, (procedure m).stopped (fun _ => p) ω U k := by
      rintro ⟨k,hk⟩
      obtain ⟨d,hd⟩ := (stopped_iff _ _ _ _ _).mp hk
      exact h ⟨k,d,hd⟩
    simp [Proc.out, hstop]

private theorem out_true_iff (m : Mixing) (p : ℝ) (ω U : Stream) :
    (procedure m).out (fun _ => p) ω U = some true ↔ pairAt (ω,U) ∈ success m p := by
  by_cases hstop : ∃ k, (procedure m).stopped (fun _ => p) ω U k
  · rw [Proc.out, dif_pos hstop]
    change (queryOrFinish (replay m ω ((procedure m).hist (fun _ => p) ω U (Nat.find hstop)))).getRight? = some true ↔ _
    rw [(run_eq_replay m p ω U (Nat.find hstop)).1]
    obtain ⟨d,hd⟩ := (stopped_iff _ _ _ _ _).mp (Nat.find_spec hstop)
    rw [hd]
    simp only [queryOrFinish, Sum.getRight?, Option.some.injEq]
    constructor
    · intro h
      exact ⟨Nat.find hstop, h ▸ hd⟩
    · rintro ⟨n,hn⟩
      have hs : (procedure m).stopped (fun _ => p) ω U n :=
        (stopped_iff _ _ _ _ _).mpr ⟨true,hn⟩
      have he := run_absorbed m p _ hd (Nat.find_min' hstop hs)
      rw [he, Sum.inl.injEq] at hn
      exact hn
  · have hnot : pairAt (ω,U) ∉ success m p := by
      rintro ⟨n,hn⟩
      exact hstop ⟨n, (stopped_iff _ _ _ _ _).mpr ⟨true,hn⟩⟩
    simp [Proc.out, hstop, hnot]

/-- A common implementation of the two factories. The down and up probabilities
are the mixture of their corresponding seed weights over the unknown bias. -/
private theorem procedure_spec (m : Mixing) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (hb : 0 < mix p m.upWeight) (hab : 2 * mix p m.downWeight ≤ mix p m.upWeight) :
    Proc.law Proc.coinLaw {x | (procedure m).out (fun _ => p) x.1 x.2 = none} = 0 ∧
      Proc.law Proc.coinLaw {x | (procedure m).out (fun _ => p) x.1 x.2 = some true} =
        ENNReal.ofReal (mix p m.downWeight / mix p m.upWeight) ∧
      (procedure m).expRounds (fun _ => p) Proc.coinLaw ≤ ENNReal.ofReal (282 / mix p m.upWeight) := by
  have hnever : MeasurableSet {x | totalRounds m p x = ⊤} :=
    (measurable_totalRounds m p) (measurableSet_singleton ⊤)
  have hmap : (Proc.law Proc.coinLaw).map pairAt = streamLaw := paired_law
  refine ⟨?_, ?_, ?_⟩
  · have he : {x : Stream × Stream | (procedure m).out (fun _ => p) x.1 x.2 = none}
        = pairAt ⁻¹' {x | totalRounds m p x = ⊤} := by
      ext x
      exact out_none_iff m p x.1 x.2
    rw [he, ← Measure.map_apply measurable_pairAt hnever, hmap]
    have := stream_finishes_ae m hp hp' hb hab
    rw [ae_iff] at this
    simpa only [never_finishes_iff] using this
  · have he : {x : Stream × Stream | (procedure m).out (fun _ => p) x.1 x.2 = some true}
        = pairAt ⁻¹' success m p := by
      ext x
      exact out_true_iff m p x.1 x.2
    rw [he, ← Measure.map_apply measurable_pairAt (measurable_success m p), hmap]
    exact stream_success m hp hp' hb hab
  · unfold Proc.expRounds
    simp_rw [rounds_eq_sum]
    change (∫⁻ x, totalRounds m p (pairAt x) ∂(Proc.law Proc.coinLaw)) ≤ _
    rw [← lintegral_map (measurable_totalRounds m p) measurable_pairAt, hmap]
    exact lintegral_rounds_le m hp hp' hb hab

private noncomputable def linearMixing (c : ℝ) (hc : 0 < c) : Mixing where
  downWeight t := if t then c / (1 + c) else 0
  upWeight _ := 1 / (1 + c)
  down_nonneg t := by cases t <;> simp <;> positivity
  up_nonneg _ := by positivity
  sum_le_one t := by
    have hd : 0 < 1 + c := by positivity
    cases t
    · simpa using ((div_le_iff₀ hd).2 (by linarith) : 1 / (1 + c) ≤ 1)
    · change c / (1 + c) + 1 / (1 + c) ≤ 1
      rw [← add_div, add_comm _ (1 : ℝ), div_self hd.ne']

private theorem linear_down {c p : ℝ} (hc : 0 < c) :
    mix p (linearMixing c hc).downWeight = c * p / (1+c) := by
  simp [mix, linearMixing]
  ring

private theorem linear_up {c p : ℝ} (hc : 0 < c) :
    mix p (linearMixing c hc).upWeight = 1/(1+c) := by
  simp [mix, linearMixing]
  ring

private noncomputable def reciprocalMixing (m : ℝ) (hm : 0 < m) : Mixing where
  downWeight _ := m / (1 + m)
  upWeight t := if t then 1 / (1 + m) else 0
  down_nonneg _ := by positivity
  up_nonneg t := by cases t <;> simp <;> positivity
  sum_le_one t := by
    have hd : 0 < 1 + m := by positivity
    cases t
    · simpa using ((div_le_iff₀ hd).2 (by linarith) : m / (1 + m) ≤ 1)
    · change m / (1 + m) + 1 / (1 + m) ≤ 1
      rw [← add_div, add_comm _ (1 : ℝ), div_self hd.ne']

private theorem reciprocal_down {m p : ℝ} (hm : 0 < m) :
    mix p (reciprocalMixing m hm).downWeight = m / (1+m) := by
  simp [mix, reciprocalMixing]
  ring

private theorem reciprocal_up {m p : ℝ} (hm : 0 < m) :
    mix p (reciprocalMixing m hm).upWeight = p/(1+m) := by
  simp [mix, reciprocalMixing, div_eq_mul_inv]

end Factory

open Factory

/-- Linear Bernoulli factory, with the guarantee of Huber (2016), Theorem 1 at
slack `1/2`. The proof uses a common two-direction walk for both factories. -/
private theorem huber_factory :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 < c →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (Pω : Measure Ω) (_ : IsProbabilityMeasure Pω)
        (F : Proc Unit Bool Ω),
        ∀ p : ℝ, 0 ≤ p → p ≤ 1 → c * p ≤ 1 / 2 →
          Proc.law Pω {x | F.out (fun _ => p) x.1 x.2 = none} = 0 ∧
          Proc.law Pω {x | F.out (fun _ => p) x.1 x.2 = some true} = ENNReal.ofReal (c * p) ∧
          F.expRounds (fun _ => p) Pω ≤ ENNReal.ofReal (C * max 1 c) := by
  refine ⟨564, by norm_num, fun c hc => ⟨Stream, inferInstance, Proc.coinLaw, inferInstance,
    procedure (linearMixing c hc), ?_⟩⟩
  intro p hp hp' hcp
  have hd : 0 < 1 + c := by positivity
  have hb : 0 < mix p (linearMixing c hc).upWeight := by rw [linear_up hc]; positivity
  have hab : 2 * mix p (linearMixing c hc).downWeight ≤ mix p (linearMixing c hc).upWeight := by
    rw [linear_down hc, linear_up hc]
    calc
      2 * (c * p / (1 + c)) = (2 * (c * p)) / (1+c) := by ring
      _ ≤ _ := (div_le_div_iff_of_pos_right hd).2 (by linarith)
  obtain ⟨hn,ht,hcst⟩ := procedure_spec (linearMixing c hc) hp hp' hb hab
  rw [linear_down hc, linear_up hc] at ht
  rw [show (c * p / (1+c)) / (1/(1+c)) = c*p by field_simp] at ht
  refine ⟨hn,ht,hcst.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  rw [linear_up hc]
  have hm : 1 + c ≤ 2 * max 1 c := by
    linarith [le_max_left (1 : ℝ) c, le_max_right (1 : ℝ) c]
  calc
    282 / (1 / (1 + c)) = 282 * (1+c) := by simp
    _ ≤ _ := by linarith

/-- Scaled reciprocal Bernoulli factory, as in Lee–Doucet–Łatuszyński,
arXiv:1407.5770v1, Propositions 1, 2, and 4. -/
private theorem lee_factory :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℝ, 0 < m → m ≤ 1 / 20 →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (Pω : Measure Ω) (_ : IsProbabilityMeasure Pω)
        (F : Proc Unit Bool Ω),
        ∀ p : ℝ, 2 * m ≤ p → p ≤ 1 → p ≤ 200 * m →
          Proc.law Pω {x | F.out (fun _ => p) x.1 x.2 = none} = 0 ∧
          Proc.law Pω {x | F.out (fun _ => p) x.1 x.2 = some true} = ENNReal.ofReal (m / p) ∧
          F.expRounds (fun _ => p) Pω ≤ ENNReal.ofReal (C / p) := by
  refine ⟨300, by norm_num, fun m hm hm' => ⟨Stream, inferInstance, Proc.coinLaw, inferInstance,
    procedure (reciprocalMixing m hm), ?_⟩⟩
  intro p hmp hp' _
  have hp : 0 < p := by linarith
  have hd : 0 < 1 + m := by positivity
  have hb : 0 < mix p (reciprocalMixing m hm).upWeight := by rw [reciprocal_up hm]; positivity
  have hab : 2 * mix p (reciprocalMixing m hm).downWeight ≤
      mix p (reciprocalMixing m hm).upWeight := by
    rw [reciprocal_down hm, reciprocal_up hm]
    calc
      2 * (m / (1 + m)) = (2*m) / (1+m) := by ring
      _ ≤ _ := (div_le_div_iff_of_pos_right hd).2 hmp
  obtain ⟨hn,ht,hcst⟩ := procedure_spec (reciprocalMixing m hm) hp.le hp' hb hab
  rw [reciprocal_down hm, reciprocal_up hm] at ht
  rw [show (m / (1+m)) / (p/(1+m)) = m/p by field_simp] at ht
  refine ⟨hn,ht,hcst.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  rw [reciprocal_up hm]
  calc
    282 / (p/(1+m)) = (282 * (1+m)) / p := by field_simp
    _ ≤ _ := by
      apply (div_le_div_iff_of_pos_right hp).mpr
      linarith

end BilateralProfitRegular
end BundlePart011


section BundlePart012



namespace BilateralProfitRegular.Factory

open Classical MeasureTheory Set
open scoped ENNReal

set_option maxHeartbeats 900000

private abbrev Prices := ℝ × ℝ
private abbrev ObservationSeed := (Fin 3 → Uniform) × Stream
private abbrev ObservationHistory := List (Prices × Bool)
private abbrev ObservationState := Fin 3 → State

private noncomputable def selectorLaw : Measure (Fin 3 → Uniform) :=
  Measure.infinitePi fun _ => (volume : Measure Uniform)

private instance : IsProbabilityMeasure selectorLaw := by unfold selectorLaw; infer_instance

private noncomputable def observationSeedLaw : Measure ObservationSeed := selectorLaw.prod Proc.coinLaw

private instance : IsProbabilityMeasure observationSeedLaw := by unfold observationSeedLaw; infer_instance

private def observationSlot (n : ℕ) : Fin 3 := ⟨n % 3, Nat.mod_lt _ (by decide)⟩

private def slotTime (i : Fin 3) (n : ℕ) : ℕ := 3 * n + (i : ℕ)

private theorem slotTime_injective : Function.Injective (fun j : Fin 3 × ℕ => slotTime j.1 j.2) := by
  rintro ⟨i,k⟩ ⟨j,l⟩ h
  simp only [slotTime] at h
  have hi := i.isLt
  have hj := j.isLt
  have hjk : i = j := Fin.ext (by omega)
  have hks : k = l := by omega
  simp [hjk, hks]

private def slotCount (n : ℕ) (i : Fin 3) : ℕ := (n + 2 - (i : ℕ)) / 3

@[simp]
private theorem slotCount_zero (i : Fin 3) : slotCount 0 i = 0 := by
  unfold slotCount
  omega

@[simp]
private theorem slotCount_cycle (i : Fin 3) (k : ℕ) : slotCount (3*k) i = k := by
  have := i.isLt
  unfold slotCount
  omega

private theorem slotCount_succ (i : Fin 3) (n : ℕ) :
    slotCount (n+1) i = slotCount n i + if observationSlot n = i then 1 else 0 := by
  have hi := i.isLt
  by_cases h : observationSlot n = i
  · have hmod : n % 3 = i := congrArg Fin.val h
    simp only [slotCount, h, ↓reduceIte]
    omega
  · have hmod : n % 3 ≠ i := fun e => h (Fin.ext e)
    simp only [slotCount, h, ↓reduceIte, add_zero]
    omega

private theorem slotTime_slotCount (n : ℕ) :
    slotTime (observationSlot n) (slotCount n (observationSlot n)) = n := by
  unfold slotTime slotCount observationSlot
  dsimp
  omega

/-- A positive extension outside the parameter range of Lemma 6.5. -/
private noncomputable def positiveEstimate (est : ℝ) : ℝ := if 0 < est then est else 1

private theorem positiveEstimate_pos (est : ℝ) : 0 < positiveEstimate est := by
  unfold positiveEstimate
  split <;> simp_all

@[fun_prop]
private theorem measurable_positiveEstimate : Measurable positiveEstimate := by
  unfold positiveEstimate
  exact measurable_id.ite measurableSet_Ioi measurable_const

private noncomputable def observationMixing (est : ℝ) (i : Fin 3) : Mixing :=
  if i = 0 then linearMixing (1/(20 * positiveEstimate est))
    (one_div_pos.mpr (mul_pos (by norm_num) (positiveEstimate_pos _)))
  else reciprocalMixing (positiveEstimate est / 20)
    (div_pos (positiveEstimate_pos _) (by norm_num))

@[fun_prop]
private theorem measurable_obs_downWeight (i : Fin 3) (t : Bool) :
    Measurable (fun e => (observationMixing e i).downWeight t) := by
  by_cases hi : i = 0 <;> cases t
  all_goals simp only [observationMixing, hi, if_true, if_false, linearMixing, reciprocalMixing,
    Bool.false_eq_true] <;> try norm_num <;> fun_prop

@[fun_prop]
private theorem measurable_obs_upWeight (i : Fin 3) (t : Bool) :
    Measurable (fun e => (observationMixing e i).upWeight t) := by
  by_cases hi : i = 0 <;> cases t
  all_goals simp only [observationMixing, hi, if_true, if_false, linearMixing, reciprocalMixing,
    Bool.false_eq_true] <;> try norm_num <;> fun_prop

@[fun_prop]
private theorem measurable_obs_select (i : Fin 3) (t : Bool) :
    Measurable (fun es : (ℝ × Uniform) × State =>
      select (observationMixing es.1.1 i) es.1.2 t es.2) := by
  refine measurable_from_prod_countable_left ?_
  rintro (d | ⟨j,k⟩)
  · exact measurable_const
  · simp only [select]
    have hd : Measurable (fun es : ℝ × Uniform => (observationMixing es.1 i).downWeight t) :=
      (measurable_obs_downWeight i t).comp measurable_fst
    have hu : Measurable (fun es : ℝ × Uniform => (observationMixing es.1 i).upWeight t / scale j) :=
      ((measurable_obs_upWeight i t).comp measurable_fst).div_const _
    apply Measurable.ite _ measurable_const (Measurable.ite _ measurable_const
      (Measurable.ite _ measurable_const measurable_const))
    · exact measurableSet_lt (measurable_subtype_coe.comp measurable_snd) hd
    · exact measurableSet_lt (measurable_subtype_coe.comp measurable_snd) (hd.add (hu.mul_const _))
    · exact measurableSet_lt (measurable_subtype_coe.comp measurable_snd) (hd.add hu)

private noncomputable def referenceWeight (ρ : ℝ) : ℝ := ρ / (ρ + ρ⁻¹)

private theorem referenceWeight_bounds {ρ : ℝ} (hρ : 0 < ρ) :
    0 ≤ referenceWeight ρ ∧ referenceWeight ρ ≤ 1 := by
  unfold referenceWeight
  have h : 0 < ρ + ρ⁻¹ := by positivity
  exact ⟨div_nonneg hρ.le h.le, (div_le_one h).2 (le_add_of_nonneg_right (inv_pos.mpr hρ).le)⟩

private noncomputable def observationPrice (ρ : ℝ) (x z : Prices) (θ : Fin 3 → Uniform) (i : Fin 3) :
    Prices :=
  if i = 0 then z
  else if (θ i : ℝ) < referenceWeight ρ then (x.1,z.2) else (z.1,x.2)

private theorem observationPrice_mem (ρ : ℝ) (x z : Prices) (θ : Fin 3 → Uniform) (i : Fin 3) :
    observationPrice ρ x z θ i ∈ ({z,(x.1,z.2),(z.1,x.2)} : Set Prices) := by
  unfold observationPrice
  split
  · exact mem_insert _ _
  · split
    · exact mem_insert_of_mem _ (mem_insert _ _)
    · exact mem_insert_of_mem _ (mem_insert_of_mem _ (mem_singleton _))

private noncomputable def observationCoefficient (est ρ : ℝ) (x : Prices) : ℝ :=
  2000 * (ρ + ρ⁻¹)^2 / ((x.2 - x.1) * est)

private def startObservation : ObservationState := fun _ => initial

private noncomputable def observationHistoryStep (est : ℝ) (ω : ObservationSeed)
    (s : ObservationState × ℕ) (q : Prices × Bool) : ObservationState × ℕ :=
  let i := observationSlot s.2
  (Function.update s.1 i (select (observationMixing est i) (ω.2 s.2) q.2 (s.1 i)), s.2 + 1)

private noncomputable def replayObservation (est : ℝ) (ω : ObservationSeed) (h : ObservationHistory) :
    ObservationState :=
  (h.foldl (observationHistoryStep est ω) (startObservation,0)).1

private theorem observation_fold_length (est : ℝ) (ω : ObservationSeed)
    (s : ObservationState × ℕ) (h : ObservationHistory) :
    (h.foldl (observationHistoryStep est ω) s).2 = s.2 + h.length := by
  induction h generalizing s with
  | nil => simp
  | cons q h ih => rw [List.foldl_cons, ih]; simp [observationHistoryStep]; omega

private theorem replayObservation_append (est : ℝ) (ω : ObservationSeed) (h : ObservationHistory)
    (q : Prices × Bool) :
    let i := observationSlot h.length
    replayObservation est ω (h ++ [q]) = Function.update (replayObservation est ω h) i
      (select (observationMixing est i) (ω.2 h.length) q.2 (replayObservation est ω h i)) := by
  simp [replayObservation, List.foldl_append, observationHistoryStep, observation_fold_length]

@[fun_prop]
private theorem measurable_replayObservation (h : ObservationHistory) :
    Measurable (fun ew : ℝ × ObservationSeed => replayObservation ew.1 ew.2 h) := by
  induction h using List.reverseRecOn with
  | nil => exact measurable_const
  | append_singleton h q ih =>
    have heq : (fun ew : ℝ × ObservationSeed => replayObservation ew.1 ew.2 (h ++ [q])) =
      fun ew => Function.update (replayObservation ew.1 ew.2 h) (observationSlot h.length)
        (select (observationMixing ew.1 (observationSlot h.length)) (ew.2.2 h.length) q.2
          (replayObservation ew.1 ew.2 h (observationSlot h.length))) := by
      funext ew
      exact replayObservation_append ew.1 ew.2 h q
    rw [heq]
    apply measurable_pi_lambda
    intro i
    by_cases hslot : i = observationSlot h.length
    · subst i
      simp only [Function.update_self]
      have h₁ : Measurable (fun ew : ℝ × ObservationSeed => ew.2.2 h.length) :=
        (measurable_pi_apply h.length).comp (measurable_snd.comp measurable_snd)
      have h₂ : Measurable (fun ew : ℝ × ObservationSeed =>
          replayObservation ew.1 ew.2 h (observationSlot h.length)) :=
        (measurable_pi_apply (observationSlot h.length)).comp ih
      exact (measurable_obs_select (observationSlot h.length) q.2).comp
        ((measurable_fst.prodMk h₁).prodMk h₂)
    · simp only [Function.update_of_ne hslot]
      exact (measurable_pi_apply i).comp ih

private def observationStep (s : ObservationState) (y : Prices) (coef : ℝ) : Prices ⊕ ℝ :=
  if ∀ i, (s i).isLeft = true then
    .inr (if ∀ i, s i = .inl true then coef else 0)
  else .inl y

private instance : MeasurableSingletonClass ObservationState := inferInstance

@[fun_prop]
private theorem measurable_observationStep :
    Measurable (fun a : ObservationState × (Prices × ℝ) =>
      observationStep a.1 a.2.1 a.2.2) := by
  refine measurable_from_prod_countable_right ?_
  intro s
  unfold observationStep
  dsimp only
  by_cases hs : ∀ i, (s i).isLeft = true
  · by_cases ht : ∀ i, s i = .inl true
    · simp only [if_pos hs, if_pos ht]
      exact measurable_inr.comp (measurable_snd : Measurable (Prod.snd : Prices × ℝ → ℝ))
    · simp only [if_pos hs, if_neg ht]
      exact measurable_const
  · simp only [if_neg hs]
    exact measurable_inl.comp (measurable_fst : Measurable (Prod.fst : Prices × ℝ → Prices))

/-- The four numeric inputs suffice to implement the observation uniformly in the unknown law. -/
private noncomputable def observationAction (est ρ : ℝ) (x z : Prices) (ω : ObservationSeed)
    (h : ObservationHistory) : Prices ⊕ ℝ :=
  observationStep (replayObservation est ω h) (observationPrice ρ x z ω.1 (observationSlot h.length))
    (observationCoefficient est ρ x)

private abbrev ObservationArgs := (ℝ × ℝ) × (Prices × Prices) × ObservationSeed

private theorem measurable_observationAction (h : ObservationHistory) :
    Measurable (fun args : ObservationArgs =>
      observationAction args.1.1 args.1.2 args.2.1.1 args.2.1.2 args.2.2 h) := by
  let i := observationSlot h.length
  have hest : Measurable (fun args : ObservationArgs => args.1.1) :=
    measurable_fst.comp measurable_fst
  have hρ : Measurable (fun args : ObservationArgs => args.1.2) :=
    measurable_snd.comp measurable_fst
  have hx : Measurable (fun args : ObservationArgs => args.2.1.1) :=
    measurable_fst.comp (measurable_fst.comp measurable_snd)
  have hz : Measurable (fun args : ObservationArgs => args.2.1.2) :=
    measurable_snd.comp (measurable_fst.comp measurable_snd)
  have hω : Measurable (fun args : ObservationArgs => args.2.2) :=
    measurable_snd.comp measurable_snd
  have hS : Measurable (fun args : ObservationArgs => replayObservation args.1.1 args.2.2 h) := by
    simpa only [Function.comp_def] using ((measurable_replayObservation h).comp (hest.prodMk hω))
  have hP : Measurable (fun args : ObservationArgs =>
      observationPrice args.1.2 args.2.1.1 args.2.1.2 args.2.2.1 i) := by
    by_cases hi : i = 0
    · simp only [observationPrice, if_pos hi]
      exact hz
    · simp only [observationPrice, if_neg hi]
      have hθ : Measurable (fun args : ObservationArgs => (args.2.2.1 i : ℝ)) :=
        measurable_subtype_coe.comp ((measurable_pi_apply i).comp (measurable_fst.comp hω))
      apply Measurable.ite
        (measurableSet_lt hθ (hρ.div (hρ.add hρ.inv)))
      · exact (measurable_fst.comp hx).prodMk (measurable_snd.comp hz)
      · exact (measurable_fst.comp hz).prodMk (measurable_snd.comp hx)
  have hC : Measurable (fun args : ObservationArgs =>
      observationCoefficient args.1.1 args.1.2 args.2.1.1) :=
    (((hρ.add hρ.inv).pow_const 2).const_mul 2000).div
      (((measurable_snd.comp hx).sub (measurable_fst.comp hx)).mul hest)
  unfold observationAction
  simpa only [Function.comp_def] using
    (measurable_observationStep.comp (hS.prodMk (hP.prodMk hC)))

private noncomputable def observationProc (est ρ : ℝ) (x z : Prices) : Proc Prices ℝ ObservationSeed where
  step ω h := observationAction est ρ x z ω h
  measurable_step h := by
    have hh : Measurable (fun ω : ObservationSeed => (est,ω)) :=
      measurable_const.prodMk measurable_id
    have hS : Measurable (fun ω : ObservationSeed => replayObservation est ω h) :=
      (measurable_replayObservation h).comp hh
    let i := observationSlot h.length
    have hP : Measurable (fun ω : ObservationSeed => observationPrice ρ x z ω.1 i) := by
      by_cases hi : i = 0
      · simp only [observationPrice, if_pos hi]
        exact measurable_const
      · simp only [observationPrice, if_neg hi]
        have hθ : Measurable (fun ω : ObservationSeed => (ω.1 i : ℝ)) :=
          measurable_subtype_coe.comp ((measurable_pi_apply i).comp measurable_fst)
        exact Measurable.ite (measurableSet_lt hθ measurable_const) measurable_const measurable_const
    exact measurable_observationStep.comp (hS.prodMk (hP.prodMk measurable_const))

private theorem observation_queries_first (est ρ : ℝ) (x z : Prices) :
    (observationProc est ρ x z).QueriesFirst := by
  intro ω
  simp [observationProc, observationAction, replayObservation, startObservation, initial, observationStep]

private theorem observation_queries (est ρ : ℝ) (x z : Prices) :
    (observationProc est ρ x z).QueriesIn {z,(x.1,z.2),(z.1,x.2)} := by
  intro ω h y hy
  change observationAction est ρ x z ω h = .inl y at hy
  unfold observationAction observationStep at hy
  split at hy
  · split at hy <;> contradiction
  · cases hy
    exact observationPrice_mem _ _ _ _ _

private theorem observation_outputs (est ρ L : ℝ) (x z : Prices)
    (h₀ : 0 ≤ observationCoefficient est ρ x) (hL : observationCoefficient est ρ x ≤ L) :
    (observationProc est ρ x z).OutputsIn (Set.Icc 0 L) := by
  intro ω h a ha
  change observationAction est ρ x z ω h = .inr a at ha
  unfold observationAction observationStep at ha
  split at ha
  · split at ha
    · cases ha
      exact ⟨h₀,hL⟩
    · cases ha
      exact ⟨le_rfl,h₀.trans hL⟩
  · contradiction

end BilateralProfitRegular.Factory
end BundlePart012


section BundlePart013


namespace BilateralProfitRegular.Factory

open Classical MeasureTheory ProbabilityTheory Set
open scoped ENNReal

set_option maxHeartbeats 900000

private abbrev ObservationSample := (Fin 3 → Uniform) × (Fin 3 → Inputs)
private abbrev ObservationPath := ObservationSeed × Stream

private def splitSlots (x : Inputs) (i : Fin 3) (n : ℕ) : Input := x (slotTime i n)

@[fun_prop]
private theorem measurable_splitSlots : Measurable splitSlots := by
  unfold splitSlots
  fun_prop

private noncomputable def observationLaw : Measure ObservationSample :=
  selectorLaw.prod (Measure.infinitePi fun _ => streamLaw)

private instance : IsProbabilityMeasure observationLaw := by unfold observationLaw; infer_instance

private def observationSample (x : ObservationPath) : ObservationSample :=
  (x.1.1, splitSlots (pairAt (x.1.2, x.2)))

@[fun_prop]
private theorem measurable_observationSample : Measurable observationSample := by
  unfold observationSample
  fun_prop

private theorem splitSlots_law :
    streamLaw.map splitSlots = Measure.infinitePi (fun _ : Fin 3 => streamLaw) := by
  let e := fun j : Fin 3 × ℕ => slotTime j.1 j.2
  have he : Measurable (fun x : Inputs => fun j => x (e j)) := by fun_prop
  have hsplit : splitSlots = (MeasurableEquiv.curry (Fin 3) ℕ Input) ∘
      (fun x : Inputs => fun j => x (e j)) := by rfl
  unfold streamLaw
  rw [hsplit, ← Measure.map_map (by fun_prop) he,
    Measure.map_infinitePi_infinitePi_of_inj slotTime_injective]
  exact Measure.infinitePi_map_curry (fun (_ : Fin 3) (_ : ℕ) => inputLaw)

private theorem observationSample_law :
    (Proc.law observationSeedLaw).map observationSample = observationLaw := by
  let e : ObservationPath ≃ᵐ ((Fin 3 → Uniform) × (Stream × Stream)) := MeasurableEquiv.prodAssoc
  have he := (measurePreserving_prodAssoc selectorLaw Proc.coinLaw Proc.coinLaw).map_eq
  have hcomp : observationSample =
      (Prod.map id (splitSlots ∘ pairAt)) ∘ e := rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) e.measurable, Proc.law,
    observationSeedLaw, show ⇑e = _ from rfl, he, ← Measure.map_prod_map,
    Measure.map_id, ← Measure.map_map measurable_splitSlots measurable_pairAt]
  change (selectorLaw.prod (((Proc.law Proc.coinLaw).map pairAt).map splitSlots)) = _
  rw [paired_law]
  change selectorLaw.prod (streamLaw.map splitSlots) = _
  rw [splitSlots_law, observationLaw]
  all_goals fun_prop

private noncomputable def observationBias (prob : Prices → ℝ) (ρ : ℝ) (x z : Prices)
    (θ : Fin 3 → Uniform) (i : Fin 3) : ℝ := prob (observationPrice ρ x z θ i)

private noncomputable def observationTrace (est ρ : ℝ) (x z : Prices) (prob : Prices → ℝ)
    (n : ℕ) (a : ObservationSample) : ObservationState :=
  fun i => run (observationMixing est i) (observationBias prob ρ x z a.1 i)
    (slotCount n i) (a.2 i)

private theorem observationTrace_step (est ρ : ℝ) (x z : Prices) (prob : Prices → ℝ)
    (n : ℕ) (ω : ObservationSeed) (U : Stream) :
    let a := observationSample (ω,U)
    let S := observationTrace est ρ x z prob n a
    let i := observationSlot n
    let y := observationPrice ρ x z ω.1 i
    observationTrace est ρ x z prob (n+1) a =
      Function.update S i (select (observationMixing est i) (ω.2 n)
        (decide ((U n : ℝ) < prob y)) (S i)) := by
  dsimp only
  funext j
  rw [observationTrace, slotCount_succ]
  by_cases hj : j = observationSlot n
  · subst j
    simp only [if_true, Function.update_self, run_succ, update]
    simp only [observationSample, splitSlots, pairAt, slotTime_slotCount,
      observationBias, observationTrace]
  · simp only [Ne.symm hj, if_false, add_zero, Function.update_of_ne hj, observationTrace]

private theorem observationTrace_absorbed (est ρ : ℝ) (x z : Prices) (prob : Prices → ℝ)
    (n : ℕ) (ω : ObservationSeed) (U : Stream)
    (hf : ∀ i, (observationTrace est ρ x z prob n (observationSample (ω,U)) i).isLeft = true) :
    observationTrace est ρ x z prob (n+1) (observationSample (ω,U)) =
      observationTrace est ρ x z prob n (observationSample (ω,U)) := by
  rw [observationTrace_step]
  funext i
  by_cases hi : i = observationSlot n
  · subst i
    have h := hf (observationSlot n)
    cases hs : observationTrace est ρ x z prob n (observationSample (ω,U)) (observationSlot n) with
    | inl d => simp [select]
    | inr jk => simp [hs] at h
  · exact Function.update_of_ne hi _ _

private theorem observation_trace_eq_replay (est ρ : ℝ) (x z : Prices) (prob : Prices → ℝ)
    (n : ℕ) (ω : ObservationSeed) (U : Stream) :
    let h := (observationProc est ρ x z).hist prob ω U n
    let S := observationTrace est ρ x z prob n (observationSample (ω,U))
    replayObservation est ω h = S ∧ ((¬ ∀ i, (S i).isLeft = true) → h.length = n) := by
  induction n with
  | zero =>
    constructor
    · funext i
      simp [observationTrace, run_zero, Proc.hist, replayObservation, startObservation]
    · simp [Proc.hist]
  | succ n ih =>
    dsimp only at ih ⊢
    rcases ih with ⟨ih,hlen⟩
    let h := (observationProc est ρ x z).hist prob ω U n
    let S := observationTrace est ρ x z prob n (observationSample (ω,U))
    let i := observationSlot n
    let y := observationPrice ρ x z ω.1 i
    by_cases hdone : ∀ j, (S j).isLeft = true
    · have hs : (observationProc est ρ x z).step ω h =
          .inr (if ∀ j, S j = .inl true then observationCoefficient est ρ x else 0) := by
        change observationStep (replayObservation est ω h) _ _ = _
        rw [ih, observationStep, if_pos hdone]
      rw [Proc.hist, show (observationProc est ρ x z).step ω h = _ from hs]
      rw [observationTrace_absorbed est ρ x z prob n ω U hdone]
      exact ⟨ih, fun hh => (hh hdone).elim⟩
    · have hn : h.length = n := hlen hdone
      have hs : (observationProc est ρ x z).step ω h = .inl y := by
        change observationStep (replayObservation est ω h)
          (observationPrice ρ x z ω.1 (observationSlot h.length)) _ = _
        rw [ih, hn, observationStep, if_neg hdone]
      rw [Proc.hist, show (observationProc est ρ x z).step ω h = _ from hs]
      refine ⟨?_, fun _ => ?_⟩
      · rw [replayObservation_append, hn, ih, observationTrace_step]
      · simp [List.length_append, show ((observationProc est ρ x z).hist prob ω U n).length = n from hn]

private theorem observation_stopped_iff (est ρ : ℝ) (x z : Prices) (prob : Prices → ℝ)
    (n : ℕ) (ω : ObservationSeed) (U : Stream) :
    (observationProc est ρ x z).stopped prob ω U n ↔
      ∀ i, (observationTrace est ρ x z prob n (observationSample (ω,U)) i).isLeft = true := by
  unfold Proc.stopped
  change (observationStep (replayObservation est ω ((observationProc est ρ x z).hist prob ω U n))
    _ _).isRight = true ↔ _
  rw [(observation_trace_eq_replay est ρ x z prob n ω U).1]
  unfold observationStep
  split <;> simp_all

private theorem slot_stop_exists (m : Mixing) (p : ℝ) (x : Inputs)
    (hx : totalRounds m p x ≠ ⊤) :
    ∃ (n : ℕ) (d : Bool), run m p n x = .inl d ∧ totalRounds m p x = n := by
  have hstop : ∃ n d, run m p n x = .inl d := by
    by_contra h
    exact hx ((never_finishes_iff m p x).mp h)
  let ω : Stream := fun n => (x n).1
  let U : Stream := fun n => (x n).2
  have he : pairAt (ω,U) = x := by funext n; exact Prod.eta _
  have hs : ∃ n, (procedure m).stopped (fun _ => p) ω U n := by
    rcases hstop with ⟨n,d,hd⟩
    exact ⟨n, (stopped_iff _ _ _ _ _).mpr ⟨d,he ▸ hd⟩⟩
  have hrun := (stopped_iff _ _ _ _ _).mp (Nat.find_spec hs)
  rw [he] at hrun
  rcases hrun with ⟨d,hd⟩
  refine ⟨_,d,hd,?_⟩
  have hRounds := rounds_eq_sum m p ω U
  rw [rounds_eq_find m p ω U hs, he] at hRounds
  simpa [totalRounds] using hRounds.symm

private theorem observation_rounds_le (est ρ : ℝ) (x z : Prices) (prob : Prices → ℝ)
    (ω : ObservationSeed) (U : Stream) :
    let a := observationSample (ω,U)
    ((observationProc est ρ x z).rounds prob ω U : ENNReal) ≤
      3 * ∑ i, totalRounds (observationMixing est i) (observationBias prob ρ x z a.1 i) (a.2 i) := by
  dsimp only
  let a := observationSample (ω,U)
  let total := fun i : Fin 3 => totalRounds (observationMixing est i)
    (observationBias prob ρ x z a.1 i) (a.2 i)
  by_cases h : ∃ i, total i = ⊤
  · rcases h with ⟨i,hi⟩
    have hsum : ∑ j, total j = ⊤ :=
      top_unique (hi ▸ Finset.single_le_sum (fun j _ => bot_le) (Finset.mem_univ i))
    change _ ≤ 3 * ∑ j, total j
    simp [hsum]
  · have h' (i : Fin 3) : total i ≠ ⊤ := fun hi => h ⟨i,hi⟩
    choose n d hd htotal using fun i : Fin 3 => slot_stop_exists (observationMixing est i)
      (observationBias prob ρ x z a.1 i) (a.2 i) (h' i)
    let N := ∑ i, n i
    have hni (i : Fin 3) : n i ≤ N := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    have hstop : (observationProc est ρ x z).stopped prob ω U (3*N) := by
      rw [observation_stopped_iff]
      intro i
      rw [observationTrace, slotCount_cycle, run_absorbed _ _ _ (hd i) (hni i)]
      rfl
    have hle : (observationProc est ρ x z).rounds prob ω U ≤ (3*N : ℕ) :=
      iInf_le_of_le (3*N) (iInf_le _ hstop)
    have hh := ENat.toENNReal_mono hle
    change _ ≤ 3 * ∑ j, total j
    simp only [show ∀ i, total i = n i from htotal]
    push_cast at hh ⊢
    simpa [N] using hh

end BilateralProfitRegular.Factory
end BundlePart013


section BundlePart014


namespace BilateralProfitRegular.Factory

open Classical MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

set_option maxHeartbeats 800000

private theorem measurable_observationSlotFunction {α : Type} [MeasurableSpace α]
    (prob : Prices → ℝ) (ρ : ℝ) (x z : Prices) (i : Fin 3)
    (f : ℝ → Inputs → α) (hf : ∀ p, Measurable (f p)) :
    Measurable (fun s : ObservationSample => f (observationBias prob ρ x z s.1 i) (s.2 i)) := by
  have hx : Measurable (fun s : ObservationSample => s.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  by_cases hi : i = 0
  · simpa only [observationBias, observationPrice, if_pos hi, Function.comp_def] using
      ((hf (prob z)).comp hx)
  · have heq : (fun s : ObservationSample =>
        f (observationBias prob ρ x z s.1 i) (s.2 i)) =
      fun s : ObservationSample =>
        if (s.1 i : ℝ) < referenceWeight ρ then f (prob (x.1,z.2)) (s.2 i)
        else f (prob (z.1,x.2)) (s.2 i) := by
      funext s
      unfold observationBias observationPrice
      rw [if_neg hi]
      split <;> rfl
    rw [heq]
    have hθ : Measurable (fun s : ObservationSample => (s.1 i : ℝ)) :=
      measurable_subtype_coe.comp ((measurable_pi_apply i).comp measurable_fst)
    exact Measurable.ite (measurableSet_lt hθ measurable_const)
      ((hf _).comp hx) ((hf _).comp hx)

private noncomputable def observationSlotRounds (est ρ : ℝ) (x z : Prices) (prob : Prices → ℝ)
    (i : Fin 3) (s : ObservationSample) : ENNReal :=
  totalRounds (observationMixing est i) (observationBias prob ρ x z s.1 i) (s.2 i)

private theorem measurable_observationSlotRounds (est ρ : ℝ) (x z : Prices) (prob : Prices → ℝ)
    (i : Fin 3) : Measurable (observationSlotRounds est ρ x z prob i) :=
  measurable_observationSlotFunction prob ρ x z i _ (measurable_totalRounds _)

private theorem observation_slot_lintegral_le (est ρ : ℝ) (x z : Prices) (prob : Prices → ℝ)
    (i : Fin 3) (N : ENNReal)
    (hN : ∀ θ, (∫⁻ s, totalRounds (observationMixing est i)
      (observationBias prob ρ x z θ i) s ∂streamLaw) ≤ N) :
    (∫⁻ s, observationSlotRounds est ρ x z prob i s ∂observationLaw) ≤ N := by
  unfold observationLaw
  rw [lintegral_prod _ (measurable_observationSlotRounds est ρ x z prob i).aemeasurable]
  have he (θ : Fin 3 → Uniform) :
      (∫⁻ v, observationSlotRounds est ρ x z prob i (θ,v)
        ∂(Measure.infinitePi fun _ : Fin 3 => streamLaw)) =
      ∫⁻ s, totalRounds (observationMixing est i) (observationBias prob ρ x z θ i) s ∂streamLaw := by
    change (∫⁻ v : Fin 3 → Inputs, totalRounds (observationMixing est i)
      (observationBias prob ρ x z θ i) (v i) ∂(Measure.infinitePi fun _ : Fin 3 => streamLaw)) = _
    rw [← lintegral_map (measurable_totalRounds _ _) (measurable_pi_apply _),
      Measure.infinitePi_map_eval]
  simp_rw [he]
  exact (lintegral_mono hN).trans_eq (by simp)

private theorem observation_expRounds_le (est ρ : ℝ) (x z : Prices) (prob : Prices → ℝ)
    (N : Fin 3 → ENNReal)
    (hN : ∀ i θ, (∫⁻ s, totalRounds (observationMixing est i)
      (observationBias prob ρ x z θ i) s ∂streamLaw) ≤ N i) :
    (observationProc est ρ x z).expRounds prob observationSeedLaw ≤ 3 * ∑ i, N i := by
  unfold Proc.expRounds
  calc
    _ ≤ ∫⁻ s, (3 : ENNReal) * ∑ i, observationSlotRounds est ρ x z prob i
        (observationSample s) ∂(Proc.law observationSeedLaw) :=
      lintegral_mono fun s => observation_rounds_le est ρ x z prob s.1 s.2
    _ = ∫⁻ s, (3 : ENNReal) * ∑ i, observationSlotRounds est ρ x z prob i s ∂observationLaw := by
      have hm : Measurable (fun s => (3 : ENNReal) *
          ∑ i, observationSlotRounds est ρ x z prob i s) :=
        measurable_const.mul (Finset.measurable_fun_sum _ fun i _ =>
          measurable_observationSlotRounds est ρ x z prob i)
      rw [← lintegral_map hm measurable_observationSample, observationSample_law]
    _ = 3 * ∑ i, ∫⁻ s, observationSlotRounds est ρ x z prob i s ∂observationLaw := by
      rw [lintegral_const_mul _ (Finset.measurable_fun_sum _ fun i _ =>
        measurable_observationSlotRounds est ρ x z prob i)]
      rw [lintegral_finsetSum _ (fun i _ => measurable_observationSlotRounds est ρ x z prob i)]
    _ ≤ _ := by
      gcongr with i _
      exact observation_slot_lintegral_le est ρ x z prob i (N i) (hN i)

private theorem observation_out_measured_none (est ρ : ℝ) (x z : Prices) (prob : Prices → ℝ)
    (N : Fin 3 → ENNReal) (hfin : ∀ i, N i ≠ ⊤)
    (hN : ∀ i θ, (∫⁻ s, totalRounds (observationMixing est i)
      (observationBias prob ρ x z θ i) s ∂streamLaw) ≤ N i) :
    Proc.law observationSeedLaw {s | (observationProc est ρ x z).out prob s.1 s.2 = none} = 0 := by
  have hfact (i : Fin 3) : ∀ᵐ s ∂observationLaw, observationSlotRounds est ρ x z prob i s < ⊤ := by
    exact ae_lt_top (measurable_observationSlotRounds est ρ x z prob i)
      (ne_top_of_le_ne_top (hfin i) (observation_slot_lintegral_le est ρ x z prob i _ (hN i)))
  have htop : ∀ᵐ s ∂(Proc.law observationSeedLaw), ∀ i,
      observationSlotRounds est ρ x z prob i (observationSample s) < ⊤ := by
    apply ae_all_iff.2
    intro i
    have hm := measurable_observationSlotRounds est ρ x z prob i
    have hfi := hfact i
    simpa only [observationSample_law] using
      (ae_map_iff measurable_observationSample.aemeasurable
        (measurableSet_lt hm measurable_const)).mp (by rw [observationSample_law]; exact hfi)
  have hn : ∀ᵐ s ∂(Proc.law observationSeedLaw),
      (observationProc est ρ x z).out prob s.1 s.2 ≠ none := by
    filter_upwards [htop] with s hs
    have hbound := observation_rounds_le est ρ x z prob s.1 s.2
    have hfin' : (3 : ENNReal) * ∑ i, observationSlotRounds est ρ x z prob i (observationSample s) ≠ ⊤ :=
      ENNReal.mul_ne_top (by norm_num) (ENNReal.sum_ne_top.mpr (fun i _ => (hs i).ne))
    have hrs : ((observationProc est ρ x z).rounds prob s.1 s.2 : ENNReal) ≠ ⊤ :=
      ne_top_of_le_ne_top hfin' hbound
    have hstop : ∃ n, (observationProc est ρ x z).stopped prob s.1 s.2 n := by
      by_contra h
      apply hrs
      have hr : (observationProc est ρ x z).rounds prob s.1 s.2 = ⊤ := by
        unfold Proc.rounds
        simp [not_exists.mp h]
      simp [hr]
    rw [Proc.out, dif_pos hstop]
    have he := Nat.find_spec hstop
    unfold Proc.stopped at he
    cases hh : (observationProc est ρ x z).step s.1
        ((observationProc est ρ x z).hist prob s.1 s.2 (Nat.find hstop)) with
    | inl y =>
      exact (Bool.noConfusion (he.symm.trans (congrArg Sum.isRight hh)))
    | inr b => simp
  simpa only [ae_iff, not_not] using hn

private def observationSuccess (est ρ : ℝ) (x z : Prices) (prob : Prices → ℝ) :
    Set ObservationSample :=
  {s | ∀ i, s.2 i ∈ success (observationMixing est i) (observationBias prob ρ x z s.1 i)}

private noncomputable def slotSuccessIndicator (m : Mixing) (p : ℝ) (s : Inputs) : ℝ :=
  (success m p).indicator (fun _ => 1) s

private theorem measurable_slotSuccessIndicator (m : Mixing) (p : ℝ) :
    Measurable (slotSuccessIndicator m p) := measurable_const.indicator (measurable_success m p)

private theorem slotSuccessIndicator_integral (m : Mixing) (p : ℝ) :
    (∫ s, slotSuccessIndicator m p s ∂streamLaw) = (streamLaw (success m p)).toReal := by
  simp [slotSuccessIndicator, integral_indicator (measurable_success m p), Measure.real]

private theorem observationSuccessIndicator_eq (est ρ : ℝ) (x z : Prices) (prob : Prices → ℝ)
    (s : ObservationSample) :
    (observationSuccess est ρ x z prob).indicator (fun _ => (1 : ℝ)) s =
      ∏ i, slotSuccessIndicator (observationMixing est i) (observationBias prob ρ x z s.1 i) (s.2 i) := by
  by_cases h : s ∈ observationSuccess est ρ x z prob
  · rw [Set.indicator_of_mem h]
    symm
    exact Finset.prod_eq_one (fun i _ => Set.indicator_of_mem (h i) _)
  · have hn : ∃ i, s.2 i ∉ success (observationMixing est i)
        (observationBias prob ρ x z s.1 i) := by
      by_contra! h'
      exact h h'
    rcases hn with ⟨i,hi⟩
    rw [Set.indicator_of_notMem h, Finset.prod_eq_zero (Finset.mem_univ i)
      (show slotSuccessIndicator _ _ _ = 0 from Set.indicator_of_notMem hi _)]

private theorem measurable_observationSuccess (est ρ : ℝ) (x z : Prices) (prob : Prices → ℝ) :
    MeasurableSet (observationSuccess est ρ x z prob) := by
  have hm (i : Fin 3) : Measurable (fun s : ObservationSample =>
      slotSuccessIndicator (observationMixing est i)
        (observationBias prob ρ x z s.1 i) (s.2 i)) :=
    measurable_observationSlotFunction prob ρ x z i _ (measurable_slotSuccessIndicator _)
  have he : observationSuccess est ρ x z prob =
      {s | (∏ i, slotSuccessIndicator (observationMixing est i)
        (observationBias prob ρ x z s.1 i) (s.2 i)) = 1} := by
    ext s
    rw [mem_setOf_eq, ← observationSuccessIndicator_eq]
    by_cases h : s ∈ observationSuccess est ρ x z prob <;> simp [h]
  rw [he]
  exact (Finset.measurable_fun_prod _ (fun i _ => hm i)) (measurableSet_singleton _)

private theorem observation_out_getD (est ρ : ℝ) (x z : Prices) (prob : Prices → ℝ)
    (s : ObservationPath) :
    ((observationProc est ρ x z).out prob s.1 s.2).getD 0 =
      (observationSuccess est ρ x z prob).indicator
        (fun _ => observationCoefficient est ρ x) (observationSample s) := by
  let a := observationSample s
  let m := fun i => observationMixing est i
  let p := fun i => observationBias prob ρ x z a.1 i
  let A := observationSuccess est ρ x z prob
  by_cases hs : a ∈ A
  · have hex (i : Fin 3) : ∃ n, run (m i) (p i) n (a.2 i) = .inl true := hs i
    choose n hn using hex
    let N := ∑ i, n i
    have hni (i : Fin 3) : n i ≤ N :=
      Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    have hstop : ∃ k, (observationProc est ρ x z).stopped prob s.1 s.2 k := by
      refine ⟨3*N, (observation_stopped_iff est ρ x z prob _ _ _).mpr ?_⟩
      intro i
      rw [observationTrace, slotCount_cycle, run_absorbed _ _ _ (hn i) (hni i)]
      rfl
    rw [Proc.out, dif_pos hstop, Set.indicator_of_mem hs]
    change ((observationStep (replayObservation est s.1
        ((observationProc est ρ x z).hist prob s.1 s.2 (Nat.find hstop))) _ _).getRight?).getD 0 = _
    rw [(observation_trace_eq_replay est ρ x z prob _ _ _).1, observationStep,
      if_pos ((observation_stopped_iff est ρ x z prob _ _ _).mp (Nat.find_spec hstop))]
    have htrue (i : Fin 3) :
        observationTrace est ρ x z prob (Nat.find hstop) a i = .inl true := by
      let k := slotCount (Nat.find hstop) i
      have hdone := (observation_stopped_iff est ρ x z prob _ _ _).mp (Nat.find_spec hstop) i
      change (run (m i) (p i) k (a.2 i)).isLeft = true at hdone
      change run (m i) (p i) k (a.2 i) = _
      cases heq : run (m i) (p i) k (a.2 i) with
      | inl d =>
        have he₁ := run_absorbed _ _ _ heq (le_max_left k (n i))
        have he₂ := run_absorbed _ _ _ (hn i) (le_max_right k (n i))
        rw [he₁] at he₂
        exact he₂
      | inr jk => simp [heq] at hdone
    rw [if_pos (show _ from htrue)]
    rfl
  · rw [Set.indicator_of_notMem hs, Proc.out]
    split
    · rename_i hstop
      change ((observationStep (replayObservation est s.1
        ((observationProc est ρ x z).hist prob s.1 s.2 (Nat.find hstop))) _ _).getRight?).getD 0 = _
      rw [(observation_trace_eq_replay est ρ x z prob _ _ _).1, observationStep,
        if_pos ((observation_stopped_iff est ρ x z prob _ _ _).mp (Nat.find_spec hstop))]
      have hfalse : ¬ ∀ i, observationTrace est ρ x z prob (Nat.find hstop) a i = .inl true := by
        intro ht
        apply hs
        intro i
        exact ⟨slotCount (Nat.find hstop) i, ht i⟩
      rw [if_neg (show _ from hfalse)]
      rfl
    · rfl

end BilateralProfitRegular.Factory
end BundlePart014


section BundlePart015


namespace BilateralProfitRegular.Factory

open Classical MeasureTheory ProbabilityTheory Set MechanismDesign.BilateralTrade
open scoped BigOperators ENNReal

set_option maxHeartbeats 800000

private theorem integral_uniform_choice {r : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 1) (v w : ℝ) :
    (∫ θ : Uniform, if (θ : ℝ) < r then v else w) = r * v + (1-r) * w := by
  have heq : (fun θ : Uniform => if (θ : ℝ) < r then v else w) =
      fun θ : Uniform => (if (θ : ℝ) < r then v-w else 0) + w := by
    funext θ
    split <;> simp_all
  have hI : Integrable (fun θ : Uniform => if (θ : ℝ) < r then v-w else 0) volume := by
    change Integrable (({θ : Uniform | (θ : ℝ) < r} : Set Uniform).indicator (fun _ => v-w)) volume
    exact (integrable_const _).indicator (measurableSet_lt measurable_subtype_coe measurable_const)
  rw [heq, integral_add hI (integrable_const w), integral_indicator_lt hr hr']
  simp
  ring

private theorem observation_mean_from_slots (est ρ : ℝ) (x z : Prices) (prob : Prices → ℝ)
    (f : Fin 3 → Uniform → ℝ) (hf : ∀ i u, 0 ≤ f i u)
    (hmean : ∀ θ i, streamLaw
      (success (observationMixing est i) (observationBias prob ρ x z θ i)) = ENNReal.ofReal (f i (θ i))) :
    (∫ s, ((observationProc est ρ x z).out prob s.1 s.2).getD 0 ∂(Proc.law observationSeedLaw)) =
      observationCoefficient est ρ x * ∏ i, ∫ θ : Uniform, f i θ := by
  let A := observationSuccess est ρ x z prob
  let c := observationCoefficient est ρ x
  have hA : MeasurableSet A := measurable_observationSuccess est ρ x z prob
  let I := A.indicator (fun _ => (1 : ℝ))
  have hI : Integrable I observationLaw := (integrable_const _).indicator hA
  have hIm : Measurable I := measurable_const.indicator hA
  have heq : (fun s : ObservationPath => ((observationProc est ρ x z).out prob s.1 s.2).getD 0) =
      fun s => c * I (observationSample s) := by
    funext s
    rw [observation_out_getD]
    change A.indicator (fun _ => c) (observationSample s) = _
    by_cases hs : observationSample s ∈ A <;> simp [I, hs]
  rw [heq, integral_const_mul,
    ← integral_map measurable_observationSample.aemeasurable hIm.aestronglyMeasurable,
    observationSample_law]
  congr 1
  unfold observationLaw at hI ⊢
  rw [integral_prod I hI]
  have hcond (θ : Fin 3 → Uniform) :
      (∫ v, I (θ,v) ∂(Measure.infinitePi fun _ : Fin 3 => streamLaw)) = ∏ i, f i (θ i) := by
    have he : (fun v => I (θ,v)) = fun v =>
        ∏ i, slotSuccessIndicator (observationMixing est i) (observationBias prob ρ x z θ i) (v i) := by
      funext v
      exact observationSuccessIndicator_eq est ρ x z prob (θ,v)
    rw [he, Measure.infinitePi_eq_pi]
    rw [integral_fintype_prod_eq_prod
      (fun i => slotSuccessIndicator (observationMixing est i) (observationBias prob ρ x z θ i))]
    simp_rw [slotSuccessIndicator_integral, hmean θ, ENNReal.toReal_ofReal (hf _ _)]
  simp_rw [hcond]
  rw [selectorLaw, Measure.infinitePi_eq_pi, integral_fintype_prod_eq_prod f]

private theorem observation_slot_spec (est ρ : ℝ) (x z : Prices) (prob : Prices → ℝ)
    (he : 0 < est) (he' : est ≤ 1)
    (hp : ∀ y ∈ ({z,(x.1,z.2),(z.1,x.2)} : Set Prices),
      est / 10 ≤ prob y ∧ prob y ≤ 10 * est ∧ prob y ≤ 1) (θ : Fin 3 → Uniform) (i : Fin 3) :
    (∫⁻ s, totalRounds (observationMixing est i) (observationBias prob ρ x z θ i) s ∂streamLaw) ≤
      ENNReal.ofReal (3000 / est) ∧
    streamLaw (success (observationMixing est i) (observationBias prob ρ x z θ i)) =
      ENNReal.ofReal (if i = 0 then prob z / (20*est)
        else est / (20 * observationBias prob ρ x z θ i)) := by
  let y := observationPrice ρ x z θ i
  let p := prob y
  have hy := hp y (observationPrice_mem ρ x z θ i)
  have hp₀ : 0 < p := (by positivity : 0 < est/10).trans_le hy.1
  have hest : positiveEstimate est = est := by simp [positiveEstimate, he]
  by_cases hi : i = 0
  · have hyp : p = prob z := by simp [p, y, observationPrice, hi]
    let c := 1 / (20 * positiveEstimate est)
    have hc : 0 < c := by dsimp [c]; positivity [positiveEstimate_pos est]
    have hce : c = 1 / (20 * est) := by unfold c; rw [hest]
    have hcp : c * p ≤ 1/2 := by
      rw [hce]
      have he₁ : 0 < 20 * est := by positivity
      rw [one_div, inv_mul_eq_div]
      apply (div_le_iff₀ he₁).mpr
      linarith [hy.2.1]
    have hb : 0 < mix p (linearMixing c hc).upWeight := by rw [linear_up]; positivity
    have hab : 2 * mix p (linearMixing c hc).downWeight ≤ mix p (linearMixing c hc).upWeight := by
      rw [linear_down, linear_up]
      rw [show 2 * (c*p/(1+c)) = (2*(c*p))/(1+c) by ring]
      apply (div_le_div_iff_of_pos_right (by positivity : 0 < 1+c)).2
      linarith
    have hmean := stream_success (linearMixing c hc) hp₀.le hy.2.2 hb hab
    have hdur := lintegral_rounds_le (linearMixing c hc) hp₀.le hy.2.2 hb hab
    rw [linear_down, linear_up] at hmean
    rw [linear_up] at hdur
    simp only [if_pos hi, observationMixing]
    change _ ≤ _ ∧ _ = ENNReal.ofReal (prob z / (20*est))
    refine ⟨hdur.trans (ENNReal.ofReal_le_ofReal ?_), hmean.trans ?_⟩
    · calc
        282 / (1 / (1 + c)) = 282 * (1 + c) := by simp
        _ ≤ 3000 / est := by
          apply (le_div_iff₀ he).mpr
          rw [hce]
          have hh : (1 / (20 * est)) * est = 1 / 20 := by field_simp
          rw [mul_assoc, add_mul, hh, one_mul]
          linarith
    · congr 1
      rw [← hyp, hce]
      field_simp
  · let m := positiveEstimate est / 20
    have hm : 0 < m := div_pos (positiveEstimate_pos _) (by norm_num)
    have hme : m = est / 20 := by unfold m; rw [hest]
    have hmp : 2 * m ≤ p := by rw [hme]; linarith [hy.1]
    have hb : 0 < mix p (reciprocalMixing m hm).upWeight := by rw [reciprocal_up]; positivity
    have hab : 2 * mix p (reciprocalMixing m hm).downWeight ≤ mix p (reciprocalMixing m hm).upWeight := by
      rw [reciprocal_down, reciprocal_up]
      rw [show 2 * (m/(1+m)) = (2*m)/(1+m) by ring]
      exact (div_le_div_iff_of_pos_right (by positivity : 0 < 1+m)).2 hmp
    have hmean := stream_success (reciprocalMixing m hm) hp₀.le hy.2.2 hb hab
    have hdur := lintegral_rounds_le (reciprocalMixing m hm) hp₀.le hy.2.2 hb hab
    rw [reciprocal_down, reciprocal_up] at hmean
    rw [reciprocal_up] at hdur
    simp only [if_neg hi, observationMixing]
    change _ ≤ _ ∧ _ = ENNReal.ofReal (est / (20*p))
    refine ⟨hdur.trans (ENNReal.ofReal_le_ofReal ?_), hmean.trans ?_⟩
    · calc
        282 / (p/(1+m)) = (282 * (1+m))/p := by field_simp
        _ ≤ 300 / p := (div_le_div_iff_of_pos_right hp₀).2 (by rw [hme]; linarith)
        _ ≤ 3000 / est := by
          apply (div_le_div_iff₀ hp₀ he).2
          linarith [hy.1]
    · congr 1
      rw [hme]
      field_simp [hm.ne', hp₀.ne']

private theorem observation_law_spec (E : Environment) (hE : RegularUnit E)
    (δ : ℝ) (hδ : 0 < δ) (c : Candidate) (hc : c.Valid E δ) (ρ : ℝ) (hρ : 0 < ρ)
    (x z : Prices) (hx : x ∈ c.region) (hz : z ∈ c.region) :
    (observationProc c.est ρ x z).expRounds (P E) observationSeedLaw ≤ ENNReal.ofReal (27000 / δ) ∧
    Proc.law observationSeedLaw {s | (observationProc c.est ρ x z).out (P E) s.1 s.2 = none} = 0 ∧
    (∫ s, ((observationProc c.est ρ x z).out (P E) s.1 s.2).getD 0 ∂(Proc.law observationSeedLaw)) =
      1 / auxProfit E (ρ * balance E z) x := by
  rcases hc with ⟨hK, hcompact, hconv, hw, haux, hcross, he, he', hwidth⟩
  have hc' : c.Valid E δ := ⟨hK,hcompact,hconv,hw,haux,hcross,he,he',hwidth⟩
  have he₀ := hδ.trans_le he
  have hp : ∀ y ∈ ({z,(x.1,z.2),(z.1,x.2)} : Set Prices),
      c.est / 10 ≤ P E y ∧ P E y ≤ 10 * c.est ∧ P E y ≤ 1 := by
    intro y hy
    have hy' : y ∈ ({x,z,(x.1,z.2),(z.1,x.2)} : Set Prices) := mem_insert_of_mem _ hy
    have hb := (hcross x hx z hz).2.2 y hy'
    exact ⟨hb.1,hb.2,((onUnit_facts E hE.1).1 y).2⟩
  let N : Fin 3 → ENNReal := fun _ => ENNReal.ofReal (3000 / c.est)
  have hb i θ := (observation_slot_spec c.est ρ x z (P E) he₀ he' hp θ i).1
  have hcost := observation_expRounds_le c.est ρ x z (P E) N hb
  have hcost' : 3 * ∑ i, N i ≤ ENNReal.ofReal (27000 / δ) := by
    simp only [N, Fin.sum_univ_three]
    have hp₀ : 0 ≤ 3000 / c.est := by positivity
    have hthree : (3 : ENNReal) = ENNReal.ofReal (3 : ℝ) := by norm_num
    rw [← ENNReal.ofReal_add hp₀ hp₀, ← ENNReal.ofReal_add (add_nonneg hp₀ hp₀) hp₀,
      hthree, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
    apply ENNReal.ofReal_le_ofReal
    rw [show (3 : ℝ) * (3000 / c.est + 3000 / c.est + 3000 / c.est) = 27000 / c.est by ring]
    exact div_le_div_of_nonneg_left (by norm_num) hδ he
  refine ⟨hcost.trans hcost', observation_out_measured_none _ _ _ _ _ N (fun _ => ENNReal.ofReal_ne_top) hb, ?_⟩
  let f := fun i (θ : Uniform) =>
    if i = (0 : Fin 3) then P E z / (20*c.est)
    else if (θ : ℝ) < referenceWeight ρ then c.est / (20*P E (x.1,z.2))
      else c.est / (20*P E (z.1,x.2))
  have hpos₁ : 0 < P E (x.1,z.2) := lt_of_lt_of_le (by positivity) (hp _ (by simp)).1
  have hpos₂ : 0 < P E (z.1,x.2) := lt_of_lt_of_le (by positivity) (hp _ (by simp)).1
  have hfn i θ : 0 ≤ f i θ := by
    unfold f
    split
    · have := ((onUnit_facts E hE.1).1 z).1
      positivity
    · split <;> positivity
  have hfm θ i := (observation_slot_spec c.est ρ x z (P E) he₀ he' hp θ i).2
  have hfm' θ i : streamLaw
      (success (observationMixing c.est i) (observationBias (P E) ρ x z θ i)) =
      ENNReal.ofReal (f i (θ i)) := by
    rw [hfm]
    by_cases hi : i=0
    · simp [f,hi]
    · unfold f observationBias observationPrice
      simp only [if_neg hi]
      split <;> rfl
  rw [observation_mean_from_slots c.est ρ x z (P E) f hfn hfm', Fin.prod_univ_three]
  have hm0 : (∫ θ : Uniform, f 0 θ) = P E z / (20*c.est) := by simp [f]
  have wm := referenceWeight_bounds hρ
  have hm (i : Fin 3) (hi : i ≠ 0) :
      (∫ θ : Uniform, f i θ) = observationReciprocalMean E c ρ x z := by
    simp only [f, if_neg hi]
    exact integral_uniform_choice wm.1 wm.2 _ _
  rw [hm0, hm 1 (by decide), hm 2 (by decide)]
  change observationScale c ρ x * (_ * _ * _) = _
  rw [show P E z / (20*c.est) * observationReciprocalMean E c ρ x z *
      observationReciprocalMean E c ρ x z =
      P E z / (20*c.est) * (observationReciprocalMean E c ρ x z)^2 by ring, ← mul_assoc]
  exact observation_mean_identity E hE δ hδ c hc' ρ hρ x z hx hz

end BilateralProfitRegular.Factory
end BundlePart015


section BundlePart016



namespace BilateralProfitRegular

open Classical MeasureTheory Set MechanismDesign.BilateralTrade
open scoped BigOperators ENNReal

namespace Factory

private theorem calibration_cost_le (T : ℕ) (η : ℝ) (hη : 0 < η) (hη' : η < 1)
    (hT : gridK η ≤ T) (E : Environment) (hE : RegularUnit E) (δ : ℝ) (hηδ : η < δ)
    (c : Candidate) (hc : c.Valid E δ) (z : CalibrationPrices) (hz : z ∈ c.region) :
    (calibrationProc T η δ c.est c.offset c.root z).QueriesIn triT ∧
    (calibrationProc T η δ c.est c.offset c.root z).expCost (P E) (Measure.dirac ())
        (fun y => muStar E - mu E y) ≤ ENNReal.ofReal (5000000000 * Real.log T / η) := by
  let F := calibrationProc T η δ c.est c.offset c.root z
  let n := calibrationSamples T η δ c.est
  have cross := hc.2.2.2.2.2.1 z hz c.root hc.2.2.2.1
  have hF : F.QueriesIn triT := by
    intro ω h y hy
    have hy' := calibration_queries T η δ c.est c.offset c.root z ω h y hy
    simp only [mem_insert_iff, mem_singleton_iff] at hy'
    rcases hy' with rfl | rfl
    · exact cross.1
    · exact cross.2.1
  refine ⟨hF,?_⟩
  have hn : (2 * (n : ℝ)) ≤ 5000000000 * Real.log T / η :=
    calibration_samples_le T (calibration_T_ge_two T η hη hη' hT) η δ c.est hη hη'
      (hη.trans hηδ) hc.2.2.2.2.2.2.1
  have hcost (y : CalibrationPrices) (hy : y ∈ triT) :
      ENNReal.ofReal (muStar E - mu E y) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    have hμ := (onUnit_facts E hE.1).2.2.2.1.2
    have hg : 0 ≤ mu E y := by
      rw [mu_formula]
      exact mul_nonneg (sub_nonneg.mpr hy.2.1) ((onUnit_facts E hE.1).1 y).1
    linarith
  have hpoint (s : Unit × Stream) :
      (∑' k, ((F.query (P E) s.1 s.2 k).map
        (fun q => ENNReal.ofReal (muStar E - mu E q))).getD 0) ≤ (2*n : ℕ) := by
    rcases s with ⟨⟨⟩,U⟩
    rw [tsum_eq_sum (s := Finset.range (2*n))]
    · calc
        _ ≤ ∑ k ∈ Finset.range (2*n), (1 : ENNReal) := by
          apply Finset.sum_le_sum
          intro k _
          unfold Proc.query
          cases he : F.step () (F.hist (P E) () U k) with
          | inl y => exact hcost y (hF _ _ _ he)
          | inr r => simp
        _ = _ := by simp
    · intro k hk
      have hnk : 2*n ≤ k := Nat.le_of_not_gt (by simpa using hk)
      have hd := (calibration_stopped T η δ c.est c.offset c.root z (P E) U k).mpr hnk
      change (F.step () (F.hist (P E) () U k)).isRight = true at hd
      unfold Proc.query
      cases he : F.step () (F.hist (P E) () U k) with
      | inl y => simp [he] at hd
      | inr r => simp
  change F.expCost (P E) (Measure.dirac ()) _ ≤ _
  unfold Proc.expCost
  calc
    _ ≤ ∫⁻ _s, ((2*n : ℕ) : ENNReal) ∂(Proc.law (Measure.dirac ())) := lintegral_mono hpoint
    _ = ((2*n : ℕ) : ENNReal) := by
      haveI : IsProbabilityMeasure (Proc.law (Measure.dirac ())) := by unfold Proc.law; infer_instance
      simp
    _ ≤ _ := by
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hn)

end Factory

open Factory

private theorem lemma_6_5 :
    ∃ C : ℝ, 0 < C ∧
      (∀ (T : ℕ) (η : ℝ), 0 < η → η < 1 → gridK η ≤ T →
        ∀ (δ : ℝ) (c : Candidate) (z : ℝ × ℝ),
        ∃ (Ω : Type) (_ : MeasurableSpace Ω) (Pω : Measure Ω) (_ : IsProbabilityMeasure Pω)
          (cal : Proc (ℝ × ℝ) ℝ Ω),
          ∀ E : Environment, RegularUnit E → η < δ → δ ≤ muStar E → muStar E < 6 * δ →
            c.Valid E δ → z ∈ c.region →
            cal.QueriesIn triT ∧
            cal.expCost (P E) Pω (fun y => muStar E - mu E y) ≤
              ENNReal.ofReal (C * Real.log T / η) ∧
            Proc.law Pω {x | ¬ ∃ ρ, cal.out (P E) x.1 x.2 = some ρ ∧ CalibValid E η δ c z ρ} ≤
              ENNReal.ofReal (1 / T)) ∧
      (∀ (η δ : ℝ) (c : Candidate) (z : ℝ × ℝ) (ρ : ℝ) (x : ℝ × ℝ),
        ∃ (Ω : Type) (_ : MeasurableSpace Ω) (Pω : Measure Ω) (_ : IsProbabilityMeasure Pω)
          (obs : Proc (ℝ × ℝ) ℝ Ω),
          ∀ E : Environment, RegularUnit E → 0 < η → η < 1 → η < δ → δ ≤ muStar E →
            muStar E < 6 * δ → c.Valid E δ → z ∈ c.region → CalibValid E η δ c z ρ →
            x ∈ c.region →
            obs.QueriesFirst ∧
            obs.OutputsIn (Set.Icc 0 (C / δ)) ∧
            obs.expRounds (P E) Pω ≤ ENNReal.ofReal (C / δ) ∧
            Proc.law Pω {y | obs.out (P E) y.1 y.2 = none} = 0 ∧
            ∫ y, (obs.out (P E) y.1 y.2).getD 0 ∂(Proc.law Pω) =
              1 / auxProfit E (ρ * balance E z) x ∧
            ∀ ω h y, obs.step ω h = Sum.inl y →
              y ∈ triT ∧
              muStar E - mu E y ≤
                C * (muStar E - auxProfit E (ρ * balance E z) z) +
                  C * δ ^ 2 * (1 / auxProfit E (ρ * balance E z) x -
                    sInf ((fun a => 1 / auxProfit E (ρ * balance E z) a) '' c.region))) := by
  refine ⟨5000000000, by norm_num, ?_,?_⟩
  · intro T η hη hη' hT δ c z
    refine ⟨Unit, inferInstance, Measure.dirac (), inferInstance,
      calibrationProc T η δ c.est c.offset c.root z, ?_⟩
    intro E hE hηδ _ _ hc hz
    have hcost := calibration_cost_le T η hη hη' hT E hE δ hηδ c hc z hz
    exact ⟨hcost.1, hcost.2, calibration_failure_le T η hη hη' hT E hE δ hηδ c hc z hz⟩
  · intro η δ c z ρ x
    refine ⟨ObservationSeed, inferInstance, observationSeedLaw, inferInstance,
      observationProc c.est ρ x z, ?_⟩
    intro E hE hη _ hηδ _ hmax hc hz hρ hx
    have hδ := hη.trans hηδ
    have hsize := observationScale_bounds E hE c η δ hη hηδ hc z hz ρ hρ x hx
    have hlaw := observation_law_spec E hE δ hδ c hc ρ hρ.1 x z hx hz
    have hsize' : observationCoefficient c.est ρ x ≤ 5000000000 / δ :=
      hsize.2.trans (div_le_div_of_nonneg_right (by norm_num) hδ.le)
    have hcost' : ENNReal.ofReal (27000 / δ) ≤ ENNReal.ofReal (5000000000 / δ) :=
      ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (by norm_num) hδ.le)
    refine ⟨observation_queries_first _ _ _ _, observation_outputs _ _ _ _ _ hsize.1 hsize',
      hlaw.1.trans hcost', hlaw.2.1, hlaw.2.2, ?_⟩
    intro ω h y hy
    have hy' := observation_queries c.est ρ x z ω h y hy
    have h := observation_query_gap E hE c η δ hη hηδ hmax hc z hz ρ hρ x hx y hy'
    refine ⟨h.1, h.2.trans ?_⟩
    let r := auxProfit E (ρ * balance E z)
    let L := fun a => 1 / r a
    have hz₀ := calibrated_candidate_profit E hE c η δ hη hηδ hc z hz ρ hρ z hz
    have hg : 0 ≤ muStar E - r z := sub_nonneg.mpr (hz₀.2.1.trans hz₀.2.2)
    have hL : 0 ≤ L x - sInf (L '' c.region) := by
      apply sub_nonneg.mpr (csInf_le _ (mem_image_of_mem L hx))
      refine ⟨0,?_⟩
      rintro _ ⟨a,ha,rfl⟩
      have hlam := mul_pos hρ.1 (balance_pos E hE.1 (hc.1 hz))
      exact (one_div_pos.mpr (auxProfit_pos E hE.1 hlam (hc.1 ha))).le
    change 8 * (muStar E - r z) + 144 * δ^2 * (L x - sInf (L '' c.region)) ≤
      5000000000 * (muStar E - r z) + 5000000000 * δ^2 * (L x - sInf (L '' c.region))
    gcongr <;> norm_num

end BilateralProfitRegular
end BundlePart016

open BilateralProfitRegular
open MeasureTheory MechanismDesign.BilateralTrade

theorem solution :
    ∃ C : ℝ, 0 < C ∧
      (∀ (T : ℕ) (η : ℝ), 0 < η → η < 1 → gridK η ≤ T →
        ∀ (δ : ℝ) (c : Candidate) (z : ℝ × ℝ),
        ∃ (Ω : Type) (_ : MeasurableSpace Ω) (Pω : Measure Ω) (_ : IsProbabilityMeasure Pω)
          (cal : Proc (ℝ × ℝ) ℝ Ω),
          ∀ E : Environment, RegularUnit E → η < δ → δ ≤ muStar E → muStar E < 6 * δ →
            c.Valid E δ → z ∈ c.region →
            cal.QueriesIn triT ∧
            cal.expCost (P E) Pω (fun y => muStar E - mu E y) ≤
              ENNReal.ofReal (C * Real.log T / η) ∧
            Proc.law Pω {x | ¬ ∃ ρ, cal.out (P E) x.1 x.2 = some ρ ∧ CalibValid E η δ c z ρ} ≤
              ENNReal.ofReal (1 / T)) ∧
      (∀ (η δ : ℝ) (c : Candidate) (z : ℝ × ℝ) (ρ : ℝ) (x : ℝ × ℝ),
        ∃ (Ω : Type) (_ : MeasurableSpace Ω) (Pω : Measure Ω) (_ : IsProbabilityMeasure Pω)
          (obs : Proc (ℝ × ℝ) ℝ Ω),
          ∀ E : Environment, RegularUnit E → 0 < η → η < 1 → η < δ → δ ≤ muStar E →
            muStar E < 6 * δ → c.Valid E δ → z ∈ c.region → CalibValid E η δ c z ρ →
            x ∈ c.region →
            obs.QueriesFirst ∧
            obs.OutputsIn (Set.Icc 0 (C / δ)) ∧
            obs.expRounds (P E) Pω ≤ ENNReal.ofReal (C / δ) ∧
            Proc.law Pω {y | obs.out (P E) y.1 y.2 = none} = 0 ∧
            ∫ y, (obs.out (P E) y.1 y.2).getD 0 ∂(Proc.law Pω) =
              1 / auxProfit E (ρ * balance E z) x ∧
            ∀ ω h y, obs.step ω h = Sum.inl y →
              y ∈ triT ∧
              muStar E - mu E y ≤
                C * (muStar E - auxProfit E (ρ * balance E z) z) +
                  C * δ ^ 2 * (1 / auxProfit E (ρ * balance E z) x -
                    sInf ((fun a => 1 / auxProfit E (ρ * balance E z) a) '' c.region))) := by
  exact BilateralProfitRegular.lemma_6_5
