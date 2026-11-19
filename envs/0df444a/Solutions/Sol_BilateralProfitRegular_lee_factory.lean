-- Prove2me | solution 1 for BilateralProfitRegular.lee_factory
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-18T15:29:55.312659+00:00
-- url     : https://prove2.me/submissions/6edf2094-efd5-4991-a31d-3b85cad7d5e2

import Mathlib
import Definitions.Def_BilateralProfitRegular_Proc


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
end BundlePart002


section BundlePart003


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
end BundlePart003


section BundlePart004


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
end BundlePart004

open BilateralProfitRegular
open MeasureTheory

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℝ, 0 < m → m ≤ 1 / 20 →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (Pω : Measure Ω) (_ : IsProbabilityMeasure Pω)
        (F : Proc Unit Bool Ω),
        ∀ p : ℝ, 2 * m ≤ p → p ≤ 1 → p ≤ 200 * m →
          Proc.law Pω {x | F.out (fun _ => p) x.1 x.2 = none} = 0 ∧
          Proc.law Pω {x | F.out (fun _ => p) x.1 x.2 = some true} = ENNReal.ofReal (m / p) ∧
          F.expRounds (fun _ => p) Pω ≤ ENNReal.ofReal (C / p) := by
  exact BilateralProfitRegular.lee_factory
