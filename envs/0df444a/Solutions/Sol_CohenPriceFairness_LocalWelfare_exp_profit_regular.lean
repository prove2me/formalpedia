-- Prove2me | solution 1 for CohenPriceFairness.LocalWelfare.exp_profit_regular
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-01T02:15:48.61195+00:00
-- url     : https://prove2.me/submissions/a89a1de6-abac-4fba-ab96-31ec5533b5e2

import Mathlib
import Definitions.Def_CohenPriceFairness_LocalWelfare_Sensitivity
import Definitions.Def_CohenPriceFairness_LocalWelfare_Families
import Theorems.Thm_ExpLaw_tail
import Theorems.Thm_ExpLaw_mean_excess

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics Real Set

namespace CohenPriceFairness.LocalWelfare.Sol_exp_profit_regular

noncomputable def eb_R (l d c p : ℝ) : ℝ := d * (p - c) * exp (-(l * p))

lemma eb_R_hasDeriv (l d c p : ℝ) :
    HasDerivAt (eb_R l d c) (d * exp (-(l * p)) * (1 - l * (p - c))) p := by
  have h1 := ((hasDerivAt_id' p).sub_const c).const_mul d
  have h2 := ((hasDerivAt_id' p).const_mul l).neg.exp
  have := h1.mul h2
  exact this.congr_deriv (by simp only [Pi.neg_apply]; ring)

lemma eb_R_strictMono {l d : ℝ} (c : ℝ) (hl : 0 < l) (hd : 0 < d) :
    StrictMonoOn (eb_R l d c) (Iic (c + 1 / l)) := by
  apply strictMonoOn_of_deriv_pos (convex_Iic _)
  · exact fun x _ => (eb_R_hasDeriv l d c x).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Iic] at hx
    rw [(eb_R_hasDeriv l d c x).deriv]
    have hx' : x < c + 1 / l := hx
    have : l * (x - c) < 1 := by
      have := mul_lt_mul_of_pos_left (show x - c < 1 / l by linarith) hl
      rwa [mul_one_div_cancel hl.ne'] at this
    have := exp_pos (-(l * x))
    apply mul_pos (mul_pos hd this); linarith

lemma eb_R_strictAnti {l d : ℝ} (c : ℝ) (hl : 0 < l) (hd : 0 < d) :
    StrictAntiOn (eb_R l d c) (Ici (c + 1 / l)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _)
  · exact fun x _ => (eb_R_hasDeriv l d c x).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    rw [(eb_R_hasDeriv l d c x).deriv]
    have hx' : c + 1 / l < x := hx
    have : 1 < l * (x - c) := by
      have := mul_lt_mul_of_pos_left (show 1 / l < x - c by linarith) hl
      rwa [mul_one_div_cancel hl.ne'] at this
    have := exp_pos (-(l * x))
    apply mul_neg_of_pos_of_neg (mul_pos hd this); linarith

lemma eb_R_lt {l d : ℝ} (c : ℝ) (hl : 0 < l) (hd : 0 < d) {p : ℝ} (hp : p ≠ c + 1 / l) :
    eb_R l d c p < eb_R l d c (c + 1 / l) := by
  rcases lt_or_gt_of_ne hp with h | h
  · exact eb_R_strictMono c hl hd (mem_Iic.mpr h.le) (mem_Iic.mpr le_rfl) h
  · exact eb_R_strictAnti c hl hd (mem_Ici.mpr le_rfl) (mem_Ici.mpr h.le) h

lemma eb_R_le {l d : ℝ} (c : ℝ) (hl : 0 < l) (hd : 0 < d) (p : ℝ) :
    eb_R l d c p ≤ eb_R l d c (c + 1 / l) := by
  by_cases hp : p = c + 1 / l
  · rw [hp]
  · exact (eb_R_lt c hl hd hp).le

lemma eb_R_loc {l d : ℝ} (c : ℝ) (hl : 0 < l) (hd : 0 < d) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ p, eb_R l d c (c + 1 / l) - δ ≤ eb_R l d c p → |p - (c + 1 / l)| < ε := by
  set b := c + 1 / l with hbdef
  have h1 : eb_R l d c (b - ε) < eb_R l d c b := eb_R_lt c hl hd (by linarith)
  have h2 : eb_R l d c (b + ε) < eb_R l d c b := eb_R_lt c hl hd (by linarith)
  refine ⟨min (eb_R l d c b - eb_R l d c (b - ε)) (eb_R l d c b - eb_R l d c (b + ε)) / 2,
    by positivity, fun p hp => ?_⟩
  have m1 := min_le_left (eb_R l d c b - eb_R l d c (b - ε)) (eb_R l d c b - eb_R l d c (b + ε))
  have m2 := min_le_right (eb_R l d c b - eb_R l d c (b - ε)) (eb_R l d c b - eb_R l d c (b + ε))
  rw [abs_lt]
  by_contra hcon
  rcases not_and_or.mp hcon with h | h
  · replace h := not_lt.mp h
    have : eb_R l d c p ≤ eb_R l d c (b - ε) :=
      (eb_R_strictMono c hl hd).monotoneOn (mem_Iic.mpr (by linarith)) (mem_Iic.mpr (by linarith))
        (by linarith)
    linarith
  · replace h := not_lt.mp h
    have : eb_R l d c p ≤ eb_R l d c (b + ε) :=
      (eb_R_strictAnti c hl hd).antitoneOn (mem_Ici.mpr (by linarith)) (mem_Ici.mpr (by linarith))
        (by linarith)
    linarith

lemma eb_exp3 {u : ℝ} (hu : |u| ≤ 1) : |exp u - (1 + u + u ^ 2 / 2)| ≤ |u| ^ 3 := by
  have hE := Real.exp_bound hu (n := 3) (by norm_num)
  have hs : ∑ m ∈ Finset.range 3, u ^ m / (m.factorial : ℝ) = 1 + u + u ^ 2 / 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [hs] at hE
  refine hE.trans (mul_le_of_le_one_right (by positivity) ?_)
  norm_num [Nat.factorial]

lemma eb_R_taylor {l : ℝ} (d c : ℝ) (hl : 0 < l) :
    (fun h => eb_R l d c (c + 1 / l + h) - eb_R l d c (c + 1 / l) -
      (-(d * l * exp (-(l * (c + 1 / l))))) / 2 * h ^ 2) =o[𝓝 0] (fun h => h ^ 2) := by
  apply IsBigO.trans_isLittleO _ (isLittleO_pow_pow (show 2 < 3 by norm_num))
  apply IsBigO.of_bound (5 / 2 * |d| * exp (-(l * (c + 1 / l))) * l ^ 2)
  have hl1 : 0 < 1 / l := one_div_pos.mpr hl
  filter_upwards [Ioo_mem_nhds (neg_lt_zero.mpr hl1) hl1] with h hh
  have hu : |-(l * h)| ≤ 1 := by
    rw [abs_neg, abs_le]
    have a := mul_lt_mul_of_pos_left hh.2 hl
    have b := mul_lt_mul_of_pos_left hh.1 hl
    rw [mul_one_div_cancel hl.ne'] at a
    rw [mul_neg, mul_one_div_cancel hl.ne'] at b
    constructor <;> linarith
  have hE := eb_exp3 hu
  set u := -(l * h) with hu_def
  set q := exp (-(l * (c + 1 / l))) with hq
  set E := exp u - (1 + u + u ^ 2 / 2) with hE_def
  have hE2 : |E| ≤ |u| ^ 3 := hE
  have key : eb_R l d c (c + 1 / l + h) - eb_R l d c (c + 1 / l) -
      (-(d * l * q)) / 2 * h ^ 2 = d * q / l * (-u ^ 3 / 2 + (1 - u) * E) := by
    unfold eb_R
    have : exp (-(l * (c + 1 / l + h))) = q * exp u := by
      rw [hq, hu_def, ← exp_add]; ring_nf
    rw [this, ← hq, hE_def, hu_def]
    field_simp
    ring
  rw [key, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
  have hq0 : 0 < q := exp_pos _
  have habs1 : |d * q / l| = |d| * q / l := by
    rw [abs_div, abs_mul, abs_of_pos hq0, abs_of_pos hl]
  have hu1 : |u| ≤ 1 := hu
  have h1u : |1 - u| ≤ 2 := by
    have := abs_sub (1:ℝ) u; rw [abs_one] at this; linarith
  have hY : |-u ^ 3 / 2 + (1 - u) * E| ≤ 5 / 2 * |u| ^ 3 := by
    have a1 : |-u ^ 3 / 2| = |u| ^ 3 / 2 := by
      rw [neg_div, abs_neg, abs_div, abs_pow]; norm_num
    have a2 : |(1 - u) * E| ≤ 2 * |u| ^ 3 := by
      rw [abs_mul]
      exact mul_le_mul h1u hE2 (abs_nonneg _) (by norm_num)
    calc |-u ^ 3 / 2 + (1 - u) * E| ≤ |-u ^ 3 / 2| + |(1 - u) * E| := abs_add_le _ _
      _ ≤ 5 / 2 * |u| ^ 3 := by rw [a1]; linarith
  have hu3 : |u| ^ 3 = l ^ 3 * |h| ^ 3 := by
    rw [hu_def, abs_neg, abs_mul, abs_of_pos hl, mul_pow]
  rw [habs1, abs_pow]
  have hdq : 0 ≤ |d| * q / l := by positivity
  calc |d| * q / l * |-u ^ 3 / 2 + (1 - u) * E| ≤ |d| * q / l * (5 / 2 * |u| ^ 3) :=
        mul_le_mul_of_nonneg_left hY hdq
    _ = 5 / 2 * |d| * q * l ^ 2 * |h| ^ 3 := by rw [hu3]; field_simp

lemma eb_hasDerivAt_of_eq {f F : ℝ → ℝ} {F' p : ℝ} (hp : 0 < p) (heq : ∀ y, 0 < y → f y = F y)
    (hF : HasDerivAt F F' p) : HasDerivAt f F' p :=
  hF.congr_of_eventuallyEq (Filter.eventually_of_mem (Ioi_mem_nhds hp) (fun y hy => heq y hy))

lemma eb_contOn {f f' : ℝ → ℝ} (hf : ∀ p, 0 < p → HasDerivAt f (f' p) p) :
    ContinuousOn f (Ioi 0) :=
  fun p hp => (hf p hp).continuousAt.continuousWithinAt

lemma eb_profit_eq (m : Market) (rate : Fin 2 → ℝ) (hrate : ∀ i, 0 < rate i)
    (hlaw : ∀ i, m.law i = expMeasure (rate i)) (i : Fin 2) {p : ℝ} (hp : 0 ≤ p) :
    profit m i p = eb_R (rate i) (m.population i) m.cost p := by
  unfold profit demand eb_R; rw [hlaw i, ExpLaw.tail (hrate i) hp]

lemma eb_demand_eq (m : Market) (rate : Fin 2 → ℝ) (hrate : ∀ i, 0 < rate i)
    (hlaw : ∀ i, m.law i = expMeasure (rate i)) (i : Fin 2) {p : ℝ} (hp : 0 ≤ p) :
    demand m i p = exp (-(rate i * p)) := by
  unfold demand; rw [hlaw i, ExpLaw.tail (hrate i) hp]

lemma eb_surplus_eq (m : Market) (rate : Fin 2 → ℝ) (hrate : ∀ i, 0 < rate i)
    (hlaw : ∀ i, m.law i = expMeasure (rate i)) (i : Fin 2) {p : ℝ} (hp : 0 ≤ p) :
    surplus m i p = exp (-(rate i * p)) / rate i := by
  unfold surplus; rw [hlaw i, ExpLaw.mean_excess (hrate i) hp]
lemma eb_expneg_hasDeriv (l p : ℝ) :
    HasDerivAt (fun p => exp (-(l * p))) (-(l * exp (-(l * p)))) p := by
  have := ((hasDerivAt_id' p).const_mul l).neg.exp
  exact this.congr_deriv (by simp only [Pi.neg_apply]; ring)

lemma eb_BO_iff (m : Market) (hd : ∀ i, 0 < m.population i) (hc : 0 ≤ m.cost)
    (rate : Fin 2 → ℝ) (hrate : ∀ i, 0 < rate i)
    (hlaw : ∀ i, m.law i = expMeasure (rate i)) (b : Prices) :
    BaselineOptimal m b ↔ ∀ i, b i = m.cost + 1 / rate i := by
  have hps : ∀ i, 0 ≤ m.cost + 1 / rate i := fun i => by have := hrate i; positivity
  constructor
  · intro hb i
    obtain ⟨hb0, hmax⟩ := hb i
    by_contra hne
    have h1 := eb_R_lt m.cost (hrate i) (hd i) hne
    have h2 := hmax _ (hps i)
    rw [eb_profit_eq m rate hrate hlaw i (hps i), eb_profit_eq m rate hrate hlaw i hb0] at h2
    linarith
  · intro hb i
    refine ⟨hb i ▸ hps i, fun p hp => ?_⟩
    rw [eb_profit_eq m rate hrate hlaw i hp, eb_profit_eq m rate hrate hlaw i (hb i ▸ hps i), hb i]
    exact eb_R_le _ (hrate i) (hd i) p

lemma eb_lb {l : ℝ} (c : ℝ) (hl : 0 < l) : l * (c + 1 / l) = 1 + l * c := by
  field_simp; ring

end CohenPriceFairness.LocalWelfare.Sol_exp_profit_regular

open CohenPriceFairness.LocalWelfare CohenPriceFairness.LocalWelfare.Sol_exp_profit_regular
open MeasureTheory ProbabilityTheory Filter Topology Asymptotics Real Set

theorem solution (m : Market) (hd : ∀ i, 0 < m.population i) (hc : 0 ≤ m.cost)
    (rate : Fin 2 → ℝ) (hrate : ∀ i, 0 < rate i)
    (hlaw : ∀ i, m.law i = expMeasure (rate i)) :
    (∀ b : Prices, BaselineOptimal m b ↔ ∀ i, b i = m.cost + 1 / rate i) ∧
    ∀ b : Prices, BaselineOptimal m b →
      (∀ i, 0 < b i) ∧
      (∀ ε > 0, ∃ δ > 0, ∀ i, ∀ p, 0 ≤ p → profit m i (b i) - δ ≤ profit m i p → |p - b i| < ε) ∧
      (∃ η > 0, ∀ i, ContinuousOn (profit m i) (Set.Icc (b i - η) (b i + η))) ∧
      (∀ i, (fun h => profit m i (b i + h) - profit m i (b i) - (-(m.population i * rate i * Real.exp (-(1 + rate i * m.cost)))) / 2 * h ^ 2)
        =o[𝓝 0] (fun h => h ^ 2)) ∧
      (∀ i, HasDerivAt (surplus m i) (-demand m i (b i)) (b i)) ∧
      (∀ i, demand m i (b i) = Real.exp (-(1 + rate i * m.cost))) := by
  have hBO := eb_BO_iff m hd hc rate hrate hlaw
  refine ⟨hBO, fun b hb => ?_⟩
  have hbi := (hBO b).1 hb
  have hbpos : ∀ i, 0 < b i := fun i => by rw [hbi i]; have := hrate i; positivity
  have hlb : ∀ i, rate i * b i = 1 + rate i * m.cost := fun i => by
    rw [hbi i]; exact eb_lb _ (hrate i)
  have hdem : ∀ i, demand m i (b i) = exp (-(1 + rate i * m.cost)) := fun i => by
    rw [eb_demand_eq m rate hrate hlaw i (hbpos i).le, hlb i]
  refine ⟨hbpos, ?_, ?_, ?_, ?_, hdem⟩
  · intro ε hε
    obtain ⟨δ0, hδ0, H0⟩ := eb_R_loc m.cost (hrate 0) (hd 0) ε hε
    obtain ⟨δ1, hδ1, H1⟩ := eb_R_loc m.cost (hrate 1) (hd 1) ε hε
    refine ⟨min δ0 δ1, lt_min hδ0 hδ1, fun i p hp h => ?_⟩
    rw [eb_profit_eq m rate hrate hlaw i hp, eb_profit_eq m rate hrate hlaw i (hbpos i).le,
      hbi i] at h
    rw [hbi i]
    fin_cases i
    · exact H0 p (by have := min_le_left δ0 δ1; simp at h ⊢; linarith)
    · exact H1 p (by have := min_le_right δ0 δ1; simp at h ⊢; linarith)
  · have hRd : ∀ i, ∀ p, 0 < p → HasDerivAt (profit m i)
        (m.population i * exp (-(rate i * p)) * (1 - rate i * (p - m.cost))) p :=
      fun i p hp => eb_hasDerivAt_of_eq hp (fun y hy => eb_profit_eq m rate hrate hlaw i hy.le)
        (eb_R_hasDeriv _ _ _ p)
    refine ⟨min (b 0) (b 1) / 2, by have := hbpos 0; have := hbpos 1; positivity,
      fun i => ?_⟩
    have hsub : Set.Icc (b i - min (b 0) (b 1) / 2) (b i + min (b 0) (b 1) / 2) ⊆ Ioi 0 := by
      intro p hp
      have hmin : min (b 0) (b 1) ≤ b i := by
        fin_cases i
        · exact min_le_left _ _
        · exact min_le_right _ _
      have : 0 < min (b 0) (b 1) := lt_min (hbpos 0) (hbpos 1)
      simp only [mem_Ioi]; linarith [hp.1]
    exact (eb_contOn (hRd i)).mono hsub
  · intro i
    have := eb_R_taylor (m.population i) m.cost (hrate i)
    rw [eb_lb _ (hrate i), ← hbi i] at this
    refine this.congr' ?_ EventuallyEq.rfl
    filter_upwards [Ioo_mem_nhds (neg_lt_zero.mpr (hbpos i)) (hbpos i)] with h hh
    have : 0 ≤ b i + h := by linarith [hh.1]
    rw [eb_profit_eq m rate hrate hlaw i this, eb_profit_eq m rate hrate hlaw i (hbpos i).le]
  · intro i
    rw [eb_demand_eq m rate hrate hlaw i (hbpos i).le]
    refine eb_hasDerivAt_of_eq (hbpos i) (fun y hy => eb_surplus_eq m rate hrate hlaw i hy.le) ?_
    have := (eb_expneg_hasDeriv (rate i) (b i)).div_const (rate i)
    refine this.congr_deriv ?_
    have := (hrate i).ne'
    field_simp
