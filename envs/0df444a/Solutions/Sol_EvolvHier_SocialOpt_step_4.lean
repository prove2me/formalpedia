-- Prove2me | solution 1 for EvolvHier.SocialOpt.step_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T02:46:27.293748+00:00
-- url     : https://prove2.me/submissions/792a6ee6-3a4d-43d3-b667-8a12f2274de1

import Mathlib
import Definitions.Def_EvolvHier_SocialOpt_Setting

open scoped BigOperators
open Set Filter Topology

namespace EvolvHier.SocialOpt.EHAux

open EvolvHier.SocialOpt

variable (T : Technology)

/-! ### Basic facts about the technology -/

lemma p_pos {x : ℝ} (hx : 0 < x) : 0 < T.p x := by
  have := T.strictMono (Set.mem_Ici.mpr (le_refl (0:ℝ))) (show x ∈ Ici 0 from hx.le) hx
  simpa [T.zero] using this

lemma p_lt_one {x : ℝ} (hx : 0 ≤ x) : T.p x < 1 := T.lt_one x hx

lemma p_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ T.p x := T.nonneg x hx

/-- Tangent-line inequality at a point `χ > 0`, strict away from `χ`. -/
lemma tangent_lt {χ y : ℝ} (hχ : 0 < χ) (hy : 0 ≤ y) (hne : y ≠ χ) :
    T.p y < T.p χ + deriv T.p χ * (y - χ) := by
  rcases lt_or_gt_of_ne hne with h | h
  · have := T.strictConcave.deriv_lt_slope (show y ∈ Ici (0:ℝ) from hy)
      (show χ ∈ Ici (0:ℝ) from hχ.le) h (T.differentiable χ hχ)
    rw [slope_def_field] at this
    have hpos : 0 < χ - y := by linarith
    rw [lt_div_iff₀ hpos] at this
    nlinarith
  · have := T.strictConcave.slope_lt_deriv (show χ ∈ Ici (0:ℝ) from hχ.le)
      (show y ∈ Ici (0:ℝ) from hy) h (T.differentiable χ hχ)
    rw [slope_def_field] at this
    have hpos : 0 < y - χ := by linarith
    rw [div_lt_iff₀ hpos] at this
    nlinarith

lemma tangent_le {χ y : ℝ} (hχ : 0 < χ) (hy : 0 ≤ y) :
    T.p y ≤ T.p χ + deriv T.p χ * (y - χ) := by
  by_cases h : y = χ
  · subst h; simp
  · exact (tangent_lt T hχ hy h).le

/-- Existence of the investment level `χ` with `p'(χ) = 1`. -/
lemma exists_chi : ∃ χ : ℝ, 0 < χ ∧ deriv T.p χ = 1 := by
  obtain ⟨a, ha1, ha0⟩ :=
    ((T.deriv_zero.eventually (eventually_gt_atTop (1:ℝ))).and
      (self_mem_nhdsWithin : Ioi (0:ℝ) ∈ 𝓝[>] (0:ℝ))).exists
  have ha0' : 0 < a := ha0
  set b := a + 2 with hb
  have hb0 : 0 < b := by linarith
  have hdb : deriv T.p b < 1 := by
    have := T.strictConcave.concaveOn.deriv_le_slope (show a ∈ Ici (0:ℝ) from ha0'.le)
      (show b ∈ Ici (0:ℝ) from hb0.le) (by linarith) (T.differentiable b hb0)
    rw [slope_def_field] at this
    have h1 := T.lt_one b hb0.le
    have h2 := T.nonneg a ha0'.le
    have : deriv T.p b ≤ (T.p b - T.p a) / 2 := by simpa [hb] using this
    linarith [show (T.p b - T.p a) / 2 < 1 by linarith]
  have hab : a ≤ b := by linarith
  have hder : ∀ x ∈ Icc a b, HasDerivWithinAt T.p (deriv T.p x) (Icc a b) x := by
    intro x hx
    exact (T.differentiable x (lt_of_lt_of_le ha0' hx.1)).hasDerivAt.hasDerivWithinAt
  obtain ⟨χ, hχ, hχd⟩ := exists_hasDerivWithinAt_eq_of_lt_of_gt hab hder ha1 hdb
  exact ⟨χ, lt_trans ha0' hχ.1, hχd⟩

/-! ### Products `w` -/

lemma w_zero (x : ℕ → ℝ) : w T x 0 = 1 := by simp [w]

lemma w_succ (x : ℕ → ℝ) (i : ℕ) : w T x (i + 1) = w T x i * T.p (x i) := by
  simp [w, Finset.prod_range_succ]

lemma w_nonneg {x : ℕ → ℝ} (hx : IsProfile x) (i : ℕ) : 0 ≤ w T x i :=
  Finset.prod_nonneg fun k _ => T.nonneg _ (hx k)

lemma w_add (x : ℕ → ℝ) (i l : ℕ) :
    w T x (i + 1 + l) = w T x (i + 1) * ∏ k ∈ Finset.range l, T.p (x (i + 1 + k)) := by
  simp [w, Finset.prod_range_add]

lemma w_const (χ : ℝ) (i : ℕ) : w T (fun _ => χ) i = T.p χ ^ i := by
  simp [w, Finset.prod_const]

/-! ### ENNReal sums -/

lemma summable_of_ofReal_ne_top {f : ℕ → ℝ} (hf : ∀ i, 0 ≤ f i)
    (h : ∑' i, ENNReal.ofReal (f i) ≠ ⊤) : Summable f := by
  have h' : ∑' i, ((f i).toNNReal : ENNReal) ≠ ⊤ := by simpa [ENNReal.ofReal] using h
  rw [ENNReal.tsum_coe_ne_top_iff_summable] at h'
  have := NNReal.summable_coe.mpr h'
  simpa [Real.coe_toNNReal _ (hf _)] using this

lemma toReal_tsum_ofReal {f : ℕ → ℝ} (hf : ∀ i, 0 ≤ f i) (hs : Summable f) :
    (∑' i, ENNReal.ofReal (f i)).toReal = ∑' i, f i := by
  rw [← ENNReal.ofReal_tsum_of_nonneg hf hs, ENNReal.toReal_ofReal (tsum_nonneg hf)]

/-! ### Step 0: finite investment implies finite length -/

lemma L_ne_top {x : ℕ → ℝ} (hx : IsProfile x) (hI : I T x ≠ ⊤) : L T x ≠ ⊤ := by
  have hg0 : ∀ i, 0 ≤ w T x i * x i := fun i => mul_nonneg (w_nonneg T hx i) (hx i)
  have hgs : Summable (fun i => w T x i * x i) := summable_of_ofReal_ne_top hg0 hI
  set J := ∑' i, w T x i * x i
  set a := T.p 1 with ha
  have ha1 : a < 1 := T.lt_one 1 zero_le_one
  have hpa : ∀ i, T.p (x i) ≤ a + x i := by
    intro i
    by_cases h : x i ≤ 1
    · have : T.p (x i) ≤ T.p 1 :=
        T.strictMono.monotoneOn (show x i ∈ Ici (0:ℝ) from hx i) (Set.mem_Ici.mpr (zero_le_one' ℝ)) h
      have := T.nonneg 1 zero_le_one
      linarith [hx i]
    · have := T.lt_one (x i) (hx i)
      have := T.nonneg 1 zero_le_one
      linarith
  have hw0 := w_nonneg T hx
  -- partial sums bound
  have key : ∀ N, (1 - a) * ∑ i ∈ Finset.range (N + 1), w T x i ≤ 1 + J := by
    intro N
    have hS : ∑ i ∈ Finset.range (N + 1), w T x i
        = 1 + ∑ i ∈ Finset.range N, w T x i * T.p (x i) := by
      rw [Finset.sum_range_succ', w_zero, add_comm]
      congr 1
      exact Finset.sum_congr rfl fun i _ => w_succ T x i
    have h1 : ∑ i ∈ Finset.range N, w T x i * T.p (x i)
        ≤ a * ∑ i ∈ Finset.range N, w T x i + ∑ i ∈ Finset.range N, w T x i * x i := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun i _ => by nlinarith [hpa i, hw0 i]
    have h2 : ∑ i ∈ Finset.range N, w T x i * x i ≤ J :=
      hgs.sum_le_tsum _ (fun i _ => hg0 i)
    have h3 : ∑ i ∈ Finset.range N, w T x i ≤ ∑ i ∈ Finset.range (N + 1), w T x i := by
      rw [Finset.sum_range_succ]; linarith [hw0 N]
    have ha0 : 0 ≤ a := T.nonneg 1 zero_le_one
    nlinarith
  have hbound : ∀ N, ∑ i ∈ Finset.range N, w T x i ≤ (1 + J) / (1 - a) := by
    intro N
    rw [le_div_iff₀ (by linarith)]
    cases N with
    | zero =>
      simp
      have : 0 ≤ J := tsum_nonneg hg0
      linarith
    | succ N => linarith [key N]
  have hs : Summable (fun i => w T x i) := summable_of_sum_range_le hw0 hbound
  unfold L
  rw [← ENNReal.ofReal_tsum_of_nonneg hw0 hs]
  exact ENNReal.ofReal_ne_top

/-! ### Gross receipts and payoffs -/

lemma gross_update (t : ℕ → ℕ → ℝ) (x : ℕ → ℝ) (i : ℕ) (y : ℝ) (hy : 0 ≤ y) :
    gross T t (Function.update x i y) i = ENNReal.ofReal (T.p y) * Estar T t x i := by
  unfold gross Estar
  rw [← ENNReal.tsum_mul_left]
  congr 1
  ext l
  rw [Finset.prod_range_succ']
  have h1 : ∀ k ∈ Finset.range l, T.p (Function.update x i y (i + (k + 1)))
      = T.p (x (i + 1 + k)) := by
    intro k _
    rw [Function.update_of_ne (by omega)]
    congr 2; omega
  rw [Finset.prod_congr rfl h1]
  simp only [add_zero, Function.update_self]
  rw [← ENNReal.ofReal_mul (T.nonneg y hy)]
  congr 1
  rw [show i + l + 1 = i + 1 + l by omega]
  ring

lemma gross_self (t : ℕ → ℕ → ℝ) {x : ℕ → ℝ} (hx : IsProfile x) (i : ℕ) :
    gross T t x i = ENNReal.ofReal (T.p (x i)) * Estar T t x i := by
  have := gross_update T t x i (x i) (hx i)
  rwa [Function.update_eq_self] at this

lemma coe_add_ofReal (a b : ℝ) (hb : 0 ≤ b) :
    ((a : EReal) + ((ENNReal.ofReal b : ENNReal) : EReal)) = ((a + b : ℝ) : EReal) := by
  rw [EReal.coe_ennreal_ofReal, max_eq_left hb, EReal.coe_add]

/-- Payoff of agent `i` after a deviation to `y`, when the conditional return is finite. -/
lemma payoff_update_fin (t : ℕ → ℕ → ℝ) (x : ℕ → ℝ) (i : ℕ) (y : ℝ) (hy : 0 ≤ y)
    (c : ℝ) (hc : 0 ≤ c) (hE : Estar T t x i = ENNReal.ofReal c) :
    payoff T t (Function.update x i y) i = ((t i i - y + T.p y * c : ℝ) : EReal) := by
  unfold payoff
  rw [gross_update T t x i y hy, hE, ← ENNReal.ofReal_mul (T.nonneg y hy)]
  simp only [Function.update_self]
  rw [coe_add_ofReal _ _ (mul_nonneg (T.nonneg y hy) hc)]

/-- First-order condition at an interior equilibrium investment. -/
lemma foc (t : ℕ → ℕ → ℝ) {x : ℕ → ℝ} (hx : IsEquilibrium T t x) (i : ℕ) (hxi : 0 < x i)
    (hE : Estar T t x i ≠ ⊤) : deriv T.p (x i) * (Estar T t x i).toReal = 1 := by
  set c := (Estar T t x i).toReal with hcdef
  have hc : 0 ≤ c := ENNReal.toReal_nonneg
  have hEc : Estar T t x i = ENNReal.ofReal c := (ENNReal.ofReal_toReal hE).symm
  have hmax : ∀ y, 0 ≤ y → T.p y * c - y ≤ T.p (x i) * c - x i := by
    intro y hy
    have h := hx.2 i y hy
    change payoff T t (Function.update x i y) i ≤ payoff T t x i at h
    rw [payoff_update_fin T t x i y hy c hc hEc] at h
    have h2 := payoff_update_fin T t x i (x i) (hx.1 i) c hc hEc
    rw [Function.update_eq_self] at h2
    rw [h2, EReal.coe_le_coe_iff] at h
    linarith
  have hlm : IsLocalMax (fun y => T.p y * c - y) (x i) := by
    filter_upwards [Ioi_mem_nhds hxi] with y hy
    exact hmax y (le_of_lt hy)
  have hd : HasDerivAt (fun y => T.p y * c - y) (deriv T.p (x i) * c - 1) (x i) :=
    ((T.differentiable (x i) hxi).hasDerivAt.mul_const c).sub (hasDerivAt_id _)
  have := hlm.hasDerivAt_eq_zero hd
  linarith

/-! ### The length identity `L = D + B` -/

/-- `D`: expected self-retained revenue. -/
noncomputable def Dsum (t : ℕ → ℕ → ℝ) (x : ℕ → ℝ) : ENNReal :=
  ∑' i, ENNReal.ofReal (w T x i * t i i)

/-- `B`: expected transfers to predecessors. -/
noncomputable def Bsum (t : ℕ → ℕ → ℝ) (x : ℕ → ℝ) : ENNReal :=
  ∑' i, ENNReal.ofReal (w T x (i + 1)) * Estar T t x i

lemma L_eq_D_add_B {t : ℕ → ℕ → ℝ} (ht : IsScheme t) {x : ℕ → ℝ} (hx : IsProfile x) :
    L T x = Dsum T t x + Bsum T t x := by
  set f : ℕ → ℕ → ENNReal := fun i m => ENNReal.ofReal (w T x m * t m i) with hf
  have hcol : ∀ m, ∑' i, f i m = ENNReal.ofReal (w T x m) := by
    intro m
    simp only [hf]
    have : ∀ i, ENNReal.ofReal (w T x m * t m i) = ENNReal.ofReal (w T x m) * ENNReal.ofReal (t m i) :=
      fun i => ENNReal.ofReal_mul (w_nonneg T hx m)
    simp_rw [this]
    rw [ENNReal.tsum_mul_left]
    have hsupp : ∀ i ∉ Finset.range (m + 1), ENNReal.ofReal (t m i) = 0 := by
      intro i hi
      rw [Finset.mem_range, not_lt] at hi
      rw [ht.2.1 m i (by omega)]; simp
    rw [tsum_eq_sum hsupp, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => (ht.1 m i).1), ht.2.2 m]
    simp
  have hrow : ∀ i, ∑' m, f i m = ENNReal.ofReal (w T x i * t i i)
      + ENNReal.ofReal (w T x (i + 1)) * Estar T t x i := by
    intro i
    rw [← (ENNReal.summable (f := fun n => f i (n + (i + 1)))).sum_add_tsum_nat_add']
    congr 1
    · rw [Finset.sum_range_succ]
      have : ∑ m ∈ Finset.range i, f i m = 0 := by
        apply Finset.sum_eq_zero
        intro m hm
        rw [Finset.mem_range] at hm
        simp [hf, ht.2.1 m i hm]
      rw [this, zero_add]
    · unfold Estar
      rw [← ENNReal.tsum_mul_left]
      congr 1
      ext l
      simp only [hf]
      rw [← ENNReal.ofReal_mul (w_nonneg T hx _), ← mul_assoc, ← w_add,
        show l + (i + 1) = i + 1 + l by omega]
  calc L T x = ∑' m, ∑' i, f i m := by unfold L; exact (tsum_congr hcol).symm
    _ = ∑' i, ∑' m, f i m := ENNReal.tsum_comm
    _ = Dsum T t x + Bsum T t x := by
      rw [tsum_congr hrow, ENNReal.tsum_add]; rfl

lemma t00 {t : ℕ → ℕ → ℝ} (ht : IsScheme t) : t 0 0 = 1 := by
  simpa using ht.2.2 0

lemma one_le_D {t : ℕ → ℕ → ℝ} (ht : IsScheme t) (x : ℕ → ℝ) : 1 ≤ Dsum T t x := by
  have := ENNReal.le_tsum (f := fun i => ENNReal.ofReal (w T x i * t i i)) 0
  simpa [Dsum, w_zero, t00 ht] using this

/-! ### Subgradient of the ratio `p / p'` at `χ` -/

lemma deriv_pos {x : ℝ} (hx : 0 < x) : 0 < deriv T.p x := by
  have h := T.strictConcave.slope_lt_deriv (Set.mem_Ici.mpr hx.le)
    (Set.mem_Ici.mpr (by linarith : (0:ℝ) ≤ x + 1)) (by linarith) (T.differentiable x hx)
  have hm : T.p x < T.p (x + 1) :=
    T.strictMono (Set.mem_Ici.mpr hx.le) (Set.mem_Ici.mpr (by linarith)) (by linarith)
  rw [slope_def_field] at h
  have : 0 < (T.p (x + 1) - T.p x) / (x + 1 - x) := div_pos (by linarith) (by linarith)
  linarith

lemma exists_subgrad {χ : ℝ} (hχ : 0 < χ) (hd : deriv T.p χ = 1) :
    ∃ s : ℝ, 1 < s ∧ ∀ y, 0 < y → T.p χ + s * (y - χ) ≤ T.p y / deriv T.p y := by
  set h : ℝ → ℝ := fun x => T.p x / deriv T.p x with hh
  have hc : ConvexOn ℝ (Ioi 0) h := T.convex_ratio
  have hint : interior (Ioi (0:ℝ)) = Ioi 0 := isOpen_Ioi.interior_eq
  have hχi : χ ∈ interior (Ioi (0:ℝ)) := by rw [hint]; exact hχ
  have hhχ : h χ = T.p χ := by simp [hh, hd]
  refine ⟨derivWithin h (Iio χ) χ, ?_, ?_⟩
  · set y := χ / 2 with hy
    have hy0 : 0 < y := by positivity
    have hyχ : y < χ := by linarith
    have h1 := hc.slope_le_leftDeriv_of_mem_interior (show y ∈ Ioi (0:ℝ) from hy0) hχi hyχ
    have h2 := T.strictConcave.deriv_lt_slope (Set.mem_Ici.mpr hy0.le)
      (Set.mem_Ici.mpr hχ.le) hyχ (T.differentiable χ hχ)
    have h3 := T.strictConcave.slope_lt_deriv (Set.mem_Ici.mpr hy0.le)
      (Set.mem_Ici.mpr hχ.le) hyχ (T.differentiable y hy0)
    rw [hd] at h2
    have hdy : 1 ≤ deriv T.p y := by linarith
    have hhy : h y ≤ T.p y := div_le_self (T.nonneg y hy0.le) hdy
    rw [slope_def_field] at h1 h2
    have hpos : 0 < χ - y := by linarith
    have : (T.p χ - T.p y) / (χ - y) ≤ (h χ - h y) / (χ - y) := by
      apply div_le_div_of_nonneg_right _ hpos.le
      rw [hhχ]; linarith
    linarith
  · intro z hz
    rcases lt_trichotomy z χ with hlt | heq | hgt
    · have h1 := hc.slope_le_leftDeriv_of_mem_interior (show z ∈ Ioi (0:ℝ) from hz) hχi hlt
      rw [slope_def_field] at h1
      have hpos : 0 < χ - z := by linarith
      rw [div_le_iff₀ hpos] at h1
      rw [← hhχ]
      change h χ + _ * (z - χ) ≤ h z
      nlinarith
    · subst heq; rw [hd]; simp
    · have h1 := hc.rightDeriv_le_slope_of_mem_interior hχi (show z ∈ Ioi (0:ℝ) from hz) hgt
      have h2 := hc.leftDeriv_le_rightDeriv_of_mem_interior hχi
      rw [slope_def_field] at h1
      have hpos : 0 < z - χ := by linarith
      rw [le_div_iff₀ hpos] at h1
      rw [← hhχ]
      change h χ + _ * (z - χ) ≤ h z
      nlinarith

/-! ### The per-agent inequality -/

lemma agent_ineq {t : ℕ → ℕ → ℝ} {x : ℕ → ℝ} (hx : IsEquilibrium T t x) (i : ℕ)
    {χ s Vs μ : ℝ} (hχ : 0 < χ) (hd : deriv T.p χ = 1)
    (hsub : ∀ y, 0 < y → T.p χ + s * (y - χ) ≤ T.p y / deriv T.p y)
    (hVs : Vs * (1 - T.p χ) = 1 - χ) (hμ : μ * (s - 1) = Vs - 1) (hVs1 : 1 < Vs) (hμ0 : 0 < μ)
    (hfin : ENNReal.ofReal (w T x (i + 1)) * Estar T t x i ≠ ⊤) :
    w T x i * (1 - x i) + w T x (i + 1) * (Vs + μ)
        - μ * (ENNReal.ofReal (w T x (i + 1)) * Estar T t x i).toReal ≤ w T x i * Vs ∧
    (0 < w T x i → w T x i * (1 - x i) + w T x (i + 1) * (Vs + μ)
        - μ * (ENNReal.ofReal (w T x (i + 1)) * Estar T t x i).toReal = w T x i * Vs →
        x i = χ) := by
  have hprof : IsProfile x := hx.1
  have hW0 := w_nonneg T hprof i
  have hsucc := w_succ T x i
  rcases hW0.eq_or_lt with hW | hW
  · have h1 : w T x (i + 1) = 0 := by rw [hsucc, ← hW, zero_mul]
    refine ⟨?_, fun h => absurd h (by rw [← hW]; exact lt_irrefl 0)⟩
    rw [h1, ← hW]; simp
  · rcases (hprof i).eq_or_lt with hx0 | hx0
    · have h1 : w T x (i + 1) = 0 := by rw [hsucc, ← hx0, T.zero, mul_zero]
      rw [h1, ← hx0]
      simp only [ENNReal.ofReal_zero, zero_mul, ENNReal.toReal_zero, mul_zero, sub_zero,
        add_zero, mul_one]
      refine ⟨by nlinarith, fun _ h => ?_⟩
      exfalso; nlinarith
    · set xi := x i with hxi
      have hp : 0 < T.p xi := p_pos T hx0
      have h1pos : 0 < w T x (i + 1) := by rw [hsucc]; exact mul_pos hW hp
      have hE : Estar T t x i ≠ ⊤ := by
        intro hE
        apply hfin
        rw [hE]
        exact ENNReal.mul_top (by simpa using h1pos)
      have hfoc := foc T t hx i hx0 hE
      set c := (Estar T t x i).toReal with hc
      have hb : (ENNReal.ofReal (w T x (i + 1)) * Estar T t x i).toReal = w T x (i + 1) * c := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal h1pos.le]
      rw [hb, hsucc]
      have hdpos := deriv_pos T hx0
      have hratio : T.p xi / deriv T.p xi = T.p xi * c := by
        field_simp
        linarith
      have hs := hsub xi hx0
      rw [hratio] at hs
      have htan := tangent_le T hχ hx0.le
      rw [hd] at htan
      set q := T.p χ
      -- per-unit quantity
      have key : 1 - xi + T.p xi * (Vs + μ) - μ * (T.p xi * c) ≤ Vs := by
        nlinarith
      have hform : w T x i * (1 - xi) + w T x i * T.p xi * (Vs + μ)
          - μ * (w T x i * T.p xi * c)
          = w T x i * (1 - xi + T.p xi * (Vs + μ) - μ * (T.p xi * c)) := by ring
      refine ⟨?_, fun _ heq => ?_⟩
      · rw [hform]; exact mul_le_mul_of_nonneg_left key hW.le
      · by_contra hne
        have hlt := tangent_lt T hχ hx0.le hne
        rw [hd] at hlt
        have key' : 1 - xi + T.p xi * (Vs + μ) - μ * (T.p xi * c) < Vs := by
          nlinarith
        rw [hform] at heq
        have := mul_lt_mul_of_pos_left key' hW
        linarith

/-! ### Summation: the main bound -/

lemma value_eq {x : ℕ → ℝ} (hI : I T x ≠ ⊤) :
    V T x = (((L T x).toReal - (I T x).toReal : ℝ) : EReal) := by
  simp [V, hI]

theorem main_bound {t : ℕ → ℕ → ℝ} (ht : IsScheme t) {x : ℕ → ℝ} (hx : IsEquilibrium T t x)
    (hI : I T x ≠ ⊤) {χ s Vs μ : ℝ} (hχ : 0 < χ) (hd : deriv T.p χ = 1)
    (hsub : ∀ y, 0 < y → T.p χ + s * (y - χ) ≤ T.p y / deriv T.p y)
    (hVs : Vs * (1 - T.p χ) = 1 - χ) (hμ : μ * (s - 1) = Vs - 1) (hVs1 : 1 < Vs) (hμ0 : 0 < μ) :
    ∃ slack : ℕ → ℝ, (∀ i, 0 ≤ slack i) ∧ Summable slack ∧
      (L T x).toReal - (I T x).toReal = Vs - ∑' i, slack i - μ * ((Dsum T t x).toReal - 1) ∧
      (∀ i, 0 < w T x i → slack i = 0 → x i = χ) ∧
      HasSum (fun i => w T x i * t i i) (Dsum T t x).toReal ∧
      (∀ i, ENNReal.ofReal (w T x (i + 1)) * Estar T t x i ≠ ⊤) ∧
      1 ≤ (Dsum T t x).toReal := by
  have hprof : IsProfile x := hx.1
  have hw0 := w_nonneg T hprof
  have hL := L_ne_top T hprof hI
  have hDB := L_eq_D_add_B T ht hprof
  have hDt : Dsum T t x ≠ ⊤ := by
    intro h; apply hL; rw [hDB, h, top_add]
  have hBt : Bsum T t x ≠ ⊤ := by
    intro h; apply hL; rw [hDB, h, add_top]
  -- summabilities
  have sw : Summable (fun i => w T x i) := summable_of_ofReal_ne_top hw0 hL
  have hg0 : ∀ i, 0 ≤ w T x i * x i := fun i => mul_nonneg (hw0 i) (hprof i)
  have sg : Summable (fun i => w T x i * x i) := summable_of_ofReal_ne_top hg0 hI
  have hd0 : ∀ i, 0 ≤ w T x i * t i i := fun i => mul_nonneg (hw0 i) (ht.1 i i).1
  have sd : Summable (fun i => w T x i * t i i) := summable_of_ofReal_ne_top hd0 hDt
  have hterm : ∀ i, ENNReal.ofReal (w T x (i + 1)) * Estar T t x i ≠ ⊤ := by
    intro i
    exact ne_top_of_le_ne_top hBt
      (ENNReal.le_tsum (f := fun i => ENNReal.ofReal (w T x (i + 1)) * Estar T t x i) i)
  set b : ℕ → ℝ := fun i => (ENNReal.ofReal (w T x (i + 1)) * Estar T t x i).toReal with hbdef
  have sb : Summable b := ENNReal.summable_toReal hBt
  have hLr : (L T x).toReal = ∑' i, w T x i := toReal_tsum_ofReal hw0 sw
  have hIr : (I T x).toReal = ∑' i, w T x i * x i := toReal_tsum_ofReal hg0 sg
  have hDr : (Dsum T t x).toReal = ∑' i, w T x i * t i i := toReal_tsum_ofReal hd0 sd
  have hBr : (Bsum T t x).toReal = ∑' i, b i := ENNReal.tsum_toReal_eq hterm
  have hLDB : (L T x).toReal = (Dsum T t x).toReal + (Bsum T t x).toReal := by
    rw [hDB, ENNReal.toReal_add hDt hBt]
  have hD1 : 1 ≤ (Dsum T t x).toReal := by
    have := one_le_D T ht x
    have := ENNReal.toReal_mono hDt this
    simpa using this
  have hshift : HasSum (fun i => w T x (i + 1)) ((L T x).toReal - 1) := by
    have := sw.hasSum
    rw [← hLr] at this
    have h2 := (hasSum_nat_add_iff' 1).mpr this
    simpa [w_zero] using h2
  -- slack
  set slack : ℕ → ℝ := fun i => w T x i * Vs - (w T x i * (1 - x i) + w T x (i + 1) * (Vs + μ)
      - μ * b i) with hsl
  have hslack_sum : HasSum slack ((L T x).toReal * Vs - ((L T x).toReal - (I T x).toReal
      + ((L T x).toReal - 1) * (Vs + μ) - μ * (Bsum T t x).toReal)) := by
    have h1 : HasSum (fun i => w T x i) (L T x).toReal := by rw [hLr]; exact sw.hasSum
    have h2 : HasSum (fun i => w T x i * x i) (I T x).toReal := by rw [hIr]; exact sg.hasSum
    have h4 : HasSum b (Bsum T t x).toReal := by rw [hBr]; exact sb.hasSum
    have h1' : HasSum (fun i => w T x i * (1 - x i)) ((L T x).toReal - (I T x).toReal) := by
      have e : (fun i => w T x i * (1 - x i)) = fun i => w T x i - w T x i * x i := by
        funext i; ring
      rw [e]; exact h1.sub h2
    exact (h1.mul_right Vs).sub ((h1'.add (hshift.mul_right (Vs + μ))).sub (h4.mul_left μ))
  refine ⟨slack, fun i => ?_, hslack_sum.summable, ?_, fun i hwi hs0 => ?_, ?_, hterm, hD1⟩
  · have := (agent_ineq T hx i hχ hd hsub hVs hμ hVs1 hμ0 (hterm i)).1
    show 0 ≤ w T x i * Vs - (w T x i * (1 - x i) + w T x (i + 1) * (Vs + μ) - μ * b i)
    linarith
  · rw [hslack_sum.tsum_eq]
    linear_combination (-μ) * hLDB
  · apply (agent_ineq T hx i hχ hd hsub hVs hμ hVs1 hμ0 (hterm i)).2 hwi
    change w T x i * Vs - (w T x i * (1 - x i) + w T x (i + 1) * (Vs + μ) - μ * b i) = 0 at hs0
    linarith
  · rw [hDr]; exact sd.hasSum

/-! ### The scheme `tStar` -/

lemma isScheme_tStar : IsScheme tStar := by
  refine ⟨fun i j => ?_, fun i j hij => ?_, fun i => ?_⟩
  · unfold tStar; split_ifs <;> norm_num
  · unfold tStar; rw [if_neg]; omega
  · rcases i with _ | m
    · simp [tStar]
    · rw [Finset.sum_eq_single m]
      · simp [tStar]
      · intro j _ hj; unfold tStar; rw [if_neg]; omega
      · intro h; simp at h

lemma Estar_tStar (x : ℕ → ℝ) (i : ℕ) : Estar T tStar x i = 1 := by
  unfold Estar
  rw [tsum_eq_single 0]
  · simp [tStar]
  · intro l hl
    unfold tStar
    rw [if_neg (by omega)]
    simp

lemma tStar_equilibrium {χ : ℝ} (hχ : 0 < χ) (hd : deriv T.p χ = 1) :
    IsEquilibrium T tStar (fun _ => χ) := by
  refine ⟨fun _ => hχ.le, fun i y hy => ?_⟩
  change payoff T tStar (Function.update (fun _ => χ) i y) i ≤ payoff T tStar (fun _ => χ) i
  have hE : Estar T tStar (fun _ => χ) i = ENNReal.ofReal 1 := by
    rw [Estar_tStar]; simp
  rw [payoff_update_fin T tStar _ i y hy 1 zero_le_one hE]
  have h2 := payoff_update_fin T tStar (fun _ => χ) i χ hχ.le 1 zero_le_one hE
  rw [Function.update_eq_self] at h2
  rw [h2, EReal.coe_le_coe_iff]
  have := tangent_le T hχ hy
  rw [hd] at this
  linarith

lemma value_const {χ : ℝ} (hχ : 0 ≤ χ) :
    V T (fun _ => χ) = (((1 - χ) / (1 - T.p χ) : ℝ) : EReal) := by
  set q := T.p χ with hq
  have hq0 : 0 ≤ q := T.nonneg χ hχ
  have hq1 : q < 1 := T.lt_one χ hχ
  have hs : Summable (fun i : ℕ => q ^ i) := summable_geometric_of_lt_one hq0 hq1
  have hL : L T (fun _ => χ) = ENNReal.ofReal ((1 - q)⁻¹) := by
    unfold L
    simp_rw [w_const]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => pow_nonneg hq0 i) hs,
      tsum_geometric_of_lt_one hq0 hq1]
  have hI : I T (fun _ => χ) = ENNReal.ofReal ((1 - q)⁻¹ * χ) := by
    unfold I
    simp_rw [w_const]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => mul_nonneg (pow_nonneg hq0 i) hχ)
      (hs.mul_right χ), tsum_mul_right, tsum_geometric_of_lt_one hq0 hq1]
  have hIt : I T (fun _ => χ) ≠ ⊤ := by rw [hI]; exact ENNReal.ofReal_ne_top
  rw [value_eq T hIt, hL, hI]
  have h1 : 0 < 1 - q := by linarith
  rw [ENNReal.toReal_ofReal (inv_nonneg.mpr h1.le),
    ENNReal.toReal_ofReal (mul_nonneg (inv_nonneg.mpr h1.le) hχ)]
  congr 1
  field_simp

/-! ### Constants `Vs`, `μ` -/

lemma constants {χ : ℝ} (hχ : 0 < χ) (hd : deriv T.p χ = 1) {s : ℝ} (hs1 : 1 < s) :
    ∃ Vs μ : ℝ, Vs = (1 - χ) / (1 - T.p χ) ∧ Vs * (1 - T.p χ) = 1 - χ ∧
      μ * (s - 1) = Vs - 1 ∧ 1 < Vs ∧ 0 < μ := by
  have hq1 : T.p χ < 1 := T.lt_one χ hχ.le
  have hqχ : χ < T.p χ := by
    have := tangent_lt T hχ (le_refl 0) (ne_of_lt hχ)
    rw [hd, T.zero] at this
    linarith
  have h1 : 0 < 1 - T.p χ := by linarith
  refine ⟨(1 - χ) / (1 - T.p χ), ((1 - χ) / (1 - T.p χ) - 1) / (s - 1), rfl, ?_, ?_, ?_, ?_⟩
  · field_simp
  · exact div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr hs1))
  · rw [lt_div_iff₀ h1]; linarith
  · apply div_pos _ (by linarith)
    rw [sub_pos, lt_div_iff₀ h1]; linarith

/-! ### Step 4 and Step 5 -/

theorem step4 : IsDecSociallyOptimal T tStar := by
  obtain ⟨χ, hχ, hd⟩ := exists_chi T
  obtain ⟨s, hs1, hsub⟩ := exists_subgrad T hχ hd
  obtain ⟨Vs, μ, hVdef, hVs, hμ, hVs1, hμ0⟩ := constants T hχ hd hs1
  refine ⟨isScheme_tStar, fun _ => χ, tStar_equilibrium T hχ hd, fun t' x' ht' hx' => ?_⟩
  rw [value_const T hχ.le, ← hVdef]
  by_cases hI : I T x' = ⊤
  · simp [V, hI]
  · obtain ⟨slack, hs0, hss, heq, -, -, -, hD1⟩ :=
      main_bound T ht' hx' hI hχ hd hsub hVs hμ hVs1 hμ0
    rw [value_eq T hI, EReal.coe_le_coe_iff, heq]
    have : 0 ≤ ∑' i, slack i := tsum_nonneg hs0
    nlinarith

theorem step5 : ∀ t, IsScheme t → IsDecSociallyOptimal T t → t = tStar := by
  intro t ht ⟨_, x, hx, hopt⟩
  obtain ⟨χ, hχ, hd⟩ := exists_chi T
  obtain ⟨s, hs1, hsub⟩ := exists_subgrad T hχ hd
  obtain ⟨Vs, μ, hVdef, hVs, hμ, hVs1, hμ0⟩ := constants T hχ hd hs1
  have hge := hopt tStar (fun _ => χ) isScheme_tStar (tStar_equilibrium T hχ hd)
  rw [value_const T hχ.le, ← hVdef] at hge
  have hI : I T x ≠ ⊤ := by
    intro h; simp [V, h] at hge
  obtain ⟨slack, hs0, hss, heq, hslack, hDsum, hterm, hD1⟩ :=
    main_bound T ht hx hI hχ hd hsub hVs hμ hVs1 hμ0
  rw [value_eq T hI, EReal.coe_le_coe_iff, heq] at hge
  have hS0 : 0 ≤ ∑' i, slack i := tsum_nonneg hs0
  have hS : ∑' i, slack i = 0 := by nlinarith
  have hDr : (Dsum T t x).toReal = 1 := by nlinarith
  have hsl0 : ∀ i, slack i = 0 := by
    have h := hss.hasSum
    rw [hS] at h
    have := (hasSum_zero_iff_of_nonneg hs0).mp h
    intro i; exact congr_fun this i
  -- all agents realized and invest `χ`
  have hall : ∀ i, 0 < w T x i ∧ x i = χ := by
    intro i
    induction i with
    | zero =>
      have h0 : 0 < w T x 0 := by rw [w_zero]; exact one_pos
      exact ⟨h0, hslack 0 h0 (hsl0 0)⟩
    | succ n ih =>
      have hw : 0 < w T x (n + 1) := by
        rw [w_succ, ih.2]; exact mul_pos ih.1 (p_pos T hχ)
      exact ⟨hw, hslack _ hw (hsl0 _)⟩
  have hxc : x = fun _ => χ := funext fun i => (hall i).2
  set q := T.p χ with hq
  have hq0 : 0 < q := p_pos T hχ
  have hwq : ∀ i, w T x i = q ^ i := by intro i; rw [hxc, w_const]
  -- diagonal transfers vanish
  have hdiag : ∀ m, t (m + 1) (m + 1) = 0 := by
    have h := hDsum
    rw [hDr] at h
    have h2 := (hasSum_nat_add_iff' 1).mpr h
    simp only [Finset.range_one, Finset.sum_singleton, w_zero, t00 ht, mul_one, sub_self] at h2
    have h3 := (hasSum_zero_iff_of_nonneg
      (fun i => mul_nonneg (w_nonneg T hx.1 _) (ht.1 _ _).1)).mp h2
    intro m
    have h4 := congr_fun h3 m
    simp only [Pi.zero_apply] at h4
    rcases mul_eq_zero.mp h4 with h5 | h5
    · exact absurd h5 (hall (m + 1)).1.ne'
    · exact h5
  -- conditional returns equal one
  have hE1 : ∀ j, Estar T t x j = 1 := by
    intro j
    have hE : Estar T t x j ≠ ⊤ := by
      intro hE
      apply hterm j
      rw [hE]
      exact ENNReal.mul_top (by simpa using (hall (j + 1)).1)
    have hf := foc T t hx j (by rw [(hall j).2]; exact hχ) hE
    rw [(hall j).2, hd, one_mul] at hf
    rw [← ENNReal.ofReal_toReal hE, hf]; simp
  have hEsum : ∀ j, ∑' l, ENNReal.ofReal (q ^ l * t (j + 1 + l) j) = 1 := by
    intro j
    have := hE1 j
    unfold Estar at this
    rw [hxc] at this
    simpa [Finset.prod_const] using this
  -- induction on the column
  have hcol : ∀ j, t (j + 1) j = 1 ∧ ∀ l, t (j + 2 + l) j = 0 := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      have hrow := ht.2.2 (j + 1)
      rw [Finset.sum_range_succ, Finset.sum_range_succ, hdiag j] at hrow
      have hz : ∑ k ∈ Finset.range j, t (j + 1) k = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        rw [Finset.mem_range] at hk
        have := (ih k hk).2 (j - 1 - k)
        rwa [show k + 2 + (j - 1 - k) = j + 1 by omega] at this
      rw [hz] at hrow
      have h1 : t (j + 1) j = 1 := by linarith
      refine ⟨h1, fun l => ?_⟩
      have hs := hEsum j
      rw [tsum_eq_zero_add' ENNReal.summable] at hs
      simp only [pow_zero, one_mul, add_zero, h1, ENNReal.ofReal_one] at hs
      have hrest : ∑' l, ENNReal.ofReal (q ^ (l + 1) * t (j + 1 + (l + 1)) j) = 0 := by
        exact (ENNReal.add_right_inj ENNReal.one_ne_top).mp (hs.trans (add_zero 1).symm)
      have h3 := (ENNReal.tsum_eq_zero.mp hrest) l
      rw [ENNReal.ofReal_eq_zero] at h3
      have h4 : 0 ≤ t (j + 1 + (l + 1)) j := (ht.1 _ _).1
      have h5 : 0 < q ^ (l + 1) := pow_pos hq0 _
      rw [show j + 2 + l = j + 1 + (l + 1) by omega]
      nlinarith
  funext i j
  rcases lt_trichotomy i j with hij | hij | hij
  · rw [ht.2.1 i j hij]; unfold tStar; rw [if_neg]; omega
  · subst hij
    rcases i with _ | m
    · rw [t00 ht]; simp [tStar]
    · rw [hdiag m]; unfold tStar; rw [if_neg]; omega
  · obtain ⟨l, rfl⟩ : ∃ l, i = j + 1 + l := ⟨i - j - 1, by omega⟩
    rcases l with _ | l
    · rw [add_zero, (hcol j).1]; simp [tStar]
    · rw [show j + 1 + (l + 1) = j + 2 + l by omega, (hcol j).2 l]
      unfold tStar; rw [if_neg]; omega

end EvolvHier.SocialOpt.EHAux

open EvolvHier.SocialOpt

theorem solution (T : Technology) : IsDecSociallyOptimal T tStar :=
  EvolvHier.SocialOpt.EHAux.step4 T
