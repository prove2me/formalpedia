-- Prove2me | solution 1 for CalibratedMA.Randomized.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @Aaron
-- created : 2026-11-13T18:40:33.669682+00:00
-- url     : https://prove2.me/submissions/2f3b0c03-6771-47bf-8080-eefa93cf3732

import Definitions.Def_CalibratedMA_Randomized_OnlineRule



namespace CalibratedMA.Randomized.OnlinePrediction

variable {X : Type*}

/-- The rule always selects a score in the unit interval, even before continuity
of the potential is assumed. -/
lemma predictFrom_mem (N : ℕ) (Φ : Finset (X → ℝ → ℝ))
    (R : (X → ℝ → ℝ) → Bool → ℝ) (x : X) :
    predictFrom N Φ R x ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  simp only [predictFrom]
  split_ifs with hz hpos
  · rcases hz with ⟨p, hp, hpzero⟩
    have hnonempty : {q ∈ Set.Icc (0 : ℝ) 1 | potential N Φ R x q = 0}.Nonempty :=
      ⟨p, hp, hpzero⟩
    have hbdd : BddBelow {q ∈ Set.Icc (0 : ℝ) 1 | potential N Φ R x q = 0} :=
      ⟨0, fun q hq => hq.1.1⟩
    exact ⟨le_csInf hnonempty (fun q hq => hq.1.1),
      (csInf_le hbdd ⟨hp, hpzero⟩).trans hp.2⟩
  · exact ⟨zero_le_one, le_refl _⟩
  · exact ⟨le_refl _, zero_le_one⟩

/-- A finite weighted sum of continuous tests is continuous on the score interval. -/
lemma continuousOn_potential (N : ℕ) (Φ : Finset (X → ℝ → ℝ))
    (R : (X → ℝ → ℝ) → Bool → ℝ) (x : X)
    (hΦ : ∀ ϕ ∈ Φ, ContinuousOn (ϕ x) (Set.Icc (0 : ℝ) 1)) :
    ContinuousOn (potential N Φ R x) (Set.Icc (0 : ℝ) 1) := by
  unfold potential
  apply continuousOn_finsetSum
  intro ϕ hϕ
  apply continuousOn_finsetSum
  intro b _
  exact continuousOn_const.mul (continuousOn_const.mul (hΦ ϕ hϕ))

/-- When a continuous function has a zero on the compact score interval, its
smallest zero lies in the interval and is itself a zero. -/
lemma sInf_zero_mem (H : ℝ → ℝ) (hH : ContinuousOn H (Set.Icc (0 : ℝ) 1))
    (hz : ∃ p ∈ Set.Icc (0 : ℝ) 1, H p = 0) :
    sInf {p ∈ Set.Icc (0 : ℝ) 1 | H p = 0} ∈ {p ∈ Set.Icc (0 : ℝ) 1 | H p = 0} := by
  have hclosed : IsClosed {p ∈ Set.Icc (0 : ℝ) 1 | H p = 0} :=
    isClosed_Icc.isClosed_eq hH continuousOn_const
  have hcompact : IsCompact {p ∈ Set.Icc (0 : ℝ) 1 | H p = 0} :=
    isCompact_Icc.of_isClosed_subset hclosed (fun _ hp => hp.1)
  exact hcompact.sInf_mem hz

/-- The chosen score makes the potential-weighted residual nonpositive for
every possible label in the unit interval. -/
lemma predictFrom_residual_nonpos (N : ℕ) (Φ : Finset (X → ℝ → ℝ))
    (R : (X → ℝ → ℝ) → Bool → ℝ) (x : X)
    (hΦ : ∀ ϕ ∈ Φ, ContinuousOn (ϕ x) (Set.Icc (0 : ℝ) 1))
    (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    (y - predictFrom N Φ R x) * potential N Φ R x (predictFrom N Φ R x) ≤ 0 := by
  classical
  have hH := continuousOn_potential N Φ R x hΦ
  simp only [predictFrom]
  split_ifs with hz hpos
  · rw [(sInf_zero_mem _ hH hz).2, mul_zero]
  · have hright : 0 ≤ potential N Φ R x 1 := by
      by_contra h
      have hnegative : potential N Φ R x 1 < 0 := lt_of_not_ge h
      obtain ⟨p, hp, hpzero⟩ :=
        intermediate_value_Icc' zero_le_one hH ⟨hnegative.le, hpos.le⟩
      exact hz ⟨p, hp, hpzero⟩
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hy.2) hright
  · simp only [sub_zero]
    exact mul_nonpos_of_nonneg_of_nonpos hy.1 (le_of_not_gt hpos)

end CalibratedMA.Randomized.OnlinePrediction


namespace CalibratedMA.Randomized.OnlinePotential

lemma exp_le_quadratic (u : ℝ) (hu : |u| ≤ 1) :
    Real.exp u ≤ 1 + u + u ^ 2 := by
  have h := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hu)).2
  linarith

lemma exp_scaled_le (η z : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hz : |z| ≤ 1) :
    Real.exp (η * z) ≤ 1 + η * z + η ^ 2 := by
  have hprod : |η * z| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hη0]
    exact (mul_le_mul_of_nonneg_left hz hη0).trans (by simpa using hη1)
  have hsq : (η * z) ^ 2 ≤ η ^ 2 := by
    rw [mul_pow]
    have hzsq : z ^ 2 ≤ 1 := by
      have h1 := (abs_le.mp hz).1
      have h2 := (abs_le.mp hz).2
      nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - z) (by linarith : 0 ≤ 1 + z)]
    simpa using mul_le_mul_of_nonneg_left hzsq (sq_nonneg η)
  exact (exp_le_quadratic (η * z) hprod).trans (by linarith)

lemma one_step {ι : Type*} (F : Finset ι) (η : ℝ) (R z : ι → ℝ)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hz : ∀ i ∈ F, |z i| ≤ 1)
    (hcancel : (∑ i ∈ F, Real.exp (η * R i) * z i) ≤ 0) :
    (∑ i ∈ F, Real.exp (η * (R i + z i))) ≤
      Real.exp (η ^ 2) * ∑ i ∈ F, Real.exp (η * R i) := by
  have hsum0 : 0 ≤ ∑ i ∈ F, Real.exp (η * R i) :=
    Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le
  have hlinear : η * (∑ i ∈ F, Real.exp (η * R i) * z i) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hη0 hcancel
  calc
    _ ≤ ∑ i ∈ F, Real.exp (η * R i) * (1 + η * z i + η ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [mul_add, Real.exp_add]
      exact mul_le_mul_of_nonneg_left (exp_scaled_le η (z i) hη0 hη1 (hz i hi))
        (Real.exp_pos _).le
    _ = (1 + η ^ 2) * (∑ i ∈ F, Real.exp (η * R i)) +
        η * (∑ i ∈ F, Real.exp (η * R i) * z i) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ (1 + η ^ 2) * ∑ i ∈ F, Real.exp (η * R i) := by linarith
    _ ≤ _ := mul_le_mul_of_nonneg_right (by simpa [add_comm] using Real.add_one_le_exp (η ^ 2)) hsum0

lemma coordinate_le_log {ι : Type*} (F : Finset ι) (η : ℝ) (R : ι → ℝ)
    (D B : ℝ) (hD : 0 < D)
    (hsum : (∑ i ∈ F, Real.exp (η * R i)) ≤ D * Real.exp B)
    (i : ι) (hi : i ∈ F) : η * R i ≤ Real.log D + B := by
  have hcoordinate : Real.exp (η * R i) ≤ ∑ j ∈ F, Real.exp (η * R j) :=
    Finset.single_le_sum (f := fun j => Real.exp (η * R j))
      (fun _ _ => (Real.exp_pos _).le) hi
  apply Real.exp_le_exp.mp
  calc
    Real.exp (η * R i) ≤ D * Real.exp B := hcoordinate.trans hsum
    _ = Real.exp (Real.log D + B) := by rw [Real.exp_add, Real.exp_log hD]

lemma iterate_le (W : ℕ → ℝ) (D a : ℝ) (N : ℕ)
    (hzero : W 0 ≤ D)
    (hstep : ∀ t < N, W (t + 1) ≤ Real.exp a * W t) :
    W N ≤ D * Real.exp ((N : ℝ) * a) := by
  induction N with
  | zero => simpa using hzero
  | succ N ih =>
    have hN := ih (fun t ht => hstep t (by omega))
    calc
      W (N + 1) ≤ Real.exp a * W N := hstep N (by omega)
      _ ≤ Real.exp a * (D * Real.exp ((N : ℝ) * a)) :=
        mul_le_mul_of_nonneg_left hN (Real.exp_pos a).le
      _ = D * Real.exp (((N + 1 : ℕ) : ℝ) * a) := by
        rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, Real.exp_add]
        ring

end CalibratedMA.Randomized.OnlinePotential


namespace CalibratedMA.Randomized.OnlineState

variable {X : Type*}

/-- The residual state at round `t` only uses examples from earlier rounds. -/
lemma residSums_history (N : ℕ) (Φ : Finset (X → ℝ → ℝ))
    (z z' : Fin N → X × ℝ) (t : ℕ)
    (hz : ∀ s : Fin N, (s : ℕ) < t → z s = z' s) :
    residSums N Φ z t = residSums N Φ z' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      have hh := ih (fun s hs => hz s (by omega))
      simp only [residSums]
      rw [hh]
      split_ifs with ht
      · rw [hz ⟨t, ht⟩ (by simp)]
      · rfl

/-- The online prediction rule has the history-dependence property in Lemma 3.1. -/
lemma onlineRule_history (N : ℕ) (Φ : Finset (X → ℝ → ℝ))
    (z z' : Fin N → X × ℝ) (t : ℕ)
    (hz : ∀ s : Fin N, (s : ℕ) < t → z s = z' s) :
    onlineRule N Φ z t = onlineRule N Φ z' t := by
  unfold onlineRule
  rw [residSums_history N Φ z z' t hz]

/-- Expand the recursive residual state as a sum of the increments already observed. -/
lemma residSums_eq_sum_range (N : ℕ) (Φ : Finset (X → ℝ → ℝ))
    (z : Fin N → X × ℝ) (t : ℕ) (ϕ : X → ℝ → ℝ) (b : Bool) :
    residSums N Φ z t ϕ b =
      ∑ j ∈ Finset.range t, if hj : j < N then
        sgnB b * ϕ (z ⟨j, hj⟩).1 (onlineScore N Φ z ⟨j, hj⟩) *
          ((z ⟨j, hj⟩).2 - onlineScore N Φ z ⟨j, hj⟩) else 0 := by
  induction t with
  | zero => simp [residSums]
  | succ t ih =>
      rw [Finset.sum_range_succ, ← ih]
      by_cases ht : t < N
      · simp only [residSums, ht, dif_pos, onlineScore, onlineRule]
      · simp only [residSums, dif_neg ht, add_zero]

/-- The terminal state is precisely the signed cumulative empirical residual. -/
lemma residSums_terminal (N : ℕ) (Φ : Finset (X → ℝ → ℝ))
    (z : Fin N → X × ℝ) (ϕ : X → ℝ → ℝ) (b : Bool) :
    residSums N Φ z N ϕ b =
      ∑ t : Fin N, sgnB b * ϕ (z t).1 (onlineScore N Φ z t) *
        ((z t).2 - onlineScore N Φ z t) := by
  rw [residSums_eq_sum_range, Finset.sum_range]
  apply Finset.sum_congr rfl
  intro t ht
  simp only [t.isLt, dif_pos]

@[simp] lemma abs_sgnB (b : Bool) : |sgnB b| = 1 := by
  cases b <;> norm_num [sgnB]

/-- The negative test tracks the negative of the positive test's residual. -/
lemma residSums_false_eq_neg_true (N : ℕ) (Φ : Finset (X → ℝ → ℝ))
    (z : Fin N → X × ℝ) (t : ℕ) (ϕ : X → ℝ → ℝ) :
    residSums N Φ z t ϕ false = -residSums N Φ z t ϕ true := by
  rw [residSums_eq_sum_range, residSums_eq_sum_range, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> simp [sgnB]

/-- A bounded test and bounded label/prediction give an increment of magnitude at most one. -/
lemma abs_increment_le_one (ϕ : X → ℝ → ℝ) (x : X) (y s : ℝ) (b : Bool)
    (hϕ : ϕ x s ∈ Set.Icc (-1 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    |sgnB b * ϕ x s * (y - s)| ≤ 1 := by
  have ht : |ϕ x s| ≤ 1 := abs_le.mpr hϕ
  have hr : |y - s| ≤ 1 :=
    abs_le.mpr ⟨by linarith [hy.1, hs.2], by linarith [hy.2, hs.1]⟩
  rw [abs_mul, abs_mul, abs_sgnB, one_mul]
  calc
    |ϕ x s| * |y - s| ≤ 1 * |y - s| := mul_le_mul_of_nonneg_right ht (abs_nonneg _)
    _ ≤ 1 := by simpa only [one_mul] using hr

/-- The crude terminal bound used when the learning rate is capped at one. -/
lemma abs_residSums_terminal_le (N : ℕ) (Φ : Finset (X → ℝ → ℝ))
    (z : Fin N → X × ℝ) (ϕ : X → ℝ → ℝ) (b : Bool)
    (hϕ : ∀ x, ∀ s ∈ Set.Icc (0 : ℝ) 1, ϕ x s ∈ Set.Icc (-1 : ℝ) 1)
    (hz : ∀ t, (z t).2 ∈ Set.Icc (0 : ℝ) 1)
    (hs : ∀ t, onlineScore N Φ z t ∈ Set.Icc (0 : ℝ) 1) :
    |residSums N Φ z N ϕ b| ≤ N := by
  rw [residSums_terminal]
  calc
    |∑ t : Fin N, sgnB b * ϕ (z t).1 (onlineScore N Φ z t) *
        ((z t).2 - onlineScore N Φ z t)| ≤
      ∑ t : Fin N, |sgnB b * ϕ (z t).1 (onlineScore N Φ z t) *
        ((z t).2 - onlineScore N Φ z t)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t : Fin N, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro t ht
      exact abs_increment_le_one ϕ (z t).1 (z t).2 (onlineScore N Φ z t) b
        (hϕ _ _ (hs t)) (hz t) (hs t)
    _ = N := by simp

end CalibratedMA.Randomized.OnlineState


namespace CalibratedMA.Randomized.OnlineNumerics

variable {X : Type*}

lemma eta_nonneg (N : ℕ) (Φ : Finset (X → ℝ → ℝ)) : 0 ≤ eta N Φ :=
  le_min (by norm_num) (Real.sqrt_nonneg _)

lemma eta_le_one (N : ℕ) (Φ : Finset (X → ℝ → ℝ)) : eta N Φ ≤ 1 :=
  min_le_left _ _

lemma log_tests_pos (Φ : Finset (X → ℝ → ℝ)) (hΦ : Φ.Nonempty) :
    0 < Real.log (2 * (Φ.card : ℝ)) := by
  apply Real.log_pos
  have hcardNat : 1 ≤ Φ.card := Finset.card_pos.mpr hΦ
  have hcard : (1 : ℝ) ≤ Φ.card := by exact_mod_cast hcardNat
  linarith

lemma eta_pos (N : ℕ) (Φ : Finset (X → ℝ → ℝ)) (hN : 1 ≤ N) (hΦ : Φ.Nonempty) :
    0 < eta N Φ := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  exact lt_min (by norm_num) (Real.sqrt_pos.mpr (div_pos (log_tests_pos Φ hΦ) hNpos))

/-- Normalizing the usual exponential-potential estimate with the capped square-root
learning rate gives a residual bound with universal constant two. -/
lemma normalized_residual_le (n ℓ r : ℝ) (hn : 0 < n) (hℓ : 0 < ℓ)
    (hcap : r ≤ n)
    (hpotential : min 1 (Real.sqrt (ℓ / n)) * r ≤
      ℓ + n * (min 1 (Real.sqrt (ℓ / n))) ^ 2) :
    r / n ≤ 2 * Real.sqrt (ℓ / n) := by
  let s := Real.sqrt (ℓ / n)
  have hspos : 0 < s := Real.sqrt_pos.mpr (div_pos hℓ hn)
  have hsnonneg : 0 ≤ s := hspos.le
  have hsq : n * s ^ 2 = ℓ := by
    dsimp only [s]
    rw [Real.sq_sqrt (div_nonneg hℓ.le hn.le)]
    field_simp
  change min 1 s * r ≤ ℓ + n * (min 1 s) ^ 2 at hpotential
  change r / n ≤ 2 * s
  by_cases hs : s ≤ 1
  · rw [min_eq_right hs] at hpotential
    have hscaled : s * r ≤ s * (2 * n * s) := by nlinarith [hpotential, hsq]
    have hr : r ≤ 2 * n * s := le_of_mul_le_mul_left hscaled hspos
    apply (div_le_iff₀ hn).2
    nlinarith [hr]
  · have hsone : 1 ≤ s := (lt_of_not_ge hs).le
    have hrone : r / n ≤ 1 := (div_le_one hn).mpr hcap
    linarith

/-- Signed potential estimates give the corresponding estimate on the absolute residual. -/
lemma abs_potential_le (η r B : ℝ) (hplus : η * r ≤ B) (hminus : η * (-r) ≤ B) :
    η * |r| ≤ B := by
  by_cases hr : 0 ≤ r
  · simpa only [abs_of_nonneg hr] using hplus
  · simpa only [abs_of_neg (lt_of_not_ge hr)] using hminus

/-- The normalized absolute residual estimate for the mission's learning rate. -/
lemma abs_normalized_residual_le (N : ℕ) (Φ : Finset (X → ℝ → ℝ))
    (hN : 1 ≤ N) (hΦ : Φ.Nonempty) (r : ℝ)
    (hcap : |r| ≤ N)
    (hpotential : eta N Φ * |r| ≤
      Real.log (2 * (Φ.card : ℝ)) + N * (eta N Φ) ^ 2) :
    |(1 / (N : ℝ)) * r| ≤ 2 * Real.sqrt (Real.log (2 * (Φ.card : ℝ)) / N) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h := normalized_residual_le (N : ℝ) (Real.log (2 * (Φ.card : ℝ))) |r|
    hNpos (log_tests_pos Φ hΦ) hcap hpotential
  rw [abs_mul, abs_of_pos (one_div_pos.mpr hNpos)]
  simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using h

/-- Version directly accepting both signed exponential-potential estimates. -/
lemma abs_normalized_residual_le_of_signed (N : ℕ) (Φ : Finset (X → ℝ → ℝ))
    (hN : 1 ≤ N) (hΦ : Φ.Nonempty) (r : ℝ)
    (hcap : |r| ≤ N)
    (hplus : eta N Φ * r ≤
      Real.log (2 * (Φ.card : ℝ)) + N * (eta N Φ) ^ 2)
    (hminus : eta N Φ * (-r) ≤
      Real.log (2 * (Φ.card : ℝ)) + N * (eta N Φ) ^ 2) :
    |(1 / (N : ℝ)) * r| ≤ 2 * Real.sqrt (Real.log (2 * (Φ.card : ℝ)) / N) :=
  abs_normalized_residual_le N Φ hN hΦ r hcap
    (abs_potential_le (eta N Φ) r _ hplus hminus)

end CalibratedMA.Randomized.OnlineNumerics


namespace CalibratedMA.Randomized.OnlineAnalysis

variable {X : Type*}

noncomputable def weights (N : ℕ) (Φ : Finset (X → ℝ → ℝ))
    (R : (X → ℝ → ℝ) → Bool → ℝ) : ℝ :=
  ∑ ϕ ∈ Φ, ∑ b : Bool, Real.exp (eta N Φ * R ϕ b)

lemma residual_abs_le (ϕ : X → ℝ → ℝ) (x : X) (s y : ℝ) (b : Bool)
    (hϕ : ϕ x s ∈ Set.Icc (-1 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) : |sgnB b * ϕ x s * (y - s)| ≤ 1 := by
  have hsgn : |sgnB b| = 1 := by cases b <;> norm_num [sgnB]
  have hdiff : |y - s| ≤ 1 := abs_le.mpr ⟨by linarith [hy.1, hs.2], by linarith [hy.2, hs.1]⟩
  rw [abs_mul, abs_mul, hsgn, one_mul]
  simpa only [one_mul] using mul_le_mul (abs_le.mpr hϕ) hdiff
    (abs_nonneg (y - s)) (by norm_num : (0 : ℝ) ≤ 1)

lemma weights_step (N : ℕ) (Φ : Finset (X → ℝ → ℝ))
    (hcont : ∀ ϕ ∈ Φ, ∀ x, ContinuousOn (ϕ x) (Set.Icc (0 : ℝ) 1))
    (hbound : ∀ ϕ ∈ Φ, ∀ x, ∀ p ∈ Set.Icc (0 : ℝ) 1, ϕ x p ∈ Set.Icc (-1 : ℝ) 1)
    (R : (X → ℝ → ℝ) → Bool → ℝ) (x : X) (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    weights N Φ (fun ϕ b => R ϕ b + sgnB b * ϕ x (predictFrom N Φ R x) *
      (y - predictFrom N Φ R x)) ≤ Real.exp ((eta N Φ) ^ 2) * weights N Φ R := by
  classical
  let F := Φ ×ˢ (Finset.univ : Finset Bool)
  let z : (X → ℝ → ℝ) × Bool → ℝ := fun i =>
    sgnB i.2 * i.1 x (predictFrom N Φ R x) * (y - predictFrom N Φ R x)
  have hs := OnlinePrediction.predictFrom_mem N Φ R x
  have hz : ∀ i ∈ F, |z i| ≤ 1 := by
    rintro ⟨ϕ,b⟩ hi
    have hϕ : ϕ ∈ Φ := (Finset.mem_product.mp hi).1
    exact residual_abs_le ϕ x _ y b (hbound ϕ hϕ x _ hs) hs hy
  have hcancel : (∑ i ∈ F, Real.exp (eta N Φ * R i.1 i.2) * z i) ≤ 0 := by
    have heq : (∑ i ∈ F, Real.exp (eta N Φ * R i.1 i.2) * z i) =
        (y - predictFrom N Φ R x) * potential N Φ R x (predictFrom N Φ R x) := by
      simp only [F, Finset.sum_product, z, potential, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ϕ hϕ
      apply Finset.sum_congr rfl
      intro b hb
      ring
    rw [heq]
    exact OnlinePrediction.predictFrom_residual_nonpos N Φ R x (fun ϕ hϕ => hcont ϕ hϕ x) y hy
  have hη0 : 0 ≤ eta N Φ := le_min (by norm_num) (Real.sqrt_nonneg _)
  have hη1 : eta N Φ ≤ 1 := min_le_left _ _
  have hstep := OnlinePotential.one_step F (eta N Φ) (fun i => R i.1 i.2) z hη0 hη1 hz hcancel
  simpa only [F, Finset.sum_product, weights, z] using hstep

lemma weights_bound (N : ℕ) (Φ : Finset (X → ℝ → ℝ))
    (hcont : ∀ ϕ ∈ Φ, ∀ x, ContinuousOn (ϕ x) (Set.Icc (0 : ℝ) 1))
    (hbound : ∀ ϕ ∈ Φ, ∀ x, ∀ p ∈ Set.Icc (0 : ℝ) 1, ϕ x p ∈ Set.Icc (-1 : ℝ) 1)
    (z : Fin N → X × ℝ) (hz : ∀ t, (z t).2 ∈ Set.Icc (0 : ℝ) 1)
    (t : ℕ) (ht : t ≤ N) :
    weights N Φ (residSums N Φ z t) ≤
      (2 * (Φ.card : ℝ)) * Real.exp ((t : ℝ) * (eta N Φ) ^ 2) := by
  induction t with
  | zero => simp [weights, residSums, mul_comm]
  | succ t ih =>
    have htN : t < N := by omega
    have hstep := weights_step N Φ hcont hbound (residSums N Φ z t)
      (z ⟨t,htN⟩).1 (z ⟨t,htN⟩).2 (hz ⟨t,htN⟩)
    have hrec : weights N Φ (residSums N Φ z (t + 1)) ≤
        Real.exp ((eta N Φ)^2) * weights N Φ (residSums N Φ z t) := by
      simpa only [residSums, dif_pos htN] using hstep
    calc
      _ ≤ _ := hrec
      _ ≤ Real.exp ((eta N Φ)^2) *
          ((2 * (Φ.card : ℝ)) * Real.exp ((t : ℝ) * (eta N Φ)^2)) :=
        mul_le_mul_of_nonneg_left (ih (by omega)) (Real.exp_pos _).le
      _ = _ := by rw [mul_left_comm, ← Real.exp_add]; congr 2; push_cast; ring

end CalibratedMA.Randomized.OnlineAnalysis


universe u
open CalibratedMA.Randomized

theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X : Type u) (N : ℕ) (Φ : Finset (X → ℝ → ℝ)), 1 ≤ N → Φ.Nonempty →
        (∀ ϕ ∈ Φ, ∀ x, ContinuousOn (ϕ x) (Set.Icc (0 : ℝ) 1)) →
        (∀ ϕ ∈ Φ, ∀ x, ∀ p ∈ Set.Icc (0 : ℝ) 1, ϕ x p ∈ Set.Icc (-1 : ℝ) 1) →
        (∀ (z z' : Fin N → X × ℝ) (t : ℕ), (∀ s : Fin N, (s : ℕ) < t → z s = z' s) →
            onlineRule N Φ z t = onlineRule N Φ z' t) ∧
        (∀ (z : Fin N → X × ℝ) (t : ℕ) (x : X), onlineRule N Φ z t x ∈ Set.Icc (0 : ℝ) 1) ∧
        ∀ z : Fin N → X × ℝ, (∀ t, (z t).2 ∈ Set.Icc (0 : ℝ) 1) →
          ∀ ϕ ∈ Φ,
            |(1 / (N : ℝ)) * ∑ t : Fin N,
                ϕ (z t).1 (onlineScore N Φ z t) * ((z t).2 - onlineScore N Φ z t)| ≤
              C * Real.sqrt (Real.log (2 * (Φ.card : ℝ)) / N)  := by
  refine ⟨2, by norm_num, ?_⟩
  intro X N Φ hN hΦ hcont hbound
  refine ⟨?_, ?_, ?_⟩
  · intro z z' t hz
    exact OnlineState.onlineRule_history N Φ z z' t hz
  · intro z t x
    exact OnlinePrediction.predictFrom_mem N Φ (residSums N Φ z t) x
  · intro z hz ϕ hϕ
    classical
    have hsum := OnlineAnalysis.weights_bound N Φ hcont hbound z hz N (le_refl N)
    have hcard : (0 : ℝ) < Φ.card := by exact_mod_cast (Finset.card_pos.mpr hΦ)
    have hD : (0 : ℝ) < 2 * (Φ.card : ℝ) := by positivity
    have hcoord (b : Bool) : eta N Φ * residSums N Φ z N ϕ b ≤
        Real.log (2 * (Φ.card : ℝ)) + N * (eta N Φ)^2 := by
      refine OnlinePotential.coordinate_le_log (Φ ×ˢ (Finset.univ : Finset Bool))
        (eta N Φ) (fun i => residSums N Φ z N i.1 i.2)
        (2 * (Φ.card : ℝ)) ((N : ℝ) * (eta N Φ)^2) hD ?_ (ϕ, b) ?_
      · simpa only [Finset.sum_product, OnlineAnalysis.weights] using hsum
      · exact Finset.mem_product.mpr ⟨hϕ, Finset.mem_univ b⟩
    have hs : ∀ t, onlineScore N Φ z t ∈ Set.Icc (0 : ℝ) 1 := by
      intro t
      exact OnlinePrediction.predictFrom_mem N Φ (residSums N Φ z t) (z t).1
    have hcap := OnlineState.abs_residSums_terminal_le N Φ z ϕ true (hbound ϕ hϕ) hz hs
    have hminus : eta N Φ * (-residSums N Φ z N ϕ true) ≤
        Real.log (2 * (Φ.card : ℝ)) + N * (eta N Φ)^2 := by
      rw [← OnlineState.residSums_false_eq_neg_true]
      exact hcoord false
    have hfinal := OnlineNumerics.abs_normalized_residual_le_of_signed N Φ hN hΦ
      (residSums N Φ z N ϕ true) hcap (hcoord true) hminus
    simpa only [OnlineState.residSums_terminal, sgnB, if_true, one_mul] using hfinal

