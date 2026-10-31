-- Prove2me | solution 1 for FBMSP.corollary2_moment_bound
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T12:36:05.5655+00:00
-- url     : https://prove2.me/submissions/2fe351eb-3117-46a5-9faa-c5b0e5e6fb09

import Theorems.Thm_FBMSP_theorem3_model_market_comparison

open MeasureTheory Set FBMSP
open scoped BigOperators

private lemma m2_menu_nonneg (η : Measure ℝ) (x : ℝ) (P : Finset ℝ) :
    0 ≤ menuAt η x P := by
  classical
  unfold menuAt
  split_ifs <;> simp_all only [le_max_iff, le_refl, true_or]


private lemma m2_menu_le (η : Measure ℝ) (x : ℝ) (P : Finset ℝ) (b : ℝ)
    (hb : 0 ≤ b) (h : ∀ p ∈ P, postedRevenue η x p ≤ b) : menuAt η x P ≤ b := by
  classical
  unfold menuAt
  split_ifs with hP
  · exact max_le hb (Finset.sup'_le _ _ h)
  · exact hb


private lemma m2_le_menu (η : Measure ℝ) (x : ℝ) (P : Finset ℝ) (p : ℝ)
    (hp : p ∈ P) : postedRevenue η x p ≤ menuAt η x P := by
  classical
  have hP : P.Nonempty := ⟨p, hp⟩
  rw [menuAt, dif_pos hP]
  exact (Finset.le_sup' (fun q => postedRevenue η x q) hp).trans (le_max_right _ _)


private lemma m2_menu_mono (η : Measure ℝ) (x : ℝ) : Monotone (menuAt η x) := by
  intro A B hAB
  exact m2_menu_le η x A _ (m2_menu_nonneg η x B) (fun p hp => m2_le_menu η x B p (hAB hp))


private lemma m2_menu_insert (η : Measure ℝ) (x p : ℝ) (P : Finset ℝ) :
    menuAt η x (insert p P) = max (menuAt η x P) (postedRevenue η x p) := by
  classical
  apply le_antisymm
  · apply m2_menu_le η x _ _ ((m2_menu_nonneg η x P).trans (le_max_left _ _))
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact le_max_right _ _
    · exact (m2_le_menu η x P q hq).trans (le_max_left _ _)
  · exact max_le (m2_menu_mono η x (Finset.subset_insert p P))
      (m2_le_menu η x _ p (Finset.mem_insert_self p P))


private lemma m2_posted_integrable (ν η : Measure ℝ)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure η] (p : ℝ) :
    Integrable (fun x => postedRevenue η x p) ν := by
  have hs : Antitone (survival η) := by
    intro a b hab
    exact ENNReal.toReal_mono (measure_ne_top η (Ici a))
      (measure_mono (Ici_subset_Ici.mpr hab))
  have hm : Measurable (fun x => postedRevenue η x p) :=
    measurable_const.mul (hs.measurable.comp (measurable_const.sub measurable_id))
  apply (integrable_const (|p| : ℝ)).mono' hm.aestronglyMeasurable
  filter_upwards [] with x
  have hS : survival η (p - x) ≤ 1 := measureReal_le_one
  have hS0 : 0 ≤ survival η (p - x) := ENNReal.toReal_nonneg
  simp only [postedRevenue, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg hS0]
  simpa using mul_le_mul_of_nonneg_left hS (abs_nonneg p)


private lemma m2_menu_integrable (ν η : Measure ℝ)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure η] (P : Finset ℝ) :
    Integrable (fun x => menuAt η x P) ν := by
  classical
  induction P using Finset.induction_on with
  | empty => simpa [menuAt] using (integrable_const (0 : ℝ) : Integrable (fun _ : ℝ => 0) ν)
  | @insert p P hp ih =>
    simpa only [m2_menu_insert, Pi.sup_def] using
      ih.sup (m2_posted_integrable ν η p)


private lemma m2_posted_dirac (x p : ℝ) :
    postedRevenue (Measure.dirac 0) x p = if p ≤ x then p else 0 := by
  by_cases hpx : p ≤ x
  · simp [postedRevenue, survival, Measure.dirac_apply', hpx, sub_nonpos.mpr hpx]
  · have hh : ¬ p - x ≤ 0 := by linarith
    simp [postedRevenue, survival, Measure.dirac_apply', hpx, hh]

private lemma m2_model_menu_le_mean (ν : Measure ℝ) (hν : ValidPredictions ν)
    (P : Finset ℝ) : menuRevenue ν (Measure.dirac 0) P ≤ predictionMean ν := by
  letI : IsProbabilityMeasure ν := hν.1
  apply integral_mono_ae (m2_menu_integrable ν (Measure.dirac 0) P) hν.2.1
  filter_upwards [hν.2.2] with x hx
  apply m2_menu_le _ _ _ _ hx
  intro p hp
  rw [m2_posted_dirac]
  split_ifs with hpx
  · exact hpx
  · exact hx

private lemma m2_model_bdd (ν : Measure ℝ) (hν : ValidPredictions ν) (k : ℕ) :
    BddAbove {r : ℝ | ∃ P : Finset ℝ, FeasibleMenu P k ∧
      r = menuRevenue ν (Measure.dirac 0) P} := by
  refine ⟨predictionMean ν, ?_⟩
  rintro r ⟨P, hP, rfl⟩
  exact m2_model_menu_le_mean ν hν P

private lemma m2_centered_sq_integrable (ν : Measure ℝ) (hν : ValidPredictions ν)
    (hMoment : Integrable (fun x : ℝ => x ^ 2) ν) (m : ℝ) :
    Integrable (fun x : ℝ => (x - m) ^ 2) ν := by
  letI : IsProbabilityMeasure ν := hν.1
  have h : Integrable (fun x : ℝ => x ^ 2 - (2 * m) * x + m ^ 2) ν :=
    (hMoment.sub (hν.2.1.const_mul (2 * m))).add (integrable_const (m ^ 2))
  exact h.congr (Filter.Eventually.of_forall (fun x => by ring))

/-- The first absolute centered moment is bounded by the standard deviation. -/
private lemma m2_abs_integral_le (ν : Measure ℝ) (hν : ValidPredictions ν)
    (hMoment : Integrable (fun x : ℝ => x ^ 2) ν)
    (σ : ℝ) (hσ : 0 ≤ σ) (hVar : predictionVariance ν = σ ^ 2) :
    (∫ x, |x - predictionMean ν| ∂ν) ≤ σ := by
  letI : IsProbabilityMeasure ν := hν.1
  let m := predictionMean ν
  let a := ∫ x, |x - m| ∂ν
  have habs : Integrable (fun x : ℝ => |x - m|) ν :=
    (hν.2.1.sub (integrable_const m)).abs
  have hsq := m2_centered_sq_integrable ν hν hMoment m
  have hdiff : Integrable (fun x : ℝ => (x - m) ^ 2 - (2 * a) * |x - m|) ν :=
    hsq.sub (habs.const_mul (2 * a))
  have hnonneg : 0 ≤ ∫ x, (|x - m| - a) ^ 2 ∂ν :=
    integral_nonneg (fun x => sq_nonneg _)
  have heq : (∫ x, (|x - m| - a) ^ 2 ∂ν) =
      (∫ x, (x - m) ^ 2 ∂ν) - 2 * a * a + a ^ 2 := by
    calc
      (∫ x, (|x - m| - a) ^ 2 ∂ν) =
          ∫ x, ((x - m) ^ 2 - (2 * a) * |x - m|) + a ^ 2 ∂ν := by
            apply integral_congr_ae
            filter_upwards [] with x
            nlinarith only [sq_abs (x - m)]
      _ = (∫ x, (x - m) ^ 2 ∂ν) - 2 * a * a + a ^ 2 := by
        rw [integral_add hdiff (integrable_const (a ^ 2)),
          integral_sub hsq (habs.const_mul (2 * a)), integral_const_mul]
        simp [a]
  have hv : (∫ x, (x - m) ^ 2 ∂ν) = σ ^ 2 := hVar
  rw [heq, hv] at hnonneg
  have ha : 0 ≤ a := integral_nonneg (fun x => abs_nonneg _)
  change a ≤ σ
  nlinarith

private lemma m2_optimize (B K D : ℝ) (hB : 0 ≤ B) (hK : 0 < K)
    (h : ∀ t : ℝ, 0 < t → D ≤ 2 * t / K + B / t) :
    D ≤ 2 * Real.sqrt (2 * B / K) := by
  by_cases hB0 : B = 0
  · simp only [hB0, mul_zero, zero_div, Real.sqrt_zero] at h ⊢
    apply le_of_forall_pos_le_add
    intro ε hε
    have ht : 0 < K * ε / 2 := by positivity
    have hstep := h (K * ε / 2) ht
    have heq : 2 * (K * ε / 2) / K = ε := by field_simp [ne_of_gt hK]
    rw [heq] at hstep
    simpa using hstep
  have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
  let s := Real.sqrt (2 * B / K)
  have hs : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hs2 : s ^ 2 = 2 * B / K := Real.sq_sqrt (by positivity)
  let t := K * s / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have hfirst : 2 * t / K = s := by dsimp [t]; field_simp [ne_of_gt hK]
  have hsecond : B / t = s := by
    apply (div_eq_iff (ne_of_gt ht)).mpr
    have hh := (eq_div_iff (ne_of_gt hK)).mp hs2
    dsimp [t]
    nlinarith
  have hstep := h t ht
  rw [hfirst, hsecond] at hstep
  dsimp [s] at hstep
  linarith


private lemma m2_grid_cover {k : ℕ} (hk : 1 ≤ k) (L U x : ℝ)
    (hx : x ∈ Icc L U) :
    ∃ j : Fin k,
      L + (j.val : ℝ) * ((U - L) / (k : ℝ)) ≤ x ∧
      x ≤ L + ((j.val : ℝ) + 1) * ((U - L) / (k : ℝ)) := by
  classical
  cases k with
  | zero => omega
  | succ k =>
      let δ : ℝ := (U - L) / ((k + 1 : ℕ) : ℝ)
      have hkne : (k : ℝ) + 1 ≠ 0 := by positivity
      have hspan : ((k : ℝ) + 1) * δ = U - L := by
        dsimp [δ]
        push_cast
        field_simp [hkne]
      let S : Finset (Fin (k + 1)) :=
        Finset.univ.filter (fun j => L + (j.val : ℝ) * δ ≤ x)
      have hS : S.Nonempty := by
        refine ⟨0, ?_⟩
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and,
          Fin.val_zero, Nat.cast_zero, zero_mul, add_zero]
        exact hx.1
      let j : Fin (k + 1) := S.max' hS
      have hjlower : L + (j.val : ℝ) * δ ≤ x :=
        (Finset.mem_filter.mp (Finset.max'_mem S hS)).2
      refine ⟨j, hjlower, ?_⟩
      change x ≤ L + ((j.val : ℝ) + 1) * δ
      by_cases hjlast : j = Fin.last k
      · rw [hjlast]
        simp only [Fin.val_last]
        linarith [hx.2]
      · have hjne : j.val ≠ k := by
          intro heq
          exact hjlast (Fin.ext heq)
        have hjlt : j.val + 1 < k + 1 := by have := j.isLt; omega
        let l : Fin (k + 1) := ⟨j.val + 1, hjlt⟩
        by_contra hbad
        have hlmem : l ∈ S := by
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and,
            l, Nat.cast_add, Nat.cast_one]
          exact le_of_lt (lt_of_not_ge hbad)
        have hmax : l ≤ j := Finset.le_max' S l hlmem
        change j.val + 1 ≤ j.val at hmax
        omega

private lemma m2_grid_menu (L U : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    ∃ P : Finset ℝ, FeasibleMenu P k ∧
      ∀ x : ℝ, 0 ≤ x → x ∈ Icc L U →
        x - menuAt (Measure.dirac 0) x P ≤ (U - L) / (k : ℝ) := by
  classical
  let δ : ℝ := (U - L) / (k : ℝ)
  let price : Fin k → ℝ := fun j => max (L + (j.val : ℝ) * δ) 0
  let P : Finset ℝ := Finset.univ.image price
  refine ⟨P, ⟨?_, ?_⟩, ?_⟩
  · exact Finset.card_image_le.trans (by simp)
  · intro p hp
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hp
    exact le_max_right _ _
  · intro x hx hRange
    obtain ⟨j, hjlo, hjhi⟩ := m2_grid_cover hk L U x hRange
    have hpjx : price j ≤ x := max_le hjlo hx
    have hgap : x - price j ≤ δ := by
      have hmax : L + (j.val : ℝ) * δ ≤ price j := le_max_left _ _
      change x ≤ L + ((j.val : ℝ) + 1) * δ at hjhi
      nlinarith
    have hmem : price j ∈ P := Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
    have hrev := m2_le_menu (Measure.dirac 0) x P (price j) hmem
    rw [m2_posted_dirac, if_pos hpjx] at hrev
    change x - menuAt (Measure.dirac 0) x P ≤ δ
    linarith

private lemma m2_model_parametric (ν : Measure ℝ) (hν : ValidPredictions ν)
    (hMoment : Integrable (fun x : ℝ => x ^ 2) ν)
    (σ : ℝ) (hσ : 0 ≤ σ) (hVar : predictionVariance ν = σ ^ 2)
    (k : ℕ) (hk : 1 ≤ k) (t : ℝ) (ht : 0 < t) :
    predictionMean ν - modelRevenue ν k ≤
      2 * t / (k : ℝ) + σ * (predictionMean ν + σ) / t := by
  letI : IsProbabilityMeasure ν := hν.1
  let m := predictionMean ν
  let δ := 2 * t / (k : ℝ)
  let pen : ℝ → ℝ := fun x => (m * |x - m| + (x - m) ^ 2) / t
  have hm : 0 ≤ m := integral_nonneg_of_ae hν.2.2
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hwidth : ((m + t) - (m - t)) / (k : ℝ) = δ := by dsimp [δ]; ring
  obtain ⟨P, hP, happrox⟩ := m2_grid_menu (m - t) (m + t) k hk
  have hpoint : ∀ᵐ x ∂ν,
      x ≤ menuAt (Measure.dirac 0) x P + δ + pen x := by
    filter_upwards [hν.2.2] with x hx
    have hpennonneg : 0 ≤ pen x := by dsimp [pen]; positivity
    by_cases hcore : |x - m| ≤ t
    · have hrange : x ∈ Icc (m - t) (m + t) := by
        constructor <;> linarith [(abs_le.mp hcore).1, (abs_le.mp hcore).2]
      have hgrid := happrox x hx hrange
      rw [hwidth] at hgrid
      linarith
    · have habs : t ≤ |x - m| := (lt_of_not_ge hcore).le
      have hxdev : x ≤ m + |x - m| := by linarith [le_abs_self (x - m)]
      have hxt : x * t ≤ m * |x - m| + (x - m) ^ 2 := by
        calc
          x * t ≤ x * |x - m| := mul_le_mul_of_nonneg_left habs hx
          _ ≤ (m + |x - m|) * |x - m| :=
            mul_le_mul_of_nonneg_right hxdev (abs_nonneg _)
          _ = m * |x - m| + (x - m) ^ 2 := by nlinarith only [sq_abs (x - m)]
      have hxpen : x ≤ pen x := (le_div_iff₀ ht).mpr hxt
      linarith [m2_menu_nonneg (Measure.dirac 0) x P]
  have habs : Integrable (fun x : ℝ => |x - m|) ν :=
    (hν.2.1.sub (integrable_const m)).abs
  have hsq := m2_centered_sq_integrable ν hν hMoment m
  have hsum : Integrable (fun x : ℝ => m * |x - m| + (x - m) ^ 2) ν :=
    (habs.const_mul m).add hsq
  have hpen : Integrable pen ν := hsum.div_const t
  have hmenu := m2_menu_integrable ν (Measure.dirac 0) P
  have hmenuδ : Integrable (fun x => menuAt (Measure.dirac 0) x P + δ) ν :=
    hmenu.add (integrable_const δ)
  have hint : (∫ x : ℝ, x ∂ν) ≤
      ∫ x, menuAt (Measure.dirac 0) x P + δ + pen x ∂ν :=
    integral_mono_ae hν.2.1 (hmenuδ.add hpen) hpoint
  rw [integral_add hmenuδ hpen, integral_add hmenu (integrable_const δ)] at hint
  have hc : (∫ _x : ℝ, δ ∂ν) = δ := by simp
  rw [hc] at hint
  change m ≤ menuRevenue ν (Measure.dirac 0) P + δ + (∫ x, pen x ∂ν) at hint
  have hpeneq : (∫ x, pen x ∂ν) =
      (m * (∫ x, |x - m| ∂ν) + σ ^ 2) / t := by
    dsimp [pen]
    rw [integral_div, integral_add (habs.const_mul m) hsq, integral_const_mul]
    change (m * (∫ x, |x - m| ∂ν) + predictionVariance ν) / t =
      (m * (∫ x, |x - m| ∂ν) + σ ^ 2) / t
    rw [hVar]
  have hpenbound : (∫ x, pen x ∂ν) ≤ σ * (m + σ) / t := by
    rw [hpeneq]
    apply div_le_div_of_nonneg_right _ ht.le
    have ha := mul_le_mul_of_nonneg_left (m2_abs_integral_le ν hν hMoment σ hσ hVar) hm
    change m * (∫ x, |x - m| ∂ν) ≤ m * σ at ha
    nlinarith
  have hsup : menuRevenue ν (Measure.dirac 0) P ≤ modelRevenue ν k :=
    le_csSup (m2_model_bdd ν hν k) ⟨P, hP, rfl⟩
  change m - modelRevenue ν k ≤ δ + σ * (m + σ) / t
  linarith

theorem solution (ν η : Measure ℝ)
    (hν : ValidPredictions ν) (hη : ValidNoise η)
    (hV : NonnegativeValuations ν η)
    (hMoment : Integrable (fun x : ℝ => x ^ 2) ν)
    (σ : ℝ) (hσ : 0 ≤ σ) (hVar : predictionVariance ν = σ ^ 2)
    (k : ℕ) (hk : 1 ≤ k) :
    segmentationLoss ν η k ≤
      2 * Real.sqrt (2 * σ * (predictionMean ν + σ) / (k : ℝ)) := by
  have hm : 0 ≤ predictionMean ν := integral_nonneg_of_ae hν.2.2
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hmodel := m2_optimize (σ * (predictionMean ν + σ)) (k : ℝ)
    (predictionMean ν - modelRevenue ν k) (mul_nonneg hσ (add_nonneg hm hσ)) hkpos
    (fun t ht => m2_model_parametric ν hν hMoment σ hσ hVar k hk t ht)
  have heq : 2 * (σ * (predictionMean ν + σ)) / (k : ℝ) =
      2 * σ * (predictionMean ν + σ) / (k : ℝ) := by ring
  rw [heq] at hmodel
  exact (theorem3_model_market_comparison ν η hν hη hV k hk).trans hmodel

