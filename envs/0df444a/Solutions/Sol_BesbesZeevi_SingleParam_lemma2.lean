-- Prove2me | solution 1 for BesbesZeevi.SingleParam.lemma2
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T06:42:33.545531+00:00
-- url     : https://prove2.me/submissions/93b4fdf8-4612-42cb-a141-71d6365be8c2

import Mathlib

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

/-- log(1+x) ≥ 2x/(2+x) for x ≥ 0 -/
lemma log_one_add_ge (x : ℝ) (hx : 0 ≤ x) : 2 * x / (2 + x) ≤ Real.log (1 + x) := by
  let g : ℝ → ℝ := fun y => Real.log (1 + y) - 2 * y / (2 + y)
  have hmono : MonotoneOn g (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · intro y hy
      have hy : (0:ℝ) ≤ y := hy
      apply ContinuousAt.continuousWithinAt
      have h1 : (1 + y) ≠ 0 := by linarith
      have h2 : (2 + y) ≠ 0 := by linarith
      fun_prop (disch := assumption)
    · intro y hy
      rw [interior_Ici] at hy
      have hy : (0:ℝ) < y := hy
      apply DifferentiableAt.differentiableWithinAt
      have h1 : (1 + y) ≠ 0 := by linarith
      have h2 : (2 + y) ≠ 0 := by linarith
      fun_prop (disch := assumption)
    · intro y hy
      rw [interior_Ici] at hy
      have hy : (0:ℝ) < y := hy
      have hd : HasDerivAt g (1 / (1 + y) - (2 * (2 + y) - 2 * y * 1) / (2 + y) ^ 2) y := by
        have a1 : HasDerivAt (fun y : ℝ => Real.log (1 + y)) (1 / (1 + y)) y := by
          have := ((hasDerivAt_id y).const_add 1).log (by simp; linarith)
          simpa [one_div] using this
        have a2 : HasDerivAt (fun y : ℝ => 2 * y / (2 + y))
            ((2 * 1 * (2 + y) - 2 * y * 1) / (2 + y) ^ 2) y := by
          have := ((hasDerivAt_id' y).const_mul 2).div ((hasDerivAt_id' y).const_add 2)
            (by linarith)
          exact this
        exact (a1.sub a2).congr_deriv (by ring)
      rw [hd.deriv]
      have : (1:ℝ) / (1 + y) - (2 * (2 + y) - 2 * y * 1) / (2 + y) ^ 2 =
          y ^ 2 / ((1 + y) * (2 + y) ^ 2) := by
        field_simp; ring
      rw [this]; positivity
  have := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hx) hx
  simp only [g, add_zero, Real.log_one, mul_zero, zero_div, sub_zero] at this
  linarith

/-- (1-δ) log(1-δ) ≥ -δ + δ²/2 for δ ∈ [0,1) -/
lemma one_sub_log_ge (δ : ℝ) (h0 : 0 ≤ δ) (h1 : δ < 1) :
    -δ + δ ^ 2 / 2 ≤ (1 - δ) * Real.log (1 - δ) := by
  let h : ℝ → ℝ := fun y => (1 - y) * Real.log (1 - y) + y - y ^ 2 / 2
  have hmono : MonotoneOn h (Ico 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ico 0 1)
    · intro y hy
      apply ContinuousAt.continuousWithinAt
      have : (1 - y) ≠ 0 := by linarith [hy.2]
      fun_prop (disch := assumption)
    · intro y hy
      rw [interior_Ico] at hy
      apply DifferentiableAt.differentiableWithinAt
      have : (1 - y) ≠ 0 := by linarith [hy.2]
      fun_prop (disch := assumption)
    · intro y hy
      rw [interior_Ico] at hy
      have hne : (1 - y) ≠ 0 := by linarith [hy.2]
      have hd : HasDerivAt h (-Real.log (1 - y) - y) y := by
        have a1 : HasDerivAt (fun y : ℝ => 1 - y) (-1) y := by
          simpa using (hasDerivAt_id y).const_sub 1
        have a2 := (a1.mul (a1.log hne))
        have a3 := (a2.add (hasDerivAt_id y)).sub ((hasDerivAt_pow 2 y).div_const 2)
        exact a3.congr_deriv (by field_simp; ring)
      rw [hd.deriv]
      have := Real.log_le_sub_one_of_pos (by linarith [hy.2] : (0:ℝ) < 1 - y)
      linarith
  have := hmono (mem_Ico.mpr ⟨le_rfl, by norm_num⟩) (mem_Ico.mpr ⟨h0, h1⟩) h0
  simp only [h, sub_zero, Real.log_one, mul_zero, zero_add, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, zero_div] at this
  linarith

lemma chord_exp' (c z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    Real.exp (c * z) ≤ 1 + z * (Real.exp c - 1) := by
  have h := convexOn_exp.2 (Set.mem_univ 0) (Set.mem_univ c) (by linarith : 0 ≤ 1 - z) hz0
    (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
  calc Real.exp (c * z) = Real.exp (z * c) := by ring_nf
    _ ≤ (1 - z) + z * Real.exp c := h
    _ = _ := by ring


section Gen
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (Y : Ω → ℝ) (M : ℝ) (hmgf : ∀ c, mgf Y P c ≤ Real.exp ((Real.exp c - 1) * M))
  (hint : ∀ c, Integrable (fun ω => Real.exp (c * Y ω)) P)
include hmgf hint

lemma lower_gen (t : ℝ) (ht : 0 < t) (htM : t ≤ M) :
    P.real {ω | Y ω ≤ t} ≤ Real.exp (t * Real.log (M / t) + t - M) := by
  have hM0 : 0 < M := lt_of_lt_of_le ht htM
  set c := Real.log (M / t) with hc
  have hc0 : 0 ≤ c := Real.log_nonneg (by rw [le_div_iff₀ ht]; linarith)
  have hec : Real.exp (-c) = t / M := by
    rw [hc, Real.exp_neg, Real.exp_log (by positivity), inv_div]
  have h1 := measure_le_le_exp_mul_mgf (μ := P) (X := Y) t (neg_nonpos.mpr hc0) (hint (-c))
  refine h1.trans ?_
  have h2 := hmgf (-c)
  rw [hec] at h2
  calc Real.exp (- -c * t) * mgf Y P (-c)
      ≤ Real.exp (- -c * t) * Real.exp ((t / M - 1) * M) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; rw [hc]; field_simp; ring

lemma upper_gen (t : ℝ) (hM : 0 < M) (htM : M ≤ t) :
    P.real {ω | t ≤ Y ω} ≤ Real.exp (-(t * Real.log (t / M)) + t - M) := by
  have ht : 0 < t := lt_of_lt_of_le hM htM
  set c := Real.log (t / M) with hc
  have hc0 : 0 ≤ c := Real.log_nonneg (by rw [le_div_iff₀ hM]; linarith)
  have hec : Real.exp c = t / M := by rw [hc, Real.exp_log (by positivity)]
  have h1 := measure_ge_le_exp_mul_mgf (μ := P) (X := Y) t hc0 (hint c)
  refine h1.trans ?_
  have h2 := hmgf c
  rw [hec] at h2
  calc Real.exp (-c * t) * mgf Y P c
      ≤ Real.exp (-c * t) * Real.exp ((t / M - 1) * M) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; rw [hc]; field_simp; ring

lemma lower_zero_gen : P.real {ω | Y ω ≤ 0} ≤ Real.exp (-M / 3) := by
  set c := Real.log (3 / 2) with hc
  have hc0 : 0 ≤ c := Real.log_nonneg (by norm_num)
  have hec : Real.exp (-c) = 2 / 3 := by
    rw [hc, Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have h1 := measure_le_le_exp_mul_mgf (μ := P) (X := Y) 0 (neg_nonpos.mpr hc0) (hint (-c))
  refine h1.trans ?_
  have h2 := hmgf (-c)
  rw [hec] at h2
  rw [mul_zero, Real.exp_zero, one_mul]
  refine h2.trans (le_of_eq ?_)
  congr 1; ring

lemma two_sided_gen (hM0 : 0 ≤ M) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    P.real {ω | δ * M ≤ |Y ω - M|} ≤ 2 * Real.exp (-(δ ^ 2 * M / 3)) := by
  have htriv : P.real {ω | δ * M ≤ |Y ω - M|} ≤ 1 := measureReal_le_one
  rcases hM0.eq_or_lt with hz | hMpos
  · refine htriv.trans ?_
    rw [← hz]; simp
  rcases hδ0.eq_or_lt with hδz | hδpos
  · refine htriv.trans ?_
    rw [← hδz]; simp
  have hsub : {ω | δ * M ≤ |Y ω - M|} ⊆
      {ω | (1 + δ) * M ≤ Y ω} ∪ {ω | Y ω ≤ (1 - δ) * M} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
    rcases le_abs'.mp hω with h | h
    · right; linarith
    · left; linarith
  have hup : P.real {ω | (1 + δ) * M ≤ Y ω} ≤ Real.exp (-(δ ^ 2 * M / 3)) := by
    refine (upper_gen P Y M hmgf hint ((1 + δ) * M) hMpos (by nlinarith)).trans ?_
    apply Real.exp_le_exp.mpr
    have hlog : Real.log ((1 + δ) * M / M) = Real.log (1 + δ) := by
      rw [show (1 + δ) * M / M = 1 + δ by field_simp]
    rw [hlog]
    have hl := log_one_add_ge δ hδ0
    have h2 : 0 < 2 + δ := by linarith
    rw [div_le_iff₀ h2] at hl
    have hl' := mul_le_mul_of_nonneg_left hl (by positivity : (0:ℝ) ≤ (1 + δ) * M)
    have key0 : δ ^ 2 * M / (2 + δ) ≤ (1 + δ) * M * Real.log (1 + δ) - δ * M := by
      rw [div_le_iff₀ h2]; nlinarith
    have : δ ^ 2 * M / 3 ≤ δ ^ 2 * M / (2 + δ) :=
      div_le_div_of_nonneg_left (by positivity) h2 (by linarith)
    linarith
  have hlow : P.real {ω | Y ω ≤ (1 - δ) * M} ≤ Real.exp (-(δ ^ 2 * M / 3)) := by
    rcases hδ1.lt_or_eq with hlt | heq
    · have ht : 0 < (1 - δ) * M := by nlinarith
      refine (lower_gen P Y M hmgf hint ((1 - δ) * M) ht (by nlinarith)).trans ?_
      apply Real.exp_le_exp.mpr
      have hlog : Real.log (M / ((1 - δ) * M)) = -Real.log (1 - δ) := by
        rw [show M / ((1 - δ) * M) = (1 - δ)⁻¹ by field_simp, Real.log_inv]
      rw [hlog]
      have := one_sub_log_ge δ hδ0 hlt
      have h3 : δ ^ 2 * M / 3 ≤ δ ^ 2 * M / 2 := by
        apply div_le_div_of_nonneg_left (by positivity) (by norm_num) (by norm_num)
      nlinarith
    · rw [heq]
      have := lower_zero_gen P Y M hmgf hint
      simp only [sub_self, zero_mul]
      refine this.trans (le_of_eq ?_)
      congr 1; ring
  calc P.real {ω | δ * M ≤ |Y ω - M|}
      ≤ P.real ({ω | (1 + δ) * M ≤ Y ω} ∪ {ω | Y ω ≤ (1 - δ) * M}) := measureReal_mono hsub
    _ ≤ P.real {ω | (1 + δ) * M ≤ Y ω} + P.real {ω | Y ω ≤ (1 - δ) * M} :=
        measureReal_union_le _ _
    _ ≤ _ := by linarith

end Gen

lemma poisson_hasSum (lam : ℝ≥0) (c : ℝ) :
    HasSum (fun n : ℕ => (Real.exp (-(lam:ℝ)) * (lam:ℝ) ^ n / (n.factorial)) * Real.exp (c * n))
      (Real.exp ((Real.exp c - 1) * lam)) := by
  have h := NormedSpace.expSeries_div_hasSum_exp ((lam:ℝ) * Real.exp c)
  rw [← Real.exp_eq_exp_ℝ] at h
  have h2 := h.mul_left (Real.exp (-(lam:ℝ)))
  have e1 : (fun n : ℕ => (Real.exp (-(lam:ℝ)) * (lam:ℝ) ^ n / (n.factorial)) * Real.exp (c * n)) =
      fun i : ℕ => Real.exp (-(lam:ℝ)) * (((lam:ℝ) * Real.exp c) ^ i / (i.factorial)) := by
    funext n
    rw [mul_pow, ← Real.exp_nat_mul, mul_comm (n:ℝ) c]
    ring
  have e2 : Real.exp ((Real.exp c - 1) * lam) = Real.exp (-(lam:ℝ)) * Real.exp ((lam:ℝ) * Real.exp c) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e1, e2]; exact h2

lemma poisson_tools (lam : ℝ≥0) :
    (∀ c, Integrable (fun k : ℕ => Real.exp (c * (k : ℝ))) (poissonMeasure lam)) ∧
    (∀ c, mgf (fun k : ℕ => (k : ℝ)) (poissonMeasure lam) c ≤
      Real.exp ((Real.exp c - 1) * (lam : ℝ))) := by
  have hint : ∀ c, Integrable (fun k : ℕ => Real.exp (c * (k : ℝ))) (poissonMeasure lam) := by
    intro c
    rw [integrable_poissonMeasure_iff]
    refine (poisson_hasSum lam c).summable.congr (fun n => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine ⟨hint, fun c => ?_⟩
  rw [mgf, integral_poissonMeasure' (hint c)]
  simp only [smul_eq_mul]
  rw [(poisson_hasSum lam c).tsum_eq]

lemma poisson_upper_pt (Λ : ℝ) (hΛ : 0 < Λ) (ε : ℝ) (hε : 0 < ε) :
    (poissonMeasure Λ.toNNReal).real {n : ℕ | ε ≤ (n : ℝ) - Λ} ≤ Real.exp (-(ε ^ 2 / (2 * Λ + ε))) := by
  obtain ⟨hint, hmgf⟩ := poisson_tools Λ.toNNReal
  have hM : ((Λ.toNNReal : ℝ)) = Λ := Real.coe_toNNReal _ hΛ.le
  rw [hM] at hmgf
  have hset : {n : ℕ | ε ≤ (n : ℝ) - Λ} = {n : ℕ | Λ + ε ≤ (n : ℝ)} := by
    ext n; simp only [Set.mem_ofPred_eq]; constructor <;> intro h <;> linarith
  rw [hset]
  refine (upper_gen (poissonMeasure Λ.toNNReal) (fun k : ℕ => (k : ℝ)) Λ hmgf hint (Λ + ε) hΛ
    (by linarith)).trans ?_
  apply Real.exp_le_exp.mpr
  have hx : 0 ≤ ε / Λ := by positivity
  have hl := log_one_add_ge (ε / Λ) hx
  have hlog : Real.log ((Λ + ε) / Λ) = Real.log (1 + ε / Λ) := by
    congr 1; field_simp
  rw [hlog]
  have hfrac : 2 * (ε / Λ) / (2 + ε / Λ) = 2 * ε / (2 * Λ + ε) := by
    field_simp
  rw [hfrac] at hl
  have hpos : 0 < 2 * Λ + ε := by linarith
  have h1 : (Λ + ε) * (2 * ε / (2 * Λ + ε)) ≤ (Λ + ε) * Real.log (1 + ε / Λ) :=
    mul_le_mul_of_nonneg_left hl (by linarith)
  have h2 : (Λ + ε) * (2 * ε / (2 * Λ + ε)) - ε = ε ^ 2 / (2 * Λ + ε) := by
    field_simp; ring
  linarith

lemma poisson_lower_pt (m : ℝ) (hm : 0 < m) (a : ℝ) (ha : 0 < a) (ham : a < m) :
    (poissonMeasure m.toNNReal).real {k : ℕ | (k : ℝ) - m < -a} ≤ Real.exp (-(a ^ 2 / (2 * m))) := by
  obtain ⟨hint, hmgf⟩ := poisson_tools m.toNNReal
  have hM : ((m.toNNReal : ℝ)) = m := Real.coe_toNNReal _ hm.le
  rw [hM] at hmgf
  have hsub : {k : ℕ | (k : ℝ) - m < -a} ⊆ {k : ℕ | (k : ℝ) ≤ m - a} := by
    intro k hk; simp only [Set.mem_ofPred_eq] at hk ⊢; linarith
  refine (measureReal_mono hsub).trans ?_
  have ht : 0 < m - a := by linarith
  refine (lower_gen (poissonMeasure m.toNNReal) (fun k : ℕ => (k : ℝ)) m hmgf hint (m - a) ht
    (by linarith)).trans ?_
  apply Real.exp_le_exp.mpr
  set δ := a / m with hδ
  have hδ0 : 0 ≤ δ := by positivity
  have hδ1 : δ < 1 := by rw [hδ, div_lt_one hm]; exact ham
  have hma : m - a = (1 - δ) * m := by rw [hδ]; field_simp
  rw [hma]
  have hlog : Real.log (m / ((1 - δ) * m)) = -Real.log (1 - δ) := by
    rw [show m / ((1 - δ) * m) = (1 - δ)⁻¹ by field_simp, Real.log_inv]
  rw [hlog]
  have := one_sub_log_ge δ hδ0 hδ1
  have he : a ^ 2 / (2 * m) = δ ^ 2 * m / 2 := by rw [hδ]; field_simp
  rw [he]
  nlinarith

theorem solution (M η β : ℝ) (hM : 0 < M) (hη : 0 < η) (hβ : 0 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ μ ∈ Set.Icc (0 : ℝ) M, ∀ r : ℝ, (n : ℝ) ^ β ≤ r →
      (poissonMeasure (μ * r).toNNReal
          {k : ℕ | (k : ℝ) - μ * r >
            r * (2 * Real.sqrt η * Real.sqrt M * Real.sqrt (Real.log n) / Real.sqrt r)}).toReal
          ≤ C / (n : ℝ) ^ η ∧
      (poissonMeasure (μ * r).toNNReal
          {k : ℕ | (k : ℝ) - μ * r <
            -(r * (2 * Real.sqrt η * Real.sqrt M * Real.sqrt (Real.log n) / Real.sqrt r))}).toReal
          ≤ C / (n : ℝ) ^ η := by
  -- eventually η log n ≤ M n^β
  have hlo := (isLittleO_log_rpow_atTop hβ).bound (c := M / η) (by positivity)
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp
    (tendsto_natCast_atTop_atTop.eventually hlo)
  set C : ℝ := max 1 ((N0 : ℝ) ^ η) with hC
  have hC1 : 1 ≤ C := le_max_left _ _
  refine ⟨C, by linarith, fun n hn μ hμ r hr => ?_⟩
  have hn0 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0:ℝ) < n := by linarith
  set R := r with hR
  have hRpos : 0 < R := lt_of_lt_of_le (Real.rpow_pos_of_pos hnpos β) hr
  set L := Real.log n with hL
  have hL0 : 0 ≤ L := Real.log_nonneg hn0
  set m := μ * R with hm
  have hm0 : 0 ≤ m := mul_nonneg hμ.1 hRpos.le
  have hmM : m ≤ M * R := mul_le_mul_of_nonneg_right hμ.2 hRpos.le
  set a := R * (2 * Real.sqrt η * Real.sqrt M * Real.sqrt L / Real.sqrt R) with ha
  have ha0 : 0 ≤ a := by positivity
  have ha2 : a ^ 2 = 4 * η * M * L * R := by
    have hsR : Real.sqrt R ≠ 0 := (Real.sqrt_pos.mpr hRpos).ne'
    rw [ha, mul_pow, div_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hη.le, Real.sq_sqrt hM.le,
      Real.sq_sqrt hL0, Real.sq_sqrt hRpos.le]
    field_simp; ring
  have hnη : 0 < (n:ℝ) ^ η := Real.rpow_pos_of_pos hnpos η
  have hpow : Real.exp (-(η * L)) = 1 / (n:ℝ) ^ η := by
    rw [hL, Real.rpow_def_of_pos hnpos, one_div, ← Real.exp_neg, mul_comm]
  have hCbig : 1 / (n:ℝ) ^ η ≤ C / (n:ℝ) ^ η := div_le_div_of_nonneg_right hC1 hnη.le
  have hCnn : 0 ≤ C / (n:ℝ) ^ η := div_nonneg (by linarith) hnη.le
  -- a = 0 forces L = 0, i.e. n = 1
  have hzero_case : a = 0 → 1 ≤ C / (n:ℝ) ^ η := by
    intro haz
    have hprod : (4 * η * M * R) * L = 0 := by nlinarith [ha2, haz]
    have hLz : L = 0 := by
      rcases mul_eq_zero.mp hprod with h | h
      · exact absurd h (by positivity)
      · exact h
    have : 1 / (n:ℝ) ^ η = 1 := by rw [← hpow, hLz]; simp
    linarith
  have hreal : ∀ S : Set ℕ, (poissonMeasure m.toNNReal).real S ≤ C / (n:ℝ) ^ η →
      poissonMeasure m.toNNReal S ≤ ENNReal.ofReal (C / (n:ℝ) ^ η) := by
    intro S hS
    rw [← ENNReal.ofReal_toReal (measure_ne_top (poissonMeasure m.toNNReal) S)]
    exact ENNReal.ofReal_le_ofReal hS
  have hsq : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → x ^ 2 ≤ y ^ 2 → x ≤ y := fun x y hx hy h =>
    (pow_le_pow_iff_left₀ hx hy (by norm_num : (2:ℕ) ≠ 0)).mp h
  constructor
  · show (poissonMeasure m.toNNReal).real _ ≤ _
    by_cases hsmall : n < N0
    · refine measureReal_le_one.trans ?_
      rw [le_div_iff₀ hnη, one_mul]
      calc (n:ℝ) ^ η ≤ (N0:ℝ) ^ η := Real.rpow_le_rpow hnpos.le (by exact_mod_cast hsmall.le) hη.le
        _ ≤ C := le_max_right _ _
    push Not at hsmall
    have hbound := hN0 n hsmall
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hL0,
      abs_of_pos (Real.rpow_pos_of_pos hnpos β)] at hbound
    have hηL : η * L ≤ M * R := by
      have : L ≤ M / η * R := le_trans hbound (mul_le_mul_of_nonneg_left hr (by positivity))
      calc η * L ≤ η * (M / η * R) := mul_le_mul_of_nonneg_left this hη.le
        _ = M * R := by field_simp
    rcases ha0.eq_or_lt with haz | hapos
    · exact measureReal_le_one.trans (hzero_case haz.symm)
    rcases hm0.eq_or_lt with hmz | hmpos
    · have hempty : {k : ℕ | (k : ℝ) - m > a} ⊆ {k : ℕ | 1 ≤ k} := by
        intro k hk; simp only [Set.mem_ofPred_eq] at hk ⊢
        rw [← hmz] at hk
        have : (0:ℝ) < k := by linarith
        exact_mod_cast this
      refine (measureReal_mono hempty).trans ?_
      have : (poissonMeasure m.toNNReal).real {k : ℕ | 1 ≤ k} = 0 := by
        rw [← hmz]
        simp only [measureReal_def, poissonMeasure, Measure.sum_apply _ (MeasurableSet.of_discrete)]
        rw [ENNReal.tsum_eq_zero.mpr, ENNReal.toReal_zero]
        intro i
        rcases Nat.eq_zero_or_pos i with h | h
        · subst h; simp
        · simp [zero_pow h.ne']
      rw [this]; exact hCnn
    have hsub : {k : ℕ | (k : ℝ) - m > a} ⊆ {k : ℕ | a ≤ (k : ℝ) - m} := by
      intro k hk; simp only [Set.mem_ofPred_eq] at hk ⊢; linarith
    refine (measureReal_mono hsub).trans ((poisson_upper_pt m hmpos a hapos).trans ?_)
    have haMR : a ≤ 2 * (M * R) := by
      apply hsq a (2 * (M * R)) ha0 (by positivity)
      rw [ha2]; nlinarith [mul_le_mul_of_nonneg_left hηL (by positivity : (0:ℝ) ≤ 4 * M * R)]
    have hden : 0 < 2 * m + a := by linarith
    have hkey : η * L ≤ a ^ 2 / (2 * m + a) := by
      rw [le_div_iff₀ hden, ha2]
      have : 2 * m + a ≤ 4 * (M * R) := by linarith
      nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0:ℝ) ≤ η * L)]
    calc Real.exp (-(a ^ 2 / (2 * m + a))) ≤ Real.exp (-(η * L)) := Real.exp_le_exp.mpr (by linarith)
      _ = 1 / (n:ℝ) ^ η := hpow
      _ ≤ _ := hCbig
  · show (poissonMeasure m.toNNReal).real _ ≤ _
    rcases ha0.eq_or_lt with haz | hapos
    · exact measureReal_le_one.trans (hzero_case haz.symm)
    by_cases ham : m ≤ a
    · have hempty : {k : ℕ | (k : ℝ) - m < -a} = ∅ := by
        ext k; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
        have : (0:ℝ) ≤ k := Nat.cast_nonneg k
        linarith
      rw [hempty, measureReal_empty]; exact hCnn
    push Not at ham
    have hmpos : 0 < m := lt_trans hapos ham
    refine (poisson_lower_pt m hmpos a hapos ham).trans ?_
    have hkey : η * L ≤ a ^ 2 / (2 * m) := by
      rw [le_div_iff₀ (by positivity), ha2]
      nlinarith [mul_le_mul_of_nonneg_left hmM (by positivity : (0:ℝ) ≤ 2 * η * L)]
    calc Real.exp (-(a ^ 2 / (2 * m))) ≤ Real.exp (-(η * L)) := Real.exp_le_exp.mpr (by linarith)
      _ = 1 / (n:ℝ) ^ η := hpow
      _ ≤ _ := hCbig
