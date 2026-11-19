-- Prove2me | solution 1 for BayesOptStop.Scheme.lemma_10
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T06:44:01.087305+00:00
-- url     : https://prove2.me/submissions/5449f328-f31c-48c7-a674-9c91d2e79a20

import Mathlib

open MeasureTheory ProbabilityTheory Set

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

section Tails
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

lemma mgf_le_chord (Z : Ω → ℝ) (hZm : Measurable Z) (hZ : ∀ᵐ ω ∂P, Z ω ∈ Icc (0:ℝ) 1) (c : ℝ) :
    mgf Z P c ≤ Real.exp ((Real.exp c - 1) * ∫ ω, Z ω ∂P) := by
  have hZi : Integrable Z P := by
    refine Integrable.mono' (integrable_const 1) hZm.aestronglyMeasurable ?_
    filter_upwards [hZ] with ω h; rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [h.1, h.2]
  have hEi : Integrable (fun ω => Real.exp (c * Z ω)) P := by
    refine Integrable.mono' (integrable_const (Real.exp |c|)) (by fun_prop) ?_
    filter_upwards [hZ] with ω h
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have : |c * Z ω| ≤ |c| := by
      rw [abs_mul, abs_of_nonneg h.1]; exact mul_le_of_le_one_right (abs_nonneg c) h.2
    linarith [le_abs_self (c * Z ω)]
  rw [mgf]
  calc ∫ ω, Real.exp (c * Z ω) ∂P ≤ ∫ ω, (1 + Z ω * (Real.exp c - 1)) ∂P := by
        apply integral_mono_ae hEi ((integrable_const 1).add (hZi.mul_const _))
        filter_upwards [hZ] with ω h using chord_exp' c (Z ω) h.1 h.2
    _ = 1 + (∫ ω, Z ω ∂P) * (Real.exp c - 1) := by
        rw [integral_add (integrable_const 1) (hZi.mul_const _), integral_const, integral_mul_const]
        simp
    _ ≤ _ := by
        have := Real.add_one_le_exp ((Real.exp c - 1) * ∫ ω, Z ω ∂P); linarith

variable {m : ℕ} (X : Fin m → Ω → ℝ) (hXm : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
  (hX : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Icc (0:ℝ) 1)
include hXm hind hX

lemma sum_mgf_le (c : ℝ) :
    mgf (fun ω => ∑ i, X i ω) P c ≤ Real.exp ((Real.exp c - 1) * ∫ ω, ∑ i, X i ω ∂P) := by
  have hZi : ∀ i, Integrable (X i) P := by
    intro i
    refine Integrable.mono' (integrable_const 1) (hXm i).aestronglyMeasurable ?_
    filter_upwards [hX i] with ω h; rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [h.1, h.2]
  have hfun : (fun ω => ∑ i, X i ω) = ∑ i, X i := by funext ω; simp
  have e := hind.mgf_sum hXm Finset.univ (t := c)
  rw [← hfun] at e
  rw [e, integral_finset_sum _ (fun i _ => hZi i), Finset.mul_sum, Real.exp_sum]
  exact Finset.prod_le_prod (fun i _ => mgf_nonneg) (fun i _ => mgf_le_chord P (X i) (hXm i) (hX i) c)

lemma sum_exp_int (c : ℝ) : Integrable (fun ω => Real.exp (c * ∑ i, X i ω)) P := by
  have hall : ∀ᵐ ω ∂P, ∀ i, X i ω ∈ Icc (0:ℝ) 1 := ae_all_iff.mpr hX
  refine Integrable.mono' (integrable_const (Real.exp (|c| * m))) (by fun_prop) ?_
  filter_upwards [hall] with ω h
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have hs0 : 0 ≤ ∑ i, X i ω := Finset.sum_nonneg (fun i _ => (h i).1)
  have hs1 : ∑ i, X i ω ≤ m := by
    calc ∑ i, X i ω ≤ ∑ _i : Fin m, (1:ℝ) := Finset.sum_le_sum (fun i _ => (h i).2)
      _ = m := by simp
  calc c * ∑ i, X i ω ≤ |c| * ∑ i, X i ω := mul_le_mul_of_nonneg_right (le_abs_self c) hs0
    _ ≤ |c| * m := mul_le_mul_of_nonneg_left hs1 (abs_nonneg c)

lemma lower_raw (t : ℝ) (ht : 0 < t) (htM : t ≤ ∫ ω, ∑ i, X i ω ∂P) :
    P.real {ω | ∑ i, X i ω ≤ t} ≤
      Real.exp (t * Real.log ((∫ ω, ∑ i, X i ω ∂P) / t) + t - ∫ ω, ∑ i, X i ω ∂P) := by
  set M := ∫ ω, ∑ i, X i ω ∂P
  have hM0 : 0 < M := lt_of_lt_of_le ht htM
  set c := Real.log (M / t) with hc
  have hc0 : 0 ≤ c := Real.log_nonneg (by rw [le_div_iff₀ ht]; linarith)
  have hec : Real.exp (-c) = t / M := by
    rw [hc, Real.exp_neg, Real.exp_log (by positivity), inv_div]
  have h1 := measure_le_le_exp_mul_mgf (μ := P) (X := fun ω => ∑ i, X i ω) t
    (neg_nonpos.mpr hc0) (sum_exp_int P X hXm hind hX (-c))
  refine h1.trans ?_
  have h2 := sum_mgf_le P X hXm hind hX (-c)
  rw [hec] at h2
  calc Real.exp (- -c * t) * mgf (fun ω => ∑ i, X i ω) P (-c)
      ≤ Real.exp (- -c * t) * Real.exp ((t / M - 1) * M) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; rw [hc]; field_simp; ring

lemma upper_raw (t : ℝ) (hM : 0 < ∫ ω, ∑ i, X i ω ∂P) (htM : ∫ ω, ∑ i, X i ω ∂P ≤ t) :
    P.real {ω | t ≤ ∑ i, X i ω} ≤
      Real.exp (-(t * Real.log (t / ∫ ω, ∑ i, X i ω ∂P)) + t - ∫ ω, ∑ i, X i ω ∂P) := by
  set M := ∫ ω, ∑ i, X i ω ∂P
  have ht : 0 < t := lt_of_lt_of_le hM htM
  set c := Real.log (t / M) with hc
  have hc0 : 0 ≤ c := Real.log_nonneg (by rw [le_div_iff₀ hM]; linarith)
  have hec : Real.exp c = t / M := by rw [hc, Real.exp_log (by positivity)]
  have h1 := measure_ge_le_exp_mul_mgf (μ := P) (X := fun ω => ∑ i, X i ω) t hc0
    (sum_exp_int P X hXm hind hX c)
  refine h1.trans ?_
  have h2 := sum_mgf_le P X hXm hind hX c
  rw [hec] at h2
  calc Real.exp (-c * t) * mgf (fun ω => ∑ i, X i ω) P c
      ≤ Real.exp (-c * t) * Real.exp ((t / M - 1) * M) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; rw [hc]; field_simp; ring

lemma lower_zero :
    P.real {ω | ∑ i, X i ω ≤ 0} ≤ Real.exp (-(∫ ω, ∑ i, X i ω ∂P) / 3) := by
  set c := Real.log (3 / 2) with hc
  have hc0 : 0 ≤ c := Real.log_nonneg (by norm_num)
  have hec : Real.exp (-c) = 2 / 3 := by
    rw [hc, Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have h1 := measure_le_le_exp_mul_mgf (μ := P) (X := fun ω => ∑ i, X i ω) 0
    (neg_nonpos.mpr hc0) (sum_exp_int P X hXm hind hX (-c))
  refine h1.trans ?_
  have h2 := sum_mgf_le P X hXm hind hX (-c)
  rw [hec] at h2
  rw [mul_zero, Real.exp_zero, one_mul]
  refine h2.trans (le_of_eq ?_)
  congr 1; ring

end Tails

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
    simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
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

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (Y : Fin n → Ω → ℝ) (hmeas : ∀ i, Measurable (Y i)) (hind : iIndepFun Y P)
    (hrange : ∀ i x, Y i x ∈ Set.Icc (0 : ℝ) 1) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    P.real {x | θ * (∫ y, (∑ i, Y i y) / n ∂P) <
        |(∑ i, Y i x) / n - ∫ y, (∑ i, Y i y) / n ∂P|} ≤
      2 * Real.exp (-(θ ^ 2 * n * ∫ y, (∑ i, Y i y) / n ∂P) / 3) := by
  have hX : ∀ i, ∀ᵐ ω ∂P, Y i ω ∈ Icc (0:ℝ) 1 := fun i => Filter.Eventually.of_forall (hrange i)
  rcases Nat.eq_zero_or_pos n with h0 | hnpos
  · subst h0
    have : {x : Ω | θ * (∫ y, (∑ i : Fin 0, Y i y) / ((0:ℕ):ℝ) ∂P) <
        |(∑ i : Fin 0, Y i x) / ((0:ℕ):ℝ) - ∫ y, (∑ i : Fin 0, Y i y) / ((0:ℕ):ℝ) ∂P|} = ∅ := by
      ext x; simp
    rw [this, measureReal_empty]; positivity
  have hn : (0:ℝ) < n := by exact_mod_cast hnpos
  set M := ∫ ω, ∑ i, Y i ω ∂P with hM
  have hM0 : 0 ≤ M := integral_nonneg (fun ω => Finset.sum_nonneg (fun i _ => (hrange i ω).1))
  have hmean : ∫ y, (∑ i, Y i y) / n ∂P = M / n := by rw [integral_div]
  rw [hmean]
  have hsub : {x | θ * (M / n) < |(∑ i, Y i x) / n - M / n|} ⊆ {x | θ * M ≤ |(∑ i, Y i x) - M|} := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    have e : (∑ i, Y i x) / n - M / n = ((∑ i, Y i x) - M) / n := by ring
    rw [e, abs_div, abs_of_pos hn, lt_div_iff₀ hn] at hx
    have : θ * (M / n) * n = θ * M := by field_simp
    linarith
  refine (measureReal_mono hsub).trans ?_
  have h := two_sided_gen P (fun ω => ∑ i, Y i ω) M (sum_mgf_le P Y hmeas hind hX)
    (sum_exp_int P Y hmeas hind hX) hM0 θ hθ0 hθ1
  refine h.trans (le_of_eq ?_)
  congr 2; field_simp
