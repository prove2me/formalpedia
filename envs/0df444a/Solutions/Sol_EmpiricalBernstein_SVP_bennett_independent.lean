-- Prove2me | solution 1 for EmpiricalBernstein.SVP.bennett_independent
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T19:55:24.646437+00:00
-- url     : https://prove2.me/submissions/ace210cf-bac1-4504-8662-8f5f742a8a1b

import Mathlib
import Definitions.Def_VarianceRegularization_Expansion_empMean

set_option autoImplicit false

open Real MeasureTheory ProbabilityTheory VarianceRegularization.Expansion

lemma ebs_N_mono : Monotone (fun u : ℝ => (u - 2) * exp u + u + 2) := by
  have hd : ∀ u : ℝ, HasDerivAt (fun u : ℝ => (u - 2) * exp u + u + 2) ((u - 1) * exp u + 1) u := by
    intro u
    have h1 : HasDerivAt (fun u : ℝ => u - 2) 1 u := (hasDerivAt_id u).sub_const 2
    have h2 := (h1.mul (hasDerivAt_exp u)).add (hasDerivAt_id u) |>.add_const 2
    refine h2.congr_deriv ?_
    ring
  refine monotone_of_deriv_nonneg (fun u => (hd u).differentiableAt) (fun u => ?_)
  rw [(hd u).deriv]
  have h := add_one_le_exp (-u)
  have h2 : (1 - u) * exp u ≤ 1 := by
    have := mul_le_mul_of_nonneg_right h (exp_pos u).le
    rw [← exp_add, neg_add_cancel, exp_zero] at this
    nlinarith
  nlinarith

lemma ebs_k_nonneg (u : ℝ) : 0 ≤ 3 * u ^ 2 - 2 * (3 - u) * (exp u - 1 - u) := by
  have hd : ∀ u : ℝ, HasDerivAt (fun u : ℝ => 3 * u ^ 2 - 2 * (3 - u) * (exp u - 1 - u))
      (2 * ((u - 2) * exp u + u + 2)) u := by
    intro u
    have h1 : HasDerivAt (fun u : ℝ => 3 * u ^ 2) (3 * (2 * u)) u := by
      simpa using (hasDerivAt_pow 2 u).const_mul 3
    have h2 : HasDerivAt (fun u : ℝ => 3 - u) (-1) u := by
      simpa using (hasDerivAt_id u).const_sub 3
    have h3 : HasDerivAt (fun u : ℝ => exp u - 1 - u) (exp u - 1) u := by
      exact ((hasDerivAt_exp u).sub_const 1).sub (hasDerivAt_id u)
    have h4 := h1.sub ((h2.mul h3).const_mul 2)
    have e : (fun u : ℝ => 3 * u ^ 2 - 2 * (3 - u) * (exp u - 1 - u))
        = (fun u : ℝ => 3 * u ^ 2) - fun y => 2 * ((fun u : ℝ => 3 - u) * fun u : ℝ => exp u - 1 - u) y := by
      funext u; simp only [Pi.sub_apply, Pi.mul_apply]; ring
    rw [e]
    refine h4.congr_deriv ?_
    ring
  have hmono := ebs_N_mono
  rcases le_total 0 u with hu | hu
  · have hm : MonotoneOn (fun u : ℝ => 3 * u ^ 2 - 2 * (3 - u) * (exp u - 1 - u)) (Set.Ici 0) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
        (fun x _ => (hd x).continuousAt.continuousWithinAt)
        (fun x _ => (hd x).differentiableAt.differentiableWithinAt) (fun x hx => ?_)
      rw [(hd x).deriv]
      have hx0 : (0 : ℝ) < x := by simpa using hx
      have := hmono hx0.le
      simp at this
      linarith
    have := hm (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hu) hu
    simpa using this
  · have hm : AntitoneOn (fun u : ℝ => 3 * u ^ 2 - 2 * (3 - u) * (exp u - 1 - u)) (Set.Iic 0) := by
      refine antitoneOn_of_deriv_nonpos (convex_Iic 0)
        (fun x _ => (hd x).continuousAt.continuousWithinAt)
        (fun x _ => (hd x).differentiableAt.differentiableWithinAt) (fun x hx => ?_)
      rw [(hd x).deriv]
      have hx0 : x < 0 := by simpa using hx
      have := hmono hx0.le
      simp at this
      linarith
    have := hm (Set.mem_Iic.2 hu) (Set.mem_Iic.2 le_rfl) hu
    simpa using this

lemma ebs_expbound (l y : ℝ) (hl0 : 0 ≤ l) (hl3 : l < 3) (hy : y ≤ 1) :
    exp (l * y) ≤ 1 + l * y + y ^ 2 * (l ^ 2 / (2 * (1 - l / 3))) := by
  have hu : l * y ≤ l := by nlinarith
  have hu3 : l * y < 3 := lt_of_le_of_lt hu hl3
  have hk := ebs_k_nonneg (l * y)
  have h3u : 0 < 3 - l * y := by linarith
  have h3l : 0 < 3 - l := by linarith
  have h1 : exp (l * y) - 1 - l * y ≤ 3 * (l * y) ^ 2 / (2 * (3 - l * y)) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have h2 : 3 * (l * y) ^ 2 / (2 * (3 - l * y)) ≤ 3 * (l * y) ^ 2 / (2 * (3 - l)) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    linarith
  have h4 : 3 * (l * y) ^ 2 / (2 * (3 - l)) = y ^ 2 * (l ^ 2 / (2 * (1 - l / 3))) := by
    have : (1 - l / 3) = (3 - l) / 3 := by ring
    rw [this]
    field_simp
  linarith

lemma ebs79_ae {n : ℕ} (μs : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μs i)]
    (hμs : ∀ i, μs i (Set.Icc (0 : ℝ) 1)ᶜ = 0) (i : Fin n) :
    ∀ᵐ z ∂(Measure.pi μs), z i ∈ Set.Icc (0 : ℝ) 1 := by
  have h : ∀ᵐ y ∂(μs i), y ∈ Set.Icc (0 : ℝ) 1 := by
    rw [ae_iff]; exact hμs i
  exact (Measure.quasiMeasurePreserving_eval μs i).ae h

lemma ebs79_intμ {n : ℕ} (μs : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μs i)]
    (hμs : ∀ i, μs i (Set.Icc (0 : ℝ) 1)ᶜ = 0) (i : Fin n) (f : ℝ → ℝ) (hf : Continuous f) :
    Integrable f (μs i) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hf.continuousOn
  refine Integrable.of_bound hf.aestronglyMeasurable C ?_
  have h : ∀ᵐ y ∂(μs i), y ∈ Set.Icc (0 : ℝ) 1 := by
    rw [ae_iff]; exact hμs i
  filter_upwards [h] with x hx using hC x hx

lemma ebs79_eval {n : ℕ} (μs : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μs i)]
    (i : Fin n) (f : ℝ → ℝ) (hf : Continuous f) :
    ∫ z, f (z i) ∂(Measure.pi μs) = ∫ y, f y ∂(μs i) := by
  conv_rhs => rw [← (measurePreserving_eval μs i).map_eq]
  rw [integral_map (measurable_pi_apply i).aemeasurable hf.aestronglyMeasurable]

lemma ebs79_integrable {n : ℕ} (μs : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μs i)]
    (hμs : ∀ i, μs i (Set.Icc (0 : ℝ) 1)ᶜ = 0) (g : (Fin n → ℝ) → ℝ) (hg : Measurable g)
    (C : ℝ) (hb : ∀ z : Fin n → ℝ, (∀ i, z i ∈ Set.Icc (0 : ℝ) 1) → |g z| ≤ C) :
    Integrable g (Measure.pi μs) := by
  refine Integrable.of_bound hg.aestronglyMeasurable C ?_
  have h : ∀ᵐ z ∂(Measure.pi μs), ∀ i, z i ∈ Set.Icc (0 : ℝ) 1 :=
    ae_all_iff.2 (fun i => ebs79_ae μs hμs i)
  filter_upwards [h] with z hz
  simpa using hb z hz


lemma ebsb_int (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (f : ℝ → ℝ) (hf : Continuous f) : Integrable f ν := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hf.continuousOn
  refine Integrable.of_bound hf.aestronglyMeasurable C ?_
  have h : ∀ᵐ y ∂ν, y ∈ Set.Icc (0 : ℝ) 1 := by
    rw [ae_iff]; exact hν
  filter_upwards [h] with x hx using hC x hx

lemma ebsb_m_le (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Set.Icc (0 : ℝ) 1)ᶜ = 0) :
    ∫ w, w ∂ν ≤ 1 := by
  have hae : ∀ᵐ y ∂ν, y ∈ Set.Icc (0 : ℝ) 1 := by rw [ae_iff]; exact hν
  calc ∫ w, w ∂ν ≤ ∫ w, (1 : ℝ) ∂ν :=
        integral_mono_ae (ebsb_int ν hν _ continuous_id) (integrable_const _)
          (by filter_upwards [hae] with y hy using hy.2)
    _ = 1 := by simp

lemma ebsb_one (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (l : ℝ) (hl0 : 0 ≤ l) (hl3 : l < 3) :
    ∫ y, exp (l * ((∫ w, w ∂ν) - y)) ∂ν
      ≤ exp (l ^ 2 / (2 * (1 - l / 3)) * ∫ y, (y - ∫ w, w ∂ν) ^ 2 ∂ν) := by
  have hm1 := ebsb_m_le ν hν
  set m := ∫ w, w ∂ν with hm
  set K := l ^ 2 / (2 * (1 - l / 3)) with hK
  have hae : ∀ᵐ y ∂ν, y ∈ Set.Icc (0 : ℝ) 1 := by rw [ae_iff]; exact hν
  have hI1 : Integrable (fun y : ℝ => 1 + l * (m - y) + (m - y) ^ 2 * K) ν :=
    ebsb_int ν hν _ (by fun_prop)
  have h1 : ∫ y, exp (l * (m - y)) ∂ν ≤ ∫ y, (1 + l * (m - y) + (m - y) ^ 2 * K) ∂ν := by
    refine integral_mono_ae (ebsb_int ν hν _ (by fun_prop)) hI1 ?_
    filter_upwards [hae] with y hy
    have := ebs_expbound l (m - y) hl0 hl3 (by linarith [hy.1])
    simpa [mul_comm] using this
  have h2 : ∫ y, (1 + l * (m - y) + (m - y) ^ 2 * K) ∂ν = 1 + K * ∫ y, (y - m) ^ 2 ∂ν := by
    have i1 : Integrable (fun y : ℝ => 1 + l * (m - y)) ν := ebsb_int ν hν _ (by fun_prop)
    have i2 : Integrable (fun y : ℝ => (m - y) ^ 2 * K) ν := ebsb_int ν hν _ (by fun_prop)
    have i3 : Integrable (fun y : ℝ => l * (m - y)) ν := ebsb_int ν hν _ (by fun_prop)
    have i4 : Integrable (fun y : ℝ => m - y) ν := ebsb_int ν hν _ (by fun_prop)
    have hsq : (fun y : ℝ => (m - y) ^ 2 * K) = fun y => K * (y - m) ^ 2 := by
      funext y; ring
    have hr : ν.real Set.univ = 1 := by simp
    rw [integral_add i1 i2, integral_add (integrable_const _) i3, integral_const_mul,
      integral_sub (integrable_const _) (ebsb_int ν hν (fun y => y) continuous_id), hsq,
      integral_const_mul]
    simp only [integral_const, hr, smul_eq_mul, one_mul]
    rw [← hm]
    ring
  have h3 := add_one_le_exp (K * ∫ y, (y - m) ^ 2 ∂ν)
  rw [h2] at h1
  linarith

lemma ebsb_tail {n : ℕ} (μs : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μs i)]
    (hμs : ∀ i, μs i (Set.Icc (0 : ℝ) 1)ᶜ = 0) (l : ℝ) (hl0 : 0 ≤ l) (hl3 : l < 3) (c : ℝ) :
    (Measure.pi μs).real {z | c ≤ ∑ i, ((∫ w, w ∂(μs i)) - z i)}
      ≤ exp (-l * c + l ^ 2 / (2 * (1 - l / 3))
          * ∑ i, ∫ y, (y - ∫ w, w ∂(μs i)) ^ 2 ∂(μs i)) := by
  set P := Measure.pi μs with hP
  set m : Fin n → ℝ := fun i => ∫ w, w ∂(μs i) with hm
  set K := l ^ 2 / (2 * (1 - l / 3)) with hK
  set X : Fin n → (Fin n → ℝ) → ℝ := fun i z => m i - z i with hX
  have hindep : iIndepFun X P :=
    iIndepFun_pi (μ := μs) (X := fun i (y : ℝ) => m i - y) (fun i => by fun_prop)
  have hmeas : ∀ i, Measurable (X i) := fun i => by simp only [hX]; fun_prop
  have hint : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      Integrable (fun z => exp (l * X i z)) P := by
    intro i _
    have h1 : Integrable (fun y : ℝ => exp (l * (m i - y))) (μs i) :=
      ebsb_int (μs i) (hμs i) _ (by fun_prop)
    exact ((measurePreserving_eval μs i).integrable_comp
      (by exact (by fun_prop : Continuous fun y : ℝ => exp (l * (m i - y))).aestronglyMeasurable)).2 h1
  have hI := hindep.integrable_exp_mul_sum hmeas hint
  have hmgf := hindep.mgf_sum hmeas Finset.univ (t := l)
  have hone : ∀ i, mgf (X i) P l ≤ exp (K * ∫ y, (y - m i) ^ 2 ∂(μs i)) := by
    intro i
    have : mgf (X i) P l = ∫ y, exp (l * (m i - y)) ∂(μs i) := by
      rw [mgf]
      exact ebs79_eval μs i (fun y => exp (l * (m i - y))) (by fun_prop)
    rw [this]
    exact ebsb_one (μs i) (hμs i) l hl0 hl3
  have hprod : mgf (∑ i ∈ Finset.univ, X i) P l
      ≤ exp (K * ∑ i, ∫ y, (y - m i) ^ 2 ∂(μs i)) := by
    rw [hmgf, Finset.mul_sum, Real.exp_sum]
    exact Finset.prod_le_prod (fun i _ => mgf_nonneg) (fun i _ => hone i)
  have hch := measure_ge_le_exp_mul_mgf (μ := P) (X := ∑ i ∈ Finset.univ, X i) c hl0 (by
    simpa using hI)
  have hset : {ω | c ≤ (∑ i ∈ Finset.univ, X i) ω} = {z | c ≤ ∑ i, (m i - z i)} := by
    ext z; simp [hX]
  rw [hset] at hch
  calc P.real {z | c ≤ ∑ i, (m i - z i)}
      ≤ exp (-l * c) * mgf (∑ i ∈ Finset.univ, X i) P l := hch
    _ ≤ exp (-l * c) * exp (K * ∑ i, ∫ y, (y - m i) ^ 2 ∂(μs i)) :=
        mul_le_mul_of_nonneg_left hprod (exp_pos _).le
    _ = _ := by rw [← exp_add]

lemma ebsb_alg (v a : ℝ) (hv : 0 < v) (ha : 0 ≤ a) :
    -(a / (1 + a / 3)) * (v * a + (v * a ^ 2 / 2) / 3)
      + (a / (1 + a / 3)) ^ 2 / (2 * (1 - (a / (1 + a / 3)) / 3)) * v = -(v * a ^ 2 / 2) := by
  have h1 : (1 + a / 3) ≠ 0 := by positivity
  have h2 : (1 - (a / (1 + a / 3)) / 3) ≠ 0 := by
    have : 1 - (a / (1 + a / 3)) / 3 = 1 / (1 + a / 3) := by field_simp; ring
    rw [this]; positivity
  field_simp
  ring

theorem solution {n : ℕ} (hn : 1 ≤ n) (μs : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μs i)] (hμs : ∀ i, μs i (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (δ : ℝ) (hδ : 0 < δ) :
    Measure.pi μs {x | (∫ z, empMean z ∂(Measure.pi μs))
        > empMean x
          + Real.sqrt (2 * ((1 / (n : ℝ)) * ∑ i, variance (fun y : ℝ => y) (μs i))
              * Real.log (1 / δ) / n)
          + Real.log (1 / δ) / (3 * n)}
      ≤ ENNReal.ofReal δ := by
  classical
  set P := Measure.pi μs with hP
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  by_cases hδ1 : 1 < δ
  · calc P _ ≤ 1 := prob_le_one
      _ ≤ ENNReal.ofReal δ := by
        rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hδ1.le
  have hδ1' : δ ≤ 1 := not_lt.1 hδ1
  set L := Real.log (1 / δ) with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  set m : Fin n → ℝ := fun i => ∫ w, w ∂(μs i) with hm
  set s : Fin n → ℝ := fun i => ∫ y, (y - ∫ w, w ∂(μs i)) ^ 2 ∂(μs i) with hs
  have hvar : ∀ i, variance (fun y : ℝ => y) (μs i) = s i := fun i => by
    rw [variance_eq_integral (X := fun y : ℝ => y) aemeasurable_id]
  have hs0 : ∀ i, 0 ≤ s i := fun i => integral_nonneg (fun y => sq_nonneg _)
  set v : ℝ := ∑ i, s i with hv
  have hv0 : 0 ≤ v := Finset.sum_nonneg (fun i _ => hs0 i)
  have hEmp : ∫ z, empMean z ∂P = (n : ℝ)⁻¹ * ∑ i, m i := by
    unfold empMean
    have hint : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        Integrable (fun z : Fin n → ℝ => z i) P := by
      intro i _
      exact ebs79_integrable μs hμs _ (measurable_pi_apply i) 1 (fun z hz => by
        rw [abs_of_nonneg (hz i).1]; exact (hz i).2)
    rw [integral_const_mul, integral_finset_sum _ hint]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => ebs79_eval μs i (fun y => y) continuous_id)
  set t : ℝ := Real.sqrt (2 * v * L) + L / 3 with ht
  have ht0 : 0 ≤ t := by positivity
  have hsub : {x | (∫ z, empMean z ∂P)
        > empMean x
          + Real.sqrt (2 * ((1 / (n : ℝ)) * ∑ i, variance (fun y : ℝ => y) (μs i))
              * Real.log (1 / δ) / n)
          + Real.log (1 / δ) / (3 * n)} ⊆ {z | t < ∑ i, (m i - z i)} := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [hEmp] at hx
    simp only [hvar] at hx
    unfold empMean at hx
    have hsq : Real.sqrt (2 * ((1 / (n : ℝ)) * ∑ i, s i) * L / n)
        = Real.sqrt (2 * v * L) / n := by
      have e : 2 * ((1 / (n : ℝ)) * ∑ i, s i) * L / n = (2 * v * L) / (n : ℝ) ^ 2 := by
        rw [hv]; field_simp
      rw [e, Real.sqrt_div (by positivity), Real.sqrt_sq hn0.le]
    rw [hsq] at hx
    rw [Finset.sum_sub_distrib]
    have e1 : (∑ i, m i) - ∑ i, x i
        = n * ((n : ℝ)⁻¹ * ∑ i, m i - (n : ℝ)⁻¹ * ∑ i, x i) := by field_simp
    have e2 : t = n * (Real.sqrt (2 * v * L) / n + L / (3 * n)) := by
      rw [ht]; field_simp
    rw [e1, e2]
    exact mul_lt_mul_of_pos_left (by linarith) hn0
  refine (measure_mono hsub).trans ?_
  rcases hv0.eq_or_lt with hv00 | hvpos
  · -- zero variance
    have hsz : ∀ i, s i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hs0 i)).1 hv00.symm i (Finset.mem_univ i)
    have hall : ∀ᵐ z ∂P, ∀ i, z i = m i := by
      refine ae_all_iff.2 (fun i => ?_)
      have h0 : ∫ y, (y - ∫ w, w ∂(μs i)) ^ 2 ∂(μs i) = 0 := hsz i
      have hI : Integrable (fun y : ℝ => (y - ∫ w, w ∂(μs i)) ^ 2) (μs i) :=
        ebsb_int (μs i) (hμs i) _ ((continuous_id.sub continuous_const).pow 2)
      rw [integral_eq_zero_iff_of_nonneg (fun y => sq_nonneg _) hI] at h0
      have h1 : ∀ᵐ y ∂(μs i), y = ∫ w, w ∂(μs i) := by
        filter_upwards [h0] with y hy
        have : (y - ∫ w, w ∂(μs i)) ^ 2 = 0 := hy
        have := (pow_eq_zero_iff two_ne_zero).1 this
        linarith
      exact (Measure.quasiMeasurePreserving_eval μs i).ae h1
    have hsub2 : {z : Fin n → ℝ | t < ∑ i, (m i - z i)} ⊆ {z | ¬ ∀ i, z i = m i} := by
      intro z hz
      simp only [Set.mem_setOf_eq] at hz ⊢
      intro hall'
      have : ∑ i, (m i - z i) = 0 := Finset.sum_eq_zero (fun i _ => by rw [hall' i]; ring)
      rw [this] at hz
      linarith
    exact (measure_mono hsub2).trans (by rw [ae_iff.1 hall]; exact zero_le)
  · -- positive variance
    set a : ℝ := Real.sqrt (2 * L / v) with ha
    have ha0 : 0 ≤ a := Real.sqrt_nonneg _
    have ha2 : a ^ 2 = 2 * L / v := Real.sq_sqrt (by positivity)
    have hva : v * a ^ 2 = 2 * L := by rw [ha2]; field_simp
    have hLv : L = v * a ^ 2 / 2 := by linarith
    have hsq2 : Real.sqrt (2 * v * L) = v * a := by
      have : 2 * v * L = (v * a) ^ 2 := by
        calc 2 * v * L = v * (2 * L) := by ring
          _ = v * (v * a ^ 2) := by rw [hva]
          _ = (v * a) ^ 2 := by ring
      rw [this, Real.sqrt_sq (mul_nonneg hvpos.le ha0)]
    set l : ℝ := a / (1 + a / 3) with hl
    have hl0 : 0 ≤ l := by positivity
    have hl3 : l < 3 := by
      rw [hl, div_lt_iff₀ (by positivity)]; linarith
    have htail := ebsb_tail μs hμs l hl0 hl3 t
    have hexp : -l * t + l ^ 2 / (2 * (1 - l / 3)) * ∑ i, ∫ y, (y - ∫ w, w ∂(μs i)) ^ 2 ∂(μs i)
        = -L := by
      have h := ebsb_alg v a hvpos ha0
      have e : t = v * a + (v * a ^ 2 / 2) / 3 := by rw [ht, hsq2, ← hLv]
      change -l * t + l ^ 2 / (2 * (1 - l / 3)) * v = -L
      rw [e, hLv]
      exact h
    rw [hexp] at htail
    have hexpL : Real.exp (-L) = δ := by
      rw [Real.exp_neg, hL, Real.exp_log (one_div_pos.2 hδ)]
      field_simp
    rw [hexpL] at htail
    have hsub3 : {z : Fin n → ℝ | t < ∑ i, (m i - z i)} ⊆
        {z | t ≤ ∑ i, ((∫ w, w ∂(μs i)) - z i)} := fun z hz => by
      simp only [Set.mem_setOf_eq] at hz ⊢
      exact le_of_lt hz
    refine (measure_mono hsub3).trans ?_
    rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hδ.le]
    exact htail
