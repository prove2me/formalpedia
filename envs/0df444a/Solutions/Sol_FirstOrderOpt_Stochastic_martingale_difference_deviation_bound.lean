-- Prove2me | solution 1 for FirstOrderOpt.Stochastic.martingale_difference_deviation_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T13:48:24.840847+00:00
-- url     : https://prove2.me/submissions/6c380b35-0b11-4743-8eac-c3397598a5c0

import Mathlib

namespace P87

lemma key_exp (u : ℝ) : Real.exp u ≤ u + Real.exp (9 * u ^ 2 / 16) := by
  have hv0 : 0 ≤ 9 * u ^ 2 / 16 := by positivity
  rcases le_or_gt u (-1) with h1 | h1
  · have he : Real.exp u ≤ 1 / 2 := by
      have := Real.exp_le_exp.2 h1
      have h2 : Real.exp (-1) ≤ 1 / 2 := by
        rw [Real.exp_neg]
        have := Real.exp_one_gt_d9
        rw [inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
        linarith
      linarith
    have := Real.add_one_le_exp (9 * u ^ 2 / 16)
    nlinarith [sq_nonneg (u + 8 / 9)]
  rcases le_or_gt u 0 with h2 | h2
  · have hb := Real.exp_bound (x := u) (by rw [abs_le]; constructor <;> linarith) (n := 4) (by norm_num)
    have habs : |u| = -u := abs_of_nonpos h2
    rw [habs] at hb
    have hb' := (abs_sub_le_iff.1 hb).1
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat] at hb'
    norm_num at hb'
    have := Real.add_one_le_exp (9 * u ^ 2 / 16)
    nlinarith [sq_nonneg u, mul_nonneg (neg_nonneg.2 h2) (sq_nonneg u), mul_nonneg (mul_nonneg (neg_nonneg.2 h2) (sq_nonneg u)) (by linarith : (0:ℝ) ≤ u + 1)]
  rcases le_or_gt u 1 with h3 | h3
  · have hb := Real.exp_bound' (x := u) h2.le h3 (n := 5) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat] at hb
    norm_num at hb
    have hl := Real.sum_le_exp_of_nonneg hv0 4
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hl
    norm_num at hl
    have hp : 0 ≤ 1 / 16 - u / 6 + (81 / 512 - 1 / 24) * u ^ 2 - u ^ 3 / 100 + 729 * u ^ 4 / 24576 := by
      nlinarith [sq_nonneg (u - 5 / 7), sq_nonneg (u ^ 2 - 1 / 2), mul_nonneg h2.le (sq_nonneg (u - 5 / 7)),
        mul_nonneg h2.le (by linarith : (0:ℝ) ≤ 1 - u)]
    nlinarith [mul_nonneg (sq_nonneg u) hp]
  rcases le_or_gt u (16 / 9) with h4 | h4
  · have ht0 : 0 ≤ u - 1 := by linarith
    have hb := Real.exp_bound' (x := u - 1) ht0 (by linarith) (n := 4) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat] at hb
    norm_num at hb
    have hl := Real.sum_le_exp_of_nonneg hv0 4
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hl
    norm_num at hl
    have he1 := Real.exp_one_lt_d9
    have hsplit : Real.exp u = Real.exp 1 * Real.exp (u - 1) := by
      rw [← Real.exp_add]; ring_nf
    have hpos : 0 ≤ Real.exp (u - 1) := (Real.exp_pos _).le
    have hA : Real.exp u ≤ 2.7182818286 * Real.exp (u - 1) := by
      rw [hsplit]; exact mul_le_mul_of_nonneg_right he1.le hpos
    nlinarith [mul_nonneg ht0 (by linarith : (0:ℝ) ≤ 16 / 9 - u), mul_nonneg ht0 ht0]
  · have : u ≤ 9 * u ^ 2 / 16 := by nlinarith
    have := Real.exp_le_exp.2 this
    linarith


lemma cvx (a y : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    Real.exp (a * y) ≤ Real.exp a * (1 - a) + a * Real.exp (a - 1) * Real.exp y := by
  have h := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (y - 1)) (by linarith : (0:ℝ) ≤ 1 - a) ha0
    (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
  have e1 : Real.exp (a * y) = Real.exp a * Real.exp (a * (y - 1)) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (a - 1) * Real.exp y = Real.exp a * Real.exp (y - 1) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  rw [e1, mul_assoc a, e2]
  have := Real.exp_pos a
  nlinarith

lemma mgf_pw (s σ : ℝ) (hσ : 0 < σ) : ∃ c0 A B : ℝ, 0 ≤ B ∧
    A + B * Real.exp 1 ≤ Real.exp (3 * s ^ 2 * σ ^ 2 / 4) ∧
    ∀ x : ℝ, Real.exp (s * x) ≤ c0 * x + A + B * Real.exp (x ^ 2 / σ ^ 2) := by
  have hσ2 : 0 < σ ^ 2 := by positivity
  set a := 9 * s ^ 2 * σ ^ 2 / 16 with ha
  have ha0 : 0 ≤ a := by positivity
  rcases le_or_gt a 1 with h1 | h1
  · refine ⟨s, Real.exp a * (1 - a), a * Real.exp (a - 1), by positivity, ?_, ?_⟩
    · have : Real.exp a * (1 - a) + a * Real.exp (a - 1) * Real.exp 1 = Real.exp a := by
        rw [mul_assoc, ← Real.exp_add]; ring_nf
      rw [this]; apply Real.exp_le_exp.2; rw [ha]; nlinarith [sq_nonneg s]
    · intro x
      have k := key_exp (s * x)
      have e : 9 * (s * x) ^ 2 / 16 = a * (x ^ 2 / σ ^ 2) := by
        rw [ha]; field_simp
      rw [e] at k
      have c := cvx a (x ^ 2 / σ ^ 2) ha0 h1
      linarith
  · refine ⟨0, Real.exp (3 * s ^ 2 * σ ^ 2 / 8) * (Real.exp (2/3) * (1 - 2/3)),
      Real.exp (3 * s ^ 2 * σ ^ 2 / 8) * ((2/3) * Real.exp (2/3 - 1)), by positivity, ?_, ?_⟩
    · have : Real.exp (3 * s ^ 2 * σ ^ 2 / 8) * (Real.exp (2/3) * (1 - 2/3)) +
          Real.exp (3 * s ^ 2 * σ ^ 2 / 8) * ((2/3) * Real.exp (2/3 - 1)) * Real.exp 1
          = Real.exp (3 * s ^ 2 * σ ^ 2 / 8 + 2 / 3) := by
        have e : Real.exp (2/3 - 1) * Real.exp 1 = Real.exp (2/3) := by
          rw [← Real.exp_add]; ring_nf
        rw [Real.exp_add]
        linear_combination (Real.exp (3 * s ^ 2 * σ ^ 2 / 8) * (2/3)) * e
      rw [this]; apply Real.exp_le_exp.2; rw [ha] at h1; nlinarith
    · intro x
      have hsx : s * x ≤ 3 * s ^ 2 * σ ^ 2 / 8 + 2 / 3 * (x ^ 2 / σ ^ 2) := by
        have : 0 ≤ (3 / 8) * (s * σ - (4 / 3) * x / σ) ^ 2 := by positivity
        have e : (3 / 8) * (s * σ - (4 / 3) * x / σ) ^ 2
            = 3 * s ^ 2 * σ ^ 2 / 8 + 2 / 3 * (x ^ 2 / σ ^ 2) - s * x := by
          field_simp; ring
        linarith
      have h2 := Real.exp_le_exp.2 hsx
      rw [Real.exp_add] at h2
      have c := cvx (2/3) (x ^ 2 / σ ^ 2) (by norm_num) (by norm_num)
      have hp := Real.exp_pos (3 * s ^ 2 * σ ^ 2 / 8)
      have := mul_le_mul_of_nonneg_left c hp.le
      nlinarith

open MeasureTheory

lemma cond_mgf {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    (hm : m ≤ mΩ) (ζ : Ω → ℝ) (σ s : ℝ) (hσ : 0 < σ) (hζm : Measurable ζ)
    (hi : Integrable ζ μ) (hi2 : Integrable (fun ω => Real.exp (ζ ω ^ 2 / σ ^ 2)) μ)
    (hmean : μ[ζ | m] =ᵐ[μ] 0)
    (htail : μ[(fun ω => Real.exp (ζ ω ^ 2 / σ ^ 2)) | m] ≤ᵐ[μ] fun _ => Real.exp 1) :
    Integrable (fun ω => Real.exp (s * ζ ω)) μ ∧
      μ[(fun ω => Real.exp (s * ζ ω)) | m] ≤ᵐ[μ] fun _ => Real.exp (3 * s ^ 2 * σ ^ 2 / 4) := by
  obtain ⟨c0, A, B, hB, hAB, hpw⟩ := mgf_pw s σ hσ
  set E : Ω → ℝ := fun ω => Real.exp (ζ ω ^ 2 / σ ^ 2) with hE
  set g : Ω → ℝ := (c0 • ζ + fun _ => A) + B • E with hg
  have hi1 : Integrable (c0 • ζ) μ := hi.smul c0
  have hiA : Integrable (fun _ : Ω => A) μ := integrable_const A
  have hiE : Integrable (B • E) μ := hi2.smul B
  have hgi : Integrable g μ := (hi1.add hiA).add hiE
  have hpt : ∀ ω, Real.exp (s * ζ ω) ≤ g ω := by
    intro ω; simp only [hg, hE, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; exact hpw (ζ ω)
  have hexpi : Integrable (fun ω => Real.exp (s * ζ ω)) μ := by
    refine Integrable.mono' hgi ((Real.measurable_exp.comp (hζm.const_mul s)).aestronglyMeasurable)
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hpt ω
  refine ⟨hexpi, ?_⟩
  have h1 := condExp_mono (m := m) hexpi hgi (ae_of_all _ hpt)
  have h2 := condExp_add (m := m) (hi1.add hiA) hiE
  have h3 := condExp_add (m := m) hi1 hiA
  have h4 := condExp_smul (μ := μ) c0 ζ m
  have h5 := condExp_smul (μ := μ) B E m
  have h6 := condExp_const (μ := μ) hm A
  filter_upwards [h1, h2, h3, h4, h5, hmean, htail] with ω e1 e2 e3 e4 e5 e6 e7
  rw [e2] at e1
  simp only [Pi.add_apply] at e1
  rw [e3, e5] at e1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1
  rw [e4, h6] at e1
  simp only [Pi.smul_apply, smul_eq_mul, e6, Pi.zero_apply, mul_zero, zero_add] at e1
  have : B * μ[E | m] ω ≤ B * Real.exp 1 := mul_le_mul_of_nonneg_left e7 hB
  linarith

lemma step {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    (hm : m ≤ mΩ) {X Y : Ω → ℝ} (hX0 : ∀ ω, 0 ≤ X ω) (hXm : Measurable[m] X)
    (hXi : Integrable X μ) (hY0 : ∀ ω, 0 ≤ Y ω) (hYi : Integrable Y μ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : μ[Y | m] ≤ᵐ[μ] fun _ => C) :
    Integrable (fun ω => X ω * Y ω) μ ∧ ∫ ω, X ω * Y ω ∂μ ≤ C * ∫ ω, X ω ∂μ := by
  set f : ℕ → Ω → ℝ := fun K ω => min (X ω) K with hf
  have hfm : ∀ K, StronglyMeasurable[m] (f K) := fun K =>
    (hXm.min measurable_const).stronglyMeasurable
  have hf0 : ∀ K ω, 0 ≤ f K ω := fun K ω => le_min (hX0 ω) (Nat.cast_nonneg K)
  have hfle : ∀ K ω, f K ω ≤ X ω := fun K ω => min_le_left _ _
  have hfK : ∀ K ω, f K ω ≤ K := fun K ω => min_le_right _ _
  have hXmeas : Measurable X := hXm.mono hm le_rfl
  have hint : ∀ K : ℕ, Integrable (fun ω => f K ω * Y ω) μ := fun K =>
    hYi.bdd_mul ((hfm K).mono hm).aestronglyMeasurable (c := K)
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (hf0 K ω)]; exact hfK K ω)
  have hbound : ∀ K : ℕ, ∫ ω, f K ω * Y ω ∂μ ≤ C * ∫ ω, X ω ∂μ := by
    intro K
    have h1 : μ[f K * Y | m] =ᵐ[μ] f K * μ[Y | m] :=
      condExp_stronglyMeasurable_mul_of_bound hm (hfm K) hYi K
        (ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (hf0 K ω)]; exact hfK K ω)
    have h2 : ∫ ω, f K ω * Y ω ∂μ = ∫ ω, (f K * μ[Y | m]) ω ∂μ := by
      have := integral_condExp (μ := μ) (f := f K * Y) hm
      rw [← integral_congr_ae h1, this]; rfl
    have hi3 : Integrable (f K * μ[Y | m]) μ := (integrable_condExp (f := f K * Y)).congr h1
    rw [h2]
    calc ∫ ω, (f K * μ[Y | m]) ω ∂μ ≤ ∫ ω, C * X ω ∂μ := by
          refine integral_mono_ae hi3 (hXi.const_mul C) ?_
          filter_upwards [hC] with ω hω
          simp only [Pi.mul_apply]
          calc f K ω * μ[Y | m] ω ≤ f K ω * C := mul_le_mul_of_nonneg_left hω (hf0 K ω)
            _ ≤ X ω * C := mul_le_mul_of_nonneg_right (hfle K ω) hC0
            _ = C * X ω := mul_comm _ _
      _ = C * ∫ ω, X ω ∂μ := integral_const_mul C _
  have hlim : ∫⁻ ω, ENNReal.ofReal (X ω * Y ω) ∂μ
      = ⨆ K : ℕ, ∫⁻ ω, ENNReal.ofReal (f K ω * Y ω) ∂μ := by
    rw [← lintegral_iSup' (fun K => (hint K).aemeasurable.ennreal_ofReal)
      (ae_of_all _ fun ω K L hKL => ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (min_le_min_left _ (Nat.cast_le.2 hKL)) (hY0 ω)))]
    congr 1; ext ω
    apply le_antisymm
    · obtain ⟨K, hK⟩ := exists_nat_ge (X ω)
      refine le_iSup_of_le K ?_
      simp only [hf, min_eq_left hK, le_refl]
    · exact iSup_le fun K => ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (hfle K ω) (hY0 ω))
  have hle : ∫⁻ ω, ENNReal.ofReal (X ω * Y ω) ∂μ ≤ ENNReal.ofReal (C * ∫ ω, X ω ∂μ) := by
    rw [hlim]; refine iSup_le fun K => ?_
    rw [← ofReal_integral_eq_lintegral_ofReal (hint K)
      (ae_of_all _ fun ω => mul_nonneg (hf0 K ω) (hY0 ω))]
    exact ENNReal.ofReal_le_ofReal (hbound K)
  have hXY0 : 0 ≤ᵐ[μ] fun ω => X ω * Y ω := ae_of_all _ fun ω => mul_nonneg (hX0 ω) (hY0 ω)
  have hInt : Integrable (fun ω => X ω * Y ω) μ :=
    ⟨hXmeas.aestronglyMeasurable.mul hYi.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal hXY0).2 (lt_of_le_of_lt hle ENNReal.ofReal_lt_top)⟩
  refine ⟨hInt, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hXY0 hInt.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg hC0 (integral_nonneg hX0)) hle

end P87

open MeasureTheory in
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (𝓕 : Filtration ℕ mΩ) (ζ : ℕ → Ω → ℝ) (σ : ℕ → ℝ)
    (hσ : ∀ t, 0 < σ t)
    (hadapt : ∀ t, Measurable[𝓕 t] (ζ t))
    (hintmean : ∀ t, 1 ≤ t → Integrable (ζ t) μ)
    (hinttail : ∀ t, 1 ≤ t → Integrable (fun ω => Real.exp ((ζ t ω) ^ 2 / (σ t) ^ 2)) μ)
    (hmean : ∀ t, 1 ≤ t → (μ[ζ t | 𝓕 (t - 1)]) =ᵐ[μ] 0)
    (htail : ∀ t, 1 ≤ t →
      (μ[(fun ω => Real.exp ((ζ t ω) ^ 2 / (σ t) ^ 2)) | 𝓕 (t - 1)])
        ≤ᵐ[μ] (fun _ => Real.exp 1))
    (N : ℕ) (hN : 1 ≤ N) (lam : ℝ) (hlam : 0 ≤ lam) :
    (μ {ω | lam * Real.sqrt (∑ t ∈ Finset.Icc 1 N, (σ t) ^ 2) < ∑ t ∈ Finset.Icc 1 N, ζ t ω}).toReal
      ≤ Real.exp (-(lam ^ 2) / 3) := by
  have hζmeas : ∀ t, Measurable (ζ t) := fun t => (hadapt t).mono (𝓕.le t) le_rfl
  have hVpos : 0 < ∑ t ∈ Finset.Icc 1 N, (σ t) ^ 2 :=
    Finset.sum_pos (fun t _ => pow_pos (hσ t) 2) ⟨1, Finset.mem_Icc.2 ⟨le_rfl, hN⟩⟩
  set V := ∑ t ∈ Finset.Icc 1 N, (σ t) ^ 2 with hV
  set r := Real.sqrt V with hrdef
  have hr : 0 < r := Real.sqrt_pos.2 hVpos
  have hr2 : r ^ 2 = V := Real.sq_sqrt hVpos.le
  set s := 2 * lam / (3 * r) with hsdef
  have hs : 0 ≤ s := by positivity
  have key : ∀ n : ℕ, Integrable (fun ω => Real.exp (s * ∑ t ∈ Finset.Icc 1 n, ζ t ω)) μ ∧
      ∫ ω, Real.exp (s * ∑ t ∈ Finset.Icc 1 n, ζ t ω) ∂μ
        ≤ Real.exp (3 * s ^ 2 * (∑ t ∈ Finset.Icc 1 n, (σ t) ^ 2) / 4) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hmeasS : Measurable[𝓕 n] (fun ω => ∑ t ∈ Finset.Icc 1 n, ζ t ω) :=
        Finset.measurable_sum _ (fun t ht =>
          (hadapt t).mono (𝓕.mono (Finset.mem_Icc.1 ht).2) le_rfl)
      have hmeasX : Measurable[𝓕 n] (fun ω => Real.exp (s * ∑ t ∈ Finset.Icc 1 n, ζ t ω)) :=
        Real.measurable_exp.comp (hmeasS.const_mul s)
      have hsub : n + 1 - 1 = n := by omega
      have hm1 := hmean (n + 1) (by omega)
      rw [hsub] at hm1
      have ht1 := htail (n + 1) (by omega)
      rw [hsub] at ht1
      obtain ⟨hYi, hYc⟩ := P87.cond_mgf (𝓕.le n) (ζ (n + 1)) (σ (n + 1)) s (hσ _) (hζmeas _)
        (hintmean _ (by omega)) (hinttail _ (by omega)) hm1 ht1
      obtain ⟨hI, hB⟩ := P87.step (𝓕.le n) (fun ω => (Real.exp_pos _).le) hmeasX ih.1
        (fun ω => (Real.exp_pos _).le) hYi (Real.exp_pos _).le hYc
      have hfun : (fun ω => Real.exp (s * ∑ t ∈ Finset.Icc 1 (n + 1), ζ t ω))
          = fun ω => Real.exp (s * ∑ t ∈ Finset.Icc 1 n, ζ t ω) * Real.exp (s * ζ (n + 1) ω) := by
        ext ω; rw [Finset.sum_Icc_succ_top (by omega), mul_add, Real.exp_add]
      rw [hfun, Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
      refine ⟨hI, hB.trans ?_⟩
      calc Real.exp (3 * s ^ 2 * σ (n + 1) ^ 2 / 4)
            * ∫ ω, Real.exp (s * ∑ t ∈ Finset.Icc 1 n, ζ t ω) ∂μ
          ≤ Real.exp (3 * s ^ 2 * σ (n + 1) ^ 2 / 4)
            * Real.exp (3 * s ^ 2 * (∑ t ∈ Finset.Icc 1 n, (σ t) ^ 2) / 4) :=
            mul_le_mul_of_nonneg_left ih.2 (Real.exp_pos _).le
        _ = Real.exp (3 * s ^ 2 * (∑ t ∈ Finset.Icc 1 n, (σ t) ^ 2 + σ (n + 1) ^ 2) / 4) := by
            rw [← Real.exp_add]; ring_nf
  obtain ⟨hI, hB⟩ := key N
  have hsubset : {ω | lam * r < ∑ t ∈ Finset.Icc 1 N, ζ t ω}
      ⊆ {ω | Real.exp (s * (lam * r)) ≤ Real.exp (s * ∑ t ∈ Finset.Icc 1 N, ζ t ω)} :=
    fun ω hω => Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (le_of_lt hω) hs)
  have hM := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun ω => (Real.exp_pos _).le) hI
    (Real.exp (s * (lam * r)))
  have hexpo : -(s * (lam * r)) + 3 * s ^ 2 * V / 4 = -(lam ^ 2) / 3 := by
    rw [hsdef, ← hr2]; field_simp; ring
  change μ.real _ ≤ _
  calc μ.real {ω | lam * r < ∑ t ∈ Finset.Icc 1 N, ζ t ω}
      ≤ μ.real {ω | Real.exp (s * (lam * r)) ≤ Real.exp (s * ∑ t ∈ Finset.Icc 1 N, ζ t ω)} :=
        measureReal_mono hsubset
    _ = Real.exp (-(s * (lam * r))) * (Real.exp (s * (lam * r)) *
          μ.real {ω | Real.exp (s * (lam * r)) ≤ Real.exp (s * ∑ t ∈ Finset.Icc 1 N, ζ t ω)}) := by
        rw [← mul_assoc (Real.exp (-(s * (lam * r)))), ← Real.exp_add, neg_add_cancel,
          Real.exp_zero, one_mul]
    _ ≤ Real.exp (-(s * (lam * r))) * Real.exp (3 * s ^ 2 * V / 4) :=
        mul_le_mul_of_nonneg_left (hM.trans hB) (Real.exp_pos _).le
    _ = Real.exp (-(lam ^ 2) / 3) := by rw [← Real.exp_add, hexpo]
