-- Prove2me | solution 1 for FractionalCalc.fractional_oscillator_solution
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T07:59:29.395445+00:00
-- url     : https://prove2.me/submissions/073ca1f5-4291-4aea-9ecf-73cf60c8b5af

import Mathlib
import Definitions.Def_FractionalCalc_rlIntegral
import Definitions.Def_FractionalCalc_caputoDeriv
import Definitions.Def_FractionalCalc_mittagLeffler
open MeasureTheory Set Classical
open FractionalCalc
set_option autoImplicit false

private lemma fc5_summ (α β r : ℝ) (hα : 1 ≤ α) (hr : 0 ≤ r) :
    Summable (fun k : ℕ => r ^ k / |Real.Gamma (α * k + β)|) := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 2 - β ≤ N := exists_nat_ge _
  rw [← summable_nat_add_iff N]
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    ((Real.summable_pow_div_factorial r).mul_left (r ^ N))
  have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have hle : (k:ℝ) + 2 ≤ α * ((k + N : ℕ) : ℝ) + β := by
    push_cast; nlinarith
  have h2 : (k:ℝ) + 2 ∈ Ici (2:ℝ) := by simp
  have h2' : α * ((k + N : ℕ) : ℝ) + β ∈ Ici (2:ℝ) := by simp only [mem_Ici]; linarith
  have hmono := Real.Gamma_strictMonoOn_Ici.monotoneOn h2 h2' hle
  have hfact : Real.Gamma ((k:ℝ) + 2) = ((k + 1).factorial : ℝ) := by
    rw [← Real.Gamma_nat_eq_factorial]; push_cast; ring_nf
  have hkf : ((k.factorial : ℕ) : ℝ) ≤ ((k + 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (Nat.le_succ k)
  have hkpos : (0:ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hG : (k.factorial : ℝ) ≤ |Real.Gamma (α * ((k + N : ℕ) : ℝ) + β)| := by
    rw [abs_of_pos (by linarith)]; linarith
  rw [pow_add, mul_comm (r ^ k) (r ^ N), mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by positivity) hkpos hG) (by positivity)

private lemma fc5_beta (μ e T : ℝ) (hμ : 0 < μ) (he : -1 < e) (hT : 0 < T) :
    ∫ s in Ioo 0 T, (T - s) ^ (μ - 1) * s ^ e
      = Real.Gamma μ * Real.Gamma (e + 1) / Real.Gamma (e + 1 + μ) * T ^ (e + μ) := by
  have hc := Complex.betaIntegral_scaled ((e:ℂ) + 1) (μ:ℂ) hT
  have hG := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := (e:ℂ) + 1) (t := (μ:ℂ))
    (by simp; linarith) (by simpa using hμ)
  have h1 : (∫ x in (0:ℝ)..T, (x : ℂ) ^ ((e:ℂ) + 1 - 1) * ((T : ℂ) - x) ^ ((μ:ℂ) - 1))
      = ((∫ s in Ioo 0 T, (T - s) ^ (μ - 1) * s ^ e : ℝ) : ℂ) := by
    rw [intervalIntegral.integral_of_le hT.le, ← integral_Ioc_eq_integral_Ioo, ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioc (fun x hx => ?_)
    rw [Complex.ofReal_mul, Complex.ofReal_cpow hx.1.le,
      Complex.ofReal_cpow (by linarith [hx.2] : (0:ℝ) ≤ T - x)]
    push_cast; ring_nf
  have hpos : 0 < Real.Gamma (e + 1 + μ) := Real.Gamma_pos_of_pos (by linarith)
  apply Complex.ofReal_injective
  rw [← h1, hc]
  have hG' : Complex.Gamma ((e:ℂ) + 1 + μ) ≠ 0 := by
    have := Complex.Gamma_ofReal (e + 1 + μ); push_cast at this; rw [this]
    exact_mod_cast hpos.ne'
  have hB : Complex.betaIntegral ((e:ℂ) + 1) (μ:ℂ)
      = Complex.Gamma ((e:ℂ) + 1) * Complex.Gamma μ / Complex.Gamma ((e:ℂ) + 1 + μ) := by
    rw [hG]; field_simp
  rw [hB]
  have e1 := Complex.Gamma_ofReal (e + 1)
  have e2 := Complex.Gamma_ofReal μ
  have e3 := Complex.Gamma_ofReal (e + 1 + μ)
  push_cast at e1 e2 e3
  rw [e1, e2, e3, Complex.ofReal_mul, Complex.ofReal_cpow hT.le]
  push_cast
  ring_nf

private noncomputable def fc5_h (e t : ℝ) : ℝ := t ^ e / Real.Gamma (e + 1)

private noncomputable def fc5_G (α c b t : ℝ) : ℝ := ∑' k : ℕ, c ^ k * fc5_h (α * k + b) t

private lemma fc5_h_deriv (e t : ℝ) (ht : 0 < t) : HasDerivAt (fc5_h e) (fc5_h (e - 1) t) t := by
  have hd := (Real.hasDerivAt_rpow_const (p := e) (Or.inl ht.ne')).div_const (Real.Gamma (e + 1))
  have hf : fc5_h e = fun x => x ^ e / Real.Gamma (e + 1) := rfl
  rw [hf]
  refine hd.congr_deriv ?_
  unfold fc5_h
  rw [sub_add_cancel]
  by_cases he : e = 0
  · subst he; simp [Real.Gamma_zero]
  · rw [Real.Gamma_add_one he]
    by_cases hg : Real.Gamma e = 0
    · simp [hg]
    · field_simp

private lemma fc5_term_abs (α c b t : ℝ) (ht : 0 < t) (k : ℕ) :
    |c ^ k * fc5_h (α * k + b) t|
      = t ^ b * ((|c| * t ^ α) ^ k / |Real.Gamma (α * k + (b + 1))|) := by
  unfold fc5_h
  rw [abs_mul, abs_div, abs_pow, abs_of_pos (Real.rpow_pos_of_pos ht _), Real.rpow_add ht,
    mul_pow, ← Real.rpow_natCast (t ^ α), ← Real.rpow_mul ht.le, add_assoc]
  ring

private lemma fc5_G_summable (α c b t : ℝ) (hα : 1 ≤ α) (ht : 0 < t) :
    Summable (fun k : ℕ => c ^ k * fc5_h (α * k + b) t) := by
  rw [← summable_abs_iff]
  simp_rw [fc5_term_abs α c b t ht]
  exact (fc5_summ α (b + 1) _ hα (by positivity)).mul_left _

private lemma fc5_rpow_le (y s e : ℝ) (hs : 0 < s) (hy : y ∈ Ioo (s / 2) (2 * s)) :
    y ^ e ≤ (s / 2) ^ e + (2 * s) ^ e := by
  have hy0 : 0 < y := by linarith [hy.1]
  rcases le_or_gt 0 e with he | he
  · have := Real.rpow_le_rpow hy0.le hy.2.le he
    have : 0 ≤ (s / 2) ^ e := by positivity
    linarith
  · have := Real.rpow_le_rpow_of_nonpos (by positivity) hy.1.le he.le
    have : 0 ≤ (2 * s) ^ e := by positivity
    linarith

private lemma fc5_G_deriv (α c b s : ℝ) (hα : 1 ≤ α) (hs : 0 < s) :
    HasDerivAt (fc5_G α c b) (fc5_G α c (b - 1) s) s := by
  have hmem : s ∈ Ioo (s / 2) (2 * s) := ⟨by linarith, by linarith⟩
  have key := hasDerivAt_tsum_of_isPreconnected
    (u := fun k : ℕ => ((s / 2) ^ (b - 1) + (2 * s) ^ (b - 1)) *
      ((|c| * (2 * s) ^ α) ^ k / |Real.Gamma (α * k + (b - 1 + 1))|))
    (g := fun (k : ℕ) (t : ℝ) => c ^ k * fc5_h (α * k + b) t)
    (g' := fun (k : ℕ) (t : ℝ) => c ^ k * fc5_h (α * k + (b - 1)) t)
    (t := Ioo (s / 2) (2 * s)) (y₀ := s) (y := s)
    ((fc5_summ α _ _ hα (by positivity)).mul_left _) isOpen_Ioo isPreconnected_Ioo
    (fun k y hy => by
      have hy0 : 0 < y := by linarith [hy.1]
      have := (fc5_h_deriv (α * k + b) y hy0).const_mul (c ^ k)
      rw [show α * k + b - 1 = α * k + (b - 1) by ring] at this
      exact this)
    (fun k y hy => by
      have hy0 : 0 < y := by linarith [hy.1]
      rw [Real.norm_eq_abs, fc5_term_abs α c (b - 1) y hy0 k]
      apply mul_le_mul (fc5_rpow_le y s _ hs hy) _ (by positivity) (by positivity)
      apply div_le_div_of_nonneg_right _ (abs_nonneg _)
      apply pow_le_pow_left₀ (by positivity)
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hy0.le hy.2.le (by linarith))
        (abs_nonneg _))
    hmem (fc5_G_summable α c b s hα hs) hmem
  exact key

private lemma fc5_G_shift (α c b t : ℝ) (hα : 1 ≤ α) (ht : 0 < t)
    (h0 : Real.Gamma (b + 1) = 0) :
    fc5_G α c b t = c * fc5_G α c (b + α) t := by
  unfold fc5_G
  rw [(fc5_G_summable α c b t hα ht).tsum_eq_zero_add, ← tsum_mul_left]
  have : c ^ 0 * fc5_h (α * ((0 : ℕ) : ℝ) + b) t = 0 := by
    simp [fc5_h, h0]
  rw [this, zero_add]
  congr 1; funext k
  rw [pow_succ]; push_cast
  rw [show α * (k + 1) + b = α * k + (b + α) by ring]
  ring

private lemma fc5_h_nonneg (e t : ℝ) (he : -1 < e) (ht : 0 < t) : 0 ≤ fc5_h e t :=
  div_nonneg (Real.rpow_nonneg ht.le _) (Real.Gamma_pos_of_pos (by linarith)).le

private lemma fc5_hint (μ e T : ℝ) (hμ : 0 < μ) (he : -1 < e) (hT : 0 < T) :
    ∫ s in Ioo 0 T, (T - s) ^ (μ - 1) * fc5_h e s = Real.Gamma μ * fc5_h (e + μ) T := by
  unfold fc5_h
  simp_rw [mul_div_assoc']
  rw [integral_div, fc5_beta μ e T hμ he hT]
  have h1 : 0 < Real.Gamma (e + 1) := Real.Gamma_pos_of_pos (by linarith)
  have h2 : 0 < Real.Gamma (e + 1 + μ) := Real.Gamma_pos_of_pos (by linarith)
  rw [show e + μ + 1 = e + 1 + μ by ring]
  field_simp

private lemma fc5_hint_int (μ e T : ℝ) (hμ : 0 < μ) (he : -1 < e) (hT : 0 < T) :
    IntegrableOn (fun s => (T - s) ^ (μ - 1) * fc5_h e s) (Ioo 0 T) := by
  apply Integrable.of_integral_ne_zero
  rw [fc5_hint μ e T hμ he hT]
  exact (mul_pos (Real.Gamma_pos_of_pos hμ)
    (div_pos (Real.rpow_pos_of_pos hT _) (Real.Gamma_pos_of_pos (by linarith)))).ne'

private lemma fc5_rl (α c μ b b' p q T : ℝ) (hα : 1 ≤ α) (hμ : 0 < μ) (hb : -1 < b)
    (hb' : -1 < b') (hT : 0 < T) :
    ∫ s in Ioo 0 T, (T - s) ^ (μ - 1) * (p * fc5_G α c b s + q * fc5_G α c b' s)
      = Real.Gamma μ * (p * fc5_G α c (b + μ) T + q * fc5_G α c (b' + μ) T) := by
  have hexp : ∀ (k : ℕ) (d : ℝ), -1 < d → -1 < α * k + d := fun k d hd => by
    have : 0 ≤ α * k := by positivity
    linarith
  set F : ℕ → ℝ → ℝ := fun k s =>
    (p * c ^ k) * ((T - s) ^ (μ - 1) * fc5_h (α * k + b) s)
      + (q * c ^ k) * ((T - s) ^ (μ - 1) * fc5_h (α * k + b') s) with hF
  have hFint : ∀ k, Integrable (F k) (volume.restrict (Ioo 0 T)) := fun k =>
    ((fc5_hint_int μ _ T hμ (hexp k b hb) hT).const_mul _).add
      ((fc5_hint_int μ _ T hμ (hexp k b' hb') hT).const_mul _)
  have hFval : ∀ k : ℕ, ∫ s in Ioo 0 T, F k s = Real.Gamma μ *
      (p * (c ^ k * fc5_h (α * k + (b + μ)) T) + q * (c ^ k * fc5_h (α * k + (b' + μ)) T)) := by
    intro k
    rw [hF, integral_add ((fc5_hint_int μ _ T hμ (hexp k b hb) hT).const_mul _)
      ((fc5_hint_int μ _ T hμ (hexp k b' hb') hT).const_mul _), integral_const_mul,
      integral_const_mul, fc5_hint μ _ T hμ (hexp k b hb) hT,
      fc5_hint μ _ T hμ (hexp k b' hb') hT, ← add_assoc, ← add_assoc]
    ring
  have hnorm : ∀ k : ℕ, ∫ s in Ioo 0 T, ‖F k s‖ ≤ Real.Gamma μ *
      (|p| * (|c| ^ k * fc5_h (α * k + (b + μ)) T)
        + |q| * (|c| ^ k * fc5_h (α * k + (b' + μ)) T)) := by
    intro k
    have hI1 := fc5_hint_int μ _ T hμ (hexp k b hb) hT
    have hI2 := fc5_hint_int μ _ T hμ (hexp k b' hb') hT
    calc ∫ s in Ioo 0 T, ‖F k s‖
        ≤ ∫ s in Ioo 0 T, ((|p| * |c| ^ k) * ((T - s) ^ (μ - 1) * fc5_h (α * k + b) s)
          + (|q| * |c| ^ k) * ((T - s) ^ (μ - 1) * fc5_h (α * k + b') s)) := by
          refine setIntegral_mono_on (hFint k).norm ((hI1.const_mul _).add (hI2.const_mul _))
            measurableSet_Ioo (fun s hs => ?_)
          have hs0 : 0 < s := hs.1
          have hA : 0 ≤ (T - s) ^ (μ - 1) := Real.rpow_nonneg (by linarith [hs.2]) _
          have h1 := fc5_h_nonneg _ s (hexp k b hb) hs0
          have h2 := fc5_h_nonneg _ s (hexp k b' hb') hs0
          rw [hF, Real.norm_eq_abs]
          refine (abs_add_le _ _).trans (le_of_eq ?_)
          simp only [abs_mul, abs_pow, abs_of_nonneg hA, abs_of_nonneg h1, abs_of_nonneg h2]
      _ = _ := by
          rw [integral_add (hI1.const_mul _) (hI2.const_mul _), integral_const_mul,
            integral_const_mul, fc5_hint μ _ T hμ (hexp k b hb) hT,
            fc5_hint μ _ T hμ (hexp k b' hb') hT, ← add_assoc, ← add_assoc]
          ring
  have hsum : Summable (fun k : ℕ => ∫ s in Ioo 0 T, ‖F k s‖) := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg (fun _ => norm_nonneg _)) hnorm ?_
    exact ((((fc5_G_summable α |c| (b + μ) T hα hT).mul_left |p|).add
      ((fc5_G_summable α |c| (b' + μ) T hα hT).mul_left |q|)).mul_left _)
  have hpt : ∀ s ∈ Ioo 0 T, (T - s) ^ (μ - 1) * (p * fc5_G α c b s + q * fc5_G α c b' s)
      = ∑' k, F k s := by
    intro s hs
    have h1 := ((fc5_G_summable α c b s hα hs.1).hasSum.mul_left (p * (T - s) ^ (μ - 1)))
    have h2 := ((fc5_G_summable α c b' s hα hs.1).hasSum.mul_left (q * (T - s) ^ (μ - 1)))
    rw [((h1.add h2).congr_fun (fun k => by rw [hF]; ring)).tsum_eq]
    unfold fc5_G; ring
  rw [setIntegral_congr_fun measurableSet_Ioo hpt,
    ← integral_tsum_of_summable_integral_norm hFint hsum]
  simp_rw [hFval]
  have h1 := (fc5_G_summable α c (b + μ) T hα hT).hasSum.mul_left p
  have h2 := (fc5_G_summable α c (b' + μ) T hα hT).hasSum.mul_left q
  rw [((h1.add h2).mul_left (Real.Gamma μ)).tsum_eq]
  rfl

private lemma fc5_ml_bound (α β L : ℝ) (hα : 1 ≤ α) (hL : 0 ≤ L) :
    ∃ M, ∀ z : ℝ, |z| ≤ L → |mittagLeffler α β z - (Real.Gamma β)⁻¹| ≤ M * |z| := by
  refine ⟨∑' k : ℕ, L ^ k / |Real.Gamma (α * k + (α + β))|, fun z hz => ?_⟩
  have hs : Summable (fun k : ℕ => z ^ k / Real.Gamma (α * k + β)) := by
    rw [← summable_abs_iff]
    refine (fc5_summ α β |z| hα (abs_nonneg z)).congr (fun k => ?_)
    rw [abs_div, abs_pow]
  unfold mittagLeffler
  rw [hs.tsum_eq_zero_add]
  simp only [pow_zero, Nat.cast_zero, mul_zero, zero_add, one_div, add_sub_cancel_left]
  have hS2 : Summable (fun k : ℕ => |z| ^ k / |Real.Gamma (α * k + (α + β))|) :=
    fc5_summ α _ |z| hα (abs_nonneg z)
  have hterm : ∀ k : ℕ, |z ^ (k + 1) / Real.Gamma (α * ((k + 1 : ℕ) : ℝ) + β)|
      = |z| * (|z| ^ k / |Real.Gamma (α * k + (α + β))|) := by
    intro k
    rw [abs_div, abs_pow, pow_succ]; push_cast
    rw [show α * (k + 1) + β = α * k + (α + β) by ring]; ring
  calc |∑' k : ℕ, z ^ (k + 1) / Real.Gamma (α * ((k + 1 : ℕ) : ℝ) + β)|
      ≤ ∑' k : ℕ, |z ^ (k + 1) / Real.Gamma (α * ((k + 1 : ℕ) : ℝ) + β)| := by
        have hsa : Summable (fun k : ℕ => |z ^ (k + 1) / Real.Gamma (α * ((k + 1 : ℕ) : ℝ) + β)|) := by
          simp_rw [hterm]; exact hS2.mul_left _
        exact norm_tsum_le_tsum_norm (f := fun k : ℕ =>
          z ^ (k + 1) / Real.Gamma (α * ((k + 1 : ℕ) : ℝ) + β)) hsa
    _ = |z| * ∑' k : ℕ, |z| ^ k / |Real.Gamma (α * k + (α + β))| := by
        simp_rw [hterm]; rw [tsum_mul_left]
    _ ≤ |z| * ∑' k : ℕ, L ^ k / |Real.Gamma (α * k + (α + β))| := by
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg z)
        refine hS2.tsum_le_tsum (fun k => ?_) (fc5_summ α _ L hα hL)
        exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg z) hz k) (abs_nonneg _)
    _ = _ := by ring

private lemma fc5_hasDerivAt_zero (α c x0 x1 : ℝ) (hα : 1 < α) :
    HasDerivAt (fun t => x0 * mittagLefflerOne α (c * t ^ α)
      + x1 * t * mittagLeffler α 2 (c * t ^ α)) x1 0 := by
  obtain ⟨M1, hM1⟩ := fc5_ml_bound α 1 |c| hα.le (abs_nonneg c)
  obtain ⟨M2, hM2⟩ := fc5_ml_bound α 2 |c| hα.le (abs_nonneg c)
  set f := fun t => x0 * mittagLefflerOne α (c * t ^ α) + x1 * t * mittagLeffler α 2 (c * t ^ α)
    with hf
  have hα0 : α ≠ 0 := by linarith
  have hf0 : f 0 = x0 := by
    have h1 : mittagLeffler α 1 0 = 1 := by
      unfold mittagLeffler
      rw [tsum_eq_single 0 (fun k hk => by simp [zero_pow hk])]
      simp
    simp [hf, Real.zero_rpow hα0, mittagLefflerOne, h1]
  set K := |x0| * |M1| * |c| + |x1| * |M2| * |c| with hK
  have hbound : ∀ t : ℝ, |t| ≤ 1 → ‖f t - f 0 - (t - 0) • x1‖ ≤ K * ‖|t| ^ α‖ := by
    intro t ht
    have hta : |t ^ α| ≤ |t| ^ α := Real.abs_rpow_le_abs_rpow t α
    have hta1 : |t| ^ α ≤ 1 := Real.rpow_le_one (abs_nonneg t) ht (by linarith)
    have hz : |c * t ^ α| ≤ |c| * |t| ^ α := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hta (abs_nonneg c)
    have hz1 : |c * t ^ α| ≤ |c| := hz.trans (by nlinarith [abs_nonneg c])
    have e1 := hM1 _ hz1
    have e2 := hM2 _ hz1
    rw [Real.Gamma_one, inv_one] at e1
    rw [Real.Gamma_two, inv_one] at e2
    have hexpr : f t - f 0 - (t - 0) • x1 = x0 * (mittagLeffler α 1 (c * t ^ α) - 1)
        + x1 * t * (mittagLeffler α 2 (c * t ^ α) - 1) := by
      rw [hf0]; simp only [hf, mittagLefflerOne, smul_eq_mul]; ring
    rw [hexpr, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg t) α)]
    have hA : |x0 * (mittagLeffler α 1 (c * t ^ α) - 1)| ≤ |x0| * (|M1| * (|c| * |t| ^ α)) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (e1.trans (mul_le_mul (le_abs_self M1) hz (abs_nonneg _)
        (abs_nonneg _))) (abs_nonneg x0)
    have hB : |x1 * t * (mittagLeffler α 2 (c * t ^ α) - 1)|
        ≤ |x1| * 1 * (|M2| * (|c| * |t| ^ α)) := by
      rw [abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul_of_nonneg_left ht (abs_nonneg _))
        (e2.trans (mul_le_mul (le_abs_self M2) hz (abs_nonneg _) (abs_nonneg _)))
        (abs_nonneg _) (by positivity)
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ |x0| * (|M1| * (|c| * |t| ^ α)) + |x1| * 1 * (|M2| * (|c| * |t| ^ α)) :=
          add_le_add hA hB
      _ = K * |t| ^ α := by rw [hK]; ring
  rw [hasDerivAt_iff_isLittleO]
  have hO : (fun t => f t - f 0 - (t - 0) • x1) =O[nhds 0] (fun t => |t| ^ α) :=
    Asymptotics.IsBigO.of_bound K (by
      filter_upwards [Metric.closedBall_mem_nhds (0:ℝ) one_pos] with t ht
      apply hbound; simpa using ht)
  have hlo : (fun t : ℝ => |t| ^ α) =o[nhds 0] (fun t => t - 0) := by
    have hT : Filter.Tendsto (fun t : ℝ => |t| ^ (α - 1)) (nhds 0) (nhds 0) := by
      have h := (continuous_abs.tendsto (0:ℝ)).rpow_const (p := α - 1) (Or.inr (by linarith))
      simpa [Real.zero_rpow (by linarith : α - 1 ≠ 0)] using h
    have h1 := (Asymptotics.isLittleO_one_iff ℝ).mpr hT
    have h2 : (fun t : ℝ => |t|) =O[nhds 0] (fun t => t - 0) :=
      Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun t => by simp)
    refine (h1.mul_isBigO h2).congr (fun t => ?_) (fun t => one_mul _)
    have := Real.rpow_add' (abs_nonneg t) (show (α - 1) + 1 ≠ 0 by linarith)
    rw [sub_add_cancel, Real.rpow_one] at this
    exact this.symm
  exact hO.trans_isLittleO hlo

private lemma fc5_repr (α c x0 x1 t : ℝ) (ht : 0 < t) :
    x0 * mittagLefflerOne α (c * t ^ α) + x1 * t * mittagLeffler α 2 (c * t ^ α)
      = x0 * fc5_G α c 0 t + x1 * fc5_G α c 1 t := by
  have hA : mittagLeffler α 1 (c * t ^ α) = fc5_G α c 0 t := by
    unfold mittagLeffler fc5_G fc5_h
    congr 1; funext k
    rw [mul_pow, ← Real.rpow_natCast (t ^ α), ← Real.rpow_mul ht.le, add_zero]
    ring
  have hB : t * mittagLeffler α 2 (c * t ^ α) = fc5_G α c 1 t := by
    unfold mittagLeffler fc5_G fc5_h
    rw [← tsum_mul_left]
    congr 1; funext k
    rw [mul_pow, ← Real.rpow_natCast (t ^ α), ← Real.rpow_mul ht.le, Real.rpow_add ht,
      Real.rpow_one, show α * k + 1 + 1 = α * k + 2 by ring]
    ring
  rw [mittagLefflerOne, hA, mul_assoc, hB]

private lemma fc5_d2 (α c x0 x1 : ℝ) (hα : 1 ≤ α) (f : ℝ → ℝ)
    (hf : ∀ t > 0, f t = x0 * fc5_G α c 0 t + x1 * fc5_G α c 1 t) (s : ℝ) (hs : 0 < s) :
    iteratedDeriv 2 f s = x0 * fc5_G α c (-2) s + x1 * fc5_G α c (-1) s := by
  have hd1 : ∀ t > 0, deriv f t = x0 * fc5_G α c (-1) t + x1 * fc5_G α c 0 t := by
    intro t ht
    have heq : f =ᶠ[nhds t] fun u => x0 * fc5_G α c 0 u + x1 * fc5_G α c 1 u := by
      filter_upwards [Ioi_mem_nhds ht] with u hu using hf u hu
    rw [heq.deriv_eq]
    have := ((fc5_G_deriv α c 0 t hα ht).const_mul x0).add
      ((fc5_G_deriv α c 1 t hα ht).const_mul x1)
    rw [show (0:ℝ) - 1 = -1 by norm_num, sub_self] at this
    exact this.deriv
  have heq2 : deriv f =ᶠ[nhds s] fun u => x0 * fc5_G α c (-1) u + x1 * fc5_G α c 0 u := by
    filter_upwards [Ioi_mem_nhds hs] with u hu using hd1 u hu
  rw [iteratedDeriv_succ, iteratedDeriv_one, heq2.deriv_eq]
  have := ((fc5_G_deriv α c (-1) s hα hs).const_mul x0).add
    ((fc5_G_deriv α c 0 s hα hs).const_mul x1)
  rw [show (-1:ℝ) - 1 = -2 by norm_num, show (0:ℝ) - 1 = -1 by norm_num] at this
  exact this.deriv

theorem solution (α ω : ℝ) (x0 x1 : ℝ)
    (hα1 : 1 < α) (hα2 : α ≤ 2) (hω : 0 < ω) :
    let x : ℝ → ℝ := fun t => x0 * mittagLefflerOne α (-(ω ^ α) * t ^ α)
      + x1 * t * mittagLeffler α 2 (-(ω ^ α) * t ^ α)
    (∀ t > 0, caputoDeriv 0 α x t + ω ^ α * x t = 0) ∧ x 0 = x0 ∧ deriv x 0 = x1 := by
  intro x
  have hderiv := fc5_hasDerivAt_zero α (-(ω ^ α)) x0 x1 hα1
  have hrepr : ∀ t > 0, x t = x0 * fc5_G α (-(ω ^ α)) 0 t + x1 * fc5_G α (-(ω ^ α)) 1 t :=
    fun t ht => fc5_repr α _ x0 x1 t ht
  refine ⟨?_, ?_, hderiv.deriv⟩
  · intro t ht
    set c : ℝ := -(ω ^ α) with hc
    have hceil : Nat.ceil α = 2 := by
      rw [Nat.ceil_eq_iff (by norm_num)]; norm_num; exact ⟨hα1, hα2⟩
    have hd2 : ∀ s > 0, iteratedDeriv 2 x s
        = x0 * (c * fc5_G α c (α - 2) s) + x1 * (c * fc5_G α c (α - 1) s) := by
      intro s hs
      rw [fc5_d2 α c x0 x1 hα1.le x hrepr s hs,
        fc5_G_shift α c (-2) s hα1.le hs (by
          rw [show (-2:ℝ) + 1 = -((1:ℕ):ℝ) by norm_num]; exact Real.Gamma_neg_nat_eq_zero 1),
        fc5_G_shift α c (-1) s hα1.le hs (by norm_num [Real.Gamma_zero])]
      ring_nf
    unfold caputoDeriv rlIntegral
    simp only [hceil]
    push_cast
    rw [hrepr t ht]
    by_cases h2 : α = 2
    · rw [if_pos (by rw [h2]; norm_num), hd2 t ht]
      subst h2
      rw [hc]; norm_num; ring
    · have hμ : 0 < 2 - α := by
        rcases lt_or_eq_of_le hα2 with h | h
        · linarith
        · exact absurd h h2
      rw [if_neg hμ.ne', setIntegral_congr_fun measurableSet_Ioo
        (g := fun s => (t - s) ^ (2 - α - 1) * ((x0 * c) * fc5_G α c (α - 2) s
          + (x1 * c) * fc5_G α c (α - 1) s)) (fun s hs => by
            simp only; rw [hd2 s hs.1]; ring),
        fc5_rl α c (2 - α) (α - 2) (α - 1) (x0 * c) (x1 * c) t hα1.le hμ (by linarith)
          (by linarith) ht]
      rw [show α - 2 + (2 - α) = 0 by ring, show α - 1 + (2 - α) = 1 by ring,
        ← mul_assoc, inv_mul_cancel₀ (Real.Gamma_pos_of_pos hμ).ne', hc]
      ring
  · show x0 * mittagLefflerOne α (-(ω ^ α) * (0:ℝ) ^ α)
      + x1 * 0 * mittagLeffler α 2 (-(ω ^ α) * (0:ℝ) ^ α) = x0
    have h1 : mittagLeffler α 1 0 = 1 := by
      unfold mittagLeffler
      rw [tsum_eq_single 0 (fun k hk => by simp [zero_pow hk])]
      simp
    simp [Real.zero_rpow (by linarith : α ≠ 0), mittagLefflerOne, h1]
