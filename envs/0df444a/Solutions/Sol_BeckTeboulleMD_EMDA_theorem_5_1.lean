-- Prove2me | solution 1 for BeckTeboulleMD.EMDA.theorem_5_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T16:46:42.483975+00:00
-- url     : https://prove2.me/submissions/1ecb56cc-b551-4219-bb9c-b0c384f0c810

import Mathlib
import Definitions.Def_BeckTeboulleMD_EMDA_Setting

set_option autoImplicit false

open MeasureTheory ProbabilityTheory in
/-- Finite Hoeffding lemma: for weights `p` in the simplex and values `|v j| ≤ L`,
`∑ p_j e^{t v_j} ≤ exp (t ∑ p_j v_j + L² t² / 2)`. -/
lemma emda_hoeff {n : ℕ} (p : Fin n → ℝ) (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1)
    (v : Fin n → ℝ) (L : ℝ) (hv : ∀ j, |v j| ≤ L) (t : ℝ) :
    ∑ j, p j * Real.exp (t * v j) ≤ Real.exp (t * ∑ j, p j * v j + L ^ 2 * t ^ 2 / 2) := by
  set μ : Measure (Fin n) := ∑ j, ENNReal.ofReal (p j) • Measure.dirac j with hμ
  have hfin : ∀ j, IsFiniteMeasure (ENNReal.ofReal (p j) • Measure.dirac j) := fun j => by
    constructor; simp
  have hint : ∀ φ : Fin n → ℝ, ∫ ω, φ ω ∂μ = ∑ j, p j * φ j := by
    intro φ
    rw [hμ, integral_finsetSum_measure (fun j _ => by haveI := hfin j; exact Integrable.of_finite)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hp0 j), smul_eq_mul]
  haveI : IsProbabilityMeasure μ := by
    constructor
    rw [hμ, Measure.coe_finsetSum, Finset.sum_apply]
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hp0 j), hp1, ENNReal.ofReal_one]
  have hb : ∀ᵐ ω ∂μ, v ω ∈ Set.Icc (-L) L :=
    Filter.Eventually.of_forall (fun ω => abs_le.mp (hv ω))
  have h := (hasSubgaussianMGF_of_mem_Icc (μ := μ) (X := v)
    (Measurable.of_discrete).aemeasurable hb).mgf_le t
  simp only [mgf] at h
  rw [hint] at h
  have hm : μ[v] = ∑ j, p j * v j := hint v
  rw [hm] at h
  have hc : (((‖L - -L‖₊ / 2) ^ 2 : NNReal) : ℝ) = L ^ 2 := by
    push_cast
    rw [Real.norm_eq_abs, sub_neg_eq_add, div_pow, sq_abs]
    ring
  rw [hc] at h
  set m := ∑ j, p j * v j
  have hsplit : ∑ j, p j * Real.exp (t * (v j - m))
      = (∑ j, p j * Real.exp (t * v j)) * Real.exp (-(t * m)) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [mul_sub, sub_eq_add_neg, Real.exp_add]
    ring
  rw [hsplit] at h
  have he : 0 < Real.exp (t * m) := Real.exp_pos _
  calc ∑ j, p j * Real.exp (t * v j)
      = ((∑ j, p j * Real.exp (t * v j)) * Real.exp (-(t * m))) * Real.exp (t * m) := by
        rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    _ ≤ Real.exp (L ^ 2 * t ^ 2 / 2) * Real.exp (t * m) :=
        mul_le_mul_of_nonneg_right h he.le
    _ = Real.exp (t * m + L ^ 2 * t ^ 2 / 2) := by
        rw [← Real.exp_add, add_comm]

open BeckTeboulleMD.EMDA in
theorem solution {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : ConvexOn ℝ (stdSimplex ℝ (Fin n)) f)
    (Lf : ℝ) (hLf : 0 < Lf)
    (hLip : ∀ x ∈ stdSimplex ℝ (Fin n), ∀ y ∈ stdSimplex ℝ (Fin n),
      |f x - f y| ≤ Lf * ∑ j, |x j - y j|)
    (g : (Fin n → ℝ) → (Fin n → ℝ))
    (hg : ∀ x ∈ stdSimplex ℝ (Fin n), ∀ y ∈ stdSimplex ℝ (Fin n),
      f x + ∑ j, g x j * (y j - x j) ≤ f y)
    (hgb : ∀ x ∈ stdSimplex ℝ (Fin n), ∀ j, |g x j| ≤ Lf)
    (xstar : Fin n → ℝ) (hxstar : xstar ∈ stdSimplex ℝ (Fin n))
    (hmin : ∀ y ∈ stdSimplex ℝ (Fin n), f xstar ≤ f y)
    (k : ℕ) (hk : 1 ≤ k)
    (x : ℕ → Fin n → ℝ) (hx1 : x 1 = fun _ => 1 / (n : ℝ))
    (hrun : IsEDARun g (Real.sqrt (2 * Real.log n) / (Lf * Real.sqrt k)) x) :
    ∃ s ∈ Finset.Icc 1 k,
      f (x s) - f xstar ≤ Real.sqrt (2 * Real.log n) * Lf / Real.sqrt k := by
  obtain ⟨hxs0, hxs1⟩ := hxstar
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at hxs1
    · exact h
  have hnR : (0:ℝ) < n := by exact_mod_cast hn1
  haveI : Nonempty (Fin n) := ⟨⟨0, hn1⟩⟩
  set t := Real.sqrt (2 * Real.log n) / (Lf * Real.sqrt k) with ht
  set R := Real.sqrt (2 * Real.log n) * Lf / Real.sqrt k with hR
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  have inv : ∀ s, 1 ≤ s → (∀ j, 0 < x s j) ∧ ∑ j, x s j = 1 := by
    intro s hs
    induction s, hs using Nat.le_induction with
    | base =>
      rw [hx1]
      refine ⟨fun j => by positivity, ?_⟩
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    | succ s hs ih =>
      obtain ⟨hpos, hsum⟩ := ih
      have hZ : 0 < ∑ i, x s i * Real.exp (-(t * g (x s) i)) :=
        Finset.sum_pos (fun i _ => mul_pos (hpos i) (Real.exp_pos _)) Finset.univ_nonempty
      refine ⟨fun j => ?_, ?_⟩
      · rw [hrun s hs j]; exact div_pos (mul_pos (hpos j) (Real.exp_pos _)) hZ
      · simp_rw [hrun s hs]; rw [← Finset.sum_div]; exact div_self hZ.ne'
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · have hn : n = 1 := by omega
    subst hn
    refine ⟨1, Finset.mem_Icc.mpr ⟨le_refl _, hk⟩, ?_⟩
    have hx : x 1 = xstar := by
      funext j
      have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      simp only [Fin.sum_univ_one] at hxs1
      rw [hx1, hxs1]; norm_num
    rw [hx, sub_self]; exact hR0
  · have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hkR : (0:ℝ) < k := by exact_mod_cast hk
    have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hkR
    have hsl : 0 < Real.sqrt (2 * Real.log n) := Real.sqrt_pos.mpr (by positivity)
    have htpos : 0 < t := by rw [ht]; positivity
    have hsl2 : Real.sqrt (2 * Real.log n) * Real.sqrt (2 * Real.log n) = 2 * Real.log n :=
      Real.mul_self_sqrt (by positivity)
    have hsk2 : Real.sqrt k * Real.sqrt k = k := Real.mul_self_sqrt hkR.le
    have ht2 : (k:ℝ) * (Lf ^ 2 * t ^ 2 / 2) = Real.log n := by
      rw [ht]; field_simp; nlinarith [hsl2, hsk2]
    have htR : t * (k * R) = 2 * Real.log n := by
      rw [ht, hR]; field_simp; nlinarith [hsl2, hsk2]
    set Ψ : ℕ → ℝ := fun s => ∑ j, xstar j * Real.log (x s j) with hΨdef
    have step : ∀ s, 1 ≤ s →
        t * (f (x s) - f xstar) ≤ Ψ (s + 1) - Ψ s + Lf ^ 2 * t ^ 2 / 2 := by
      intro s hs
      obtain ⟨hpos, hsum⟩ := inv s hs
      have hmem : x s ∈ stdSimplex ℝ (Fin n) := ⟨fun j => (hpos j).le, hsum⟩
      have hsub := hg (x s) hmem xstar ⟨hxs0, hxs1⟩
      have hgb' := hgb (x s) hmem
      set v := g (x s) with hv
      set Z := ∑ i, x s i * Real.exp (-(t * v i)) with hZdef
      have hZ : 0 < Z :=
        Finset.sum_pos (fun i _ => mul_pos (hpos i) (Real.exp_pos _)) Finset.univ_nonempty
      have hlogx : ∀ j, Real.log (x (s + 1) j) = Real.log (x s j) - t * v j - Real.log Z := by
        intro j
        rw [hrun s hs j, Real.log_div (mul_pos (hpos j) (Real.exp_pos _)).ne' hZ.ne',
          Real.log_mul (hpos j).ne' (Real.exp_pos _).ne', Real.log_exp]
        ring
      have hΨ : Ψ (s + 1) - Ψ s = -(t * ∑ j, xstar j * v j) - Real.log Z := by
        simp only [hΨdef]
        simp_rw [hlogx]
        rw [← Finset.sum_sub_distrib]
        have e : ∀ j, xstar j * (Real.log (x s j) - t * v j - Real.log Z)
            - xstar j * Real.log (x s j) = -(t * (xstar j * v j)) - xstar j * Real.log Z :=
          fun j => by ring
        simp_rw [e]
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hxs1, Finset.sum_neg_distrib,
          ← Finset.mul_sum]
        ring
      have hH := emda_hoeff (x s) (fun j => (hpos j).le) hsum v Lf hgb' (-t)
      have hlZ : Real.log Z ≤ -t * ∑ j, x s j * v j + Lf ^ 2 * t ^ 2 / 2 := by
        have e : Z = ∑ j, x s j * Real.exp (-t * v j) := by
          rw [hZdef]; simp only [neg_mul]
        rw [Real.log_le_iff_le_exp hZ, e]
        convert hH using 2
        ring
      have hlin : f (x s) - f xstar ≤ ∑ j, x s j * v j - ∑ j, xstar j * v j := by
        have e : ∑ j, v j * (xstar j - x s j) = ∑ j, xstar j * v j - ∑ j, x s j * v j := by
          rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun j _ => by ring)
        linarith
      have hm := mul_le_mul_of_nonneg_left hlin htpos.le
      rw [mul_sub] at hm
      have e2 : -t * ∑ j, x s j * v j = -(t * ∑ j, x s j * v j) := by ring
      linarith
    have tele : ∀ m : ℕ, t * ∑ i ∈ Finset.range m, (f (x (i + 1)) - f xstar)
        ≤ Ψ (m + 1) - Ψ 1 + m * (Lf ^ 2 * t ^ 2 / 2) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [Finset.sum_range_succ, mul_add]
        have := step (m + 1) (by omega)
        push_cast
        linarith
    have hΨ1 : Ψ 1 = -Real.log n := by
      simp only [hΨdef, hx1]
      rw [← Finset.sum_mul, hxs1, one_mul, one_div, Real.log_inv]
    have hΨk : Ψ (k + 1) ≤ 0 := by
      obtain ⟨hpos, hsum⟩ := inv (k + 1) (by omega)
      simp only [hΨdef]
      refine Finset.sum_nonpos (fun j _ => mul_nonpos_of_nonneg_of_nonpos (hxs0 j) ?_)
      refine Real.log_nonpos (hpos j).le ?_
      rw [← hsum]
      exact Finset.single_le_sum (fun i _ => (hpos i).le) (Finset.mem_univ j)
    by_contra hcon
    push Not at hcon
    have hlt : ∑ i ∈ Finset.range k, R < ∑ i ∈ Finset.range k, (f (x (i + 1)) - f xstar) := by
      refine Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr (by omega)) ?_
      intro i hi
      exact hcon (i + 1) (Finset.mem_Icc.mpr ⟨by omega, by
        have := Finset.mem_range.mp hi; omega⟩)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hlt
    have h1 := mul_lt_mul_of_pos_left hlt htpos
    have h2 := tele k
    linarith
