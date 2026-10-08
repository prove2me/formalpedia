-- Prove2me | solution 1 for BurkholderDFI.ConcavePhi.truncation_implies_concave
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T09:32:30.948996+00:00
-- url     : https://prove2.me/submissions/a20f581c-7c13-4560-a090-a9da8fc45f1e

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace BurkholderDFI.ConcavePhi

open Filter Topology BurkholderDFI.SquareFnLp

/-! ### Finiteness of `Φ` on finite arguments and the real-valued function `phiR` -/

lemma isPhi_ne_top {Φ : ℝ≥0∞ → ℝ≥0∞} {c : ℝ≥0} (hΦ : IsPhi Φ c) {x : ℝ≥0∞}
    (hx : x ≠ ⊤) : Φ x ≠ ⊤ := by
  have h0 : Tendsto Φ (𝓝 0) (𝓝 0) := by
    have := hΦ.cont.tendsto 0
    rwa [hΦ.zero] at this
  rw [ENNReal.tendsto_nhds_zero] at h0
  have h1 := h0 1 one_pos
  rw [ENNReal.nhds_zero_basis.eventually_iff] at h1
  obtain ⟨δ, hδ, hδ'⟩ := h1
  obtain ⟨d, hd0, hdδ⟩ := exists_between hδ
  have hΦd : Φ d ≤ 1 := hδ' hdδ
  have hdtop : d ≠ ⊤ := (hdδ.trans_le le_top).ne
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (ENNReal.div_lt_top hx hd0.ne').ne
  have hxle : x ≤ 2 ^ n * d := by
    calc x = x / d * d := (ENNReal.div_mul_cancel hd0.ne' hdtop).symm
      _ ≤ (n : ℝ≥0∞) * d := mul_le_mul_left hn.le _
      _ ≤ 2 ^ n * d := by
        gcongr
        exact_mod_cast n.lt_two_pow_self.le
  have key : ∀ k : ℕ, Φ (2 ^ k * d) ≤ (c : ℝ≥0∞) ^ k * Φ d := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc Φ (2 ^ (k + 1) * d) = Φ (2 * (2 ^ k * d)) := by ring_nf
        _ ≤ c * Φ (2 ^ k * d) := hΦ.growth _
        _ ≤ c * ((c : ℝ≥0∞) ^ k * Φ d) := mul_le_mul_right ih _
        _ = (c : ℝ≥0∞) ^ (k + 1) * Φ d := by ring
  refine ne_top_of_le_ne_top ?_ ((hΦ.mono hxle).trans (key n))
  exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
    (ne_top_of_le_ne_top ENNReal.one_ne_top hΦd)

/-- The real-valued version of `Φ`. -/
noncomputable def phiR (Φ : ℝ≥0∞ → ℝ≥0∞) (r : ℝ) : ℝ := (Φ (ENNReal.ofReal r)).toReal

section phiR
variable {Φ : ℝ≥0∞ → ℝ≥0∞} {c : ℝ≥0}

lemma ofReal_phiR (hΦ : IsPhi Φ c) (r : ℝ) :
    ENNReal.ofReal (phiR Φ r) = Φ (ENNReal.ofReal r) :=
  ENNReal.ofReal_toReal (isPhi_ne_top hΦ ENNReal.ofReal_ne_top)

lemma phiR_zero (hΦ : IsPhi Φ c) : phiR Φ 0 = 0 := by simp [phiR, hΦ.zero]

lemma phiR_nonneg (Φ : ℝ≥0∞ → ℝ≥0∞) (r : ℝ) : 0 ≤ phiR Φ r := ENNReal.toReal_nonneg

lemma phiR_mono (hΦ : IsPhi Φ c) : Monotone (phiR Φ) := by
  intro a b hab
  exact ENNReal.toReal_mono (isPhi_ne_top hΦ ENNReal.ofReal_ne_top)
    (hΦ.mono (ENNReal.ofReal_le_ofReal hab))

lemma phiR_continuous (hΦ : IsPhi Φ c) : Continuous (phiR Φ) := by
  have : phiR Φ = ENNReal.toReal ∘ (Φ ∘ ENNReal.ofReal) := rfl
  rw [this]
  exact ENNReal.continuousOn_toReal.comp_continuous (hΦ.cont.comp ENNReal.continuous_ofReal)
    (fun x => isPhi_ne_top hΦ ENNReal.ofReal_ne_top)

lemma phiR_concave (hcc : IsConcavePhi Φ) : ConcaveOn ℝ (Set.Ici 0) (phiR Φ) := hcc

end phiR

/-- Chord inequality for a concave function. -/
lemma chord_le {φ : ℝ → ℝ} (hcc : ConcaveOn ℝ (Set.Ici 0) φ) {a b x : ℝ} (ha : 0 ≤ a)
    (hab : a < b) (hx1 : a ≤ x) (hx2 : x ≤ b) :
    φ a + (φ b - φ a) / (b - a) * (x - a) ≤ φ x := by
  have hba : 0 < b - a := by linarith
  have ht0 : 0 ≤ (x - a) / (b - a) := div_nonneg (by linarith) hba.le
  have ht1 : (x - a) / (b - a) ≤ 1 := by rw [div_le_one hba]; linarith
  have hx : x = (1 - (x - a) / (b - a)) • a + ((x - a) / (b - a)) • b := by
    simp only [smul_eq_mul]
    field_simp
    ring
  have := hcc.2 (Set.mem_Ici.mpr ha) (Set.mem_Ici.mpr (by linarith : (0:ℝ) ≤ b))
    (by linarith : 0 ≤ 1 - (x - a) / (b - a)) ht0 (by ring)
  rw [← hx] at this
  simp only [smul_eq_mul] at this
  calc φ a + (φ b - φ a) / (b - a) * (x - a)
      = (1 - (x - a) / (b - a)) * φ a + (x - a) / (b - a) * φ b := by
        field_simp
        ring
    _ ≤ φ x := this

/-! ### Piecewise-linear lower approximations on a grid of mesh `h` -/

section grid
variable (Φ : ℝ≥0∞ → ℝ≥0∞) (h : ℝ)

/-- Slope of the chord of `phiR Φ` on `[i h, (i+1) h]`. -/
noncomputable def sl (i : ℕ) : ℝ := (phiR Φ (((i : ℝ) + 1) * h) - phiR Φ ((i : ℝ) * h)) / h

/-- The chord interpolant on `[0, N h]` (constant beyond), written as a sum of ramps. -/
noncomputable def Bsum (N : ℕ) (r : ℝ) : ℝ :=
  ∑ i ∈ Finset.range N, sl Φ h i * (min r (((i : ℝ) + 1) * h) - min r ((i : ℝ) * h))

/-- Coefficients of the truncation representation. -/
noncomputable def acoef (N i : ℕ) : ℝ := sl Φ h i - (if i + 1 < N then sl Φ h (i + 1) else 0)

/-- The same function as a nonnegative combination of truncations `min r (λ_i)`. -/
noncomputable def Asum (N : ℕ) (r : ℝ) : ℝ :=
  ∑ i ∈ Finset.range N, acoef Φ h N i * min r (((i : ℝ) + 1) * h)

/-- The `ℝ≥0∞`-valued version. -/
noncomputable def psi (N : ℕ) (x : ℝ≥0∞) : ℝ≥0∞ :=
  ∑ i ∈ Finset.range N,
    ENNReal.ofReal (acoef Φ h N i) * min x (ENNReal.ofReal (((i : ℝ) + 1) * h))

variable {Φ h}

lemma abel_aux (s m : ℕ → ℝ) (hm : m 0 = 0) (N : ℕ) :
    ∑ i ∈ Finset.range N, (s i - s (i + 1)) * m (i + 1) + s N * m N
      = ∑ i ∈ Finset.range N, s i * (m (i + 1) - m i) := by
  induction N with
  | zero => simp [hm]
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ← ih]
    ring

lemma Asum_eq_Bsum (N : ℕ) (r : ℝ) (hr : 0 ≤ r) : Asum Φ h N r = Bsum Φ h N r := by
  have := abel_aux (fun i => if i < N then sl Φ h i else 0) (fun i => min r ((i : ℝ) * h))
    (by simp [hr]) N
  simp only [lt_irrefl, if_false, zero_mul, add_zero] at this
  unfold Asum Bsum
  rw [show (∑ i ∈ Finset.range N, acoef Φ h N i * min r (((i : ℝ) + 1) * h))
      = ∑ i ∈ Finset.range N, ((if i < N then sl Φ h i else 0)
          - if i + 1 < N then sl Φ h (i + 1) else 0) * min r (((i + 1 : ℕ) : ℝ) * h) from
    Finset.sum_congr rfl (fun i hi => by
      rw [Finset.mem_range] at hi
      simp only [acoef, hi, if_true]
      push_cast
      ring), this]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  simp only [hi, if_true]
  push_cast
  ring

variable {c : ℝ≥0}

lemma sl_nonneg (hΦ : IsPhi Φ c) (hh : 0 < h) (i : ℕ) : 0 ≤ sl Φ h i := by
  unfold sl
  apply div_nonneg _ hh.le
  rw [sub_nonneg]
  apply phiR_mono hΦ
  nlinarith

lemma sl_succ_le (hΦ : IsPhi Φ c) (hcc : IsConcavePhi Φ) (hh : 0 < h) (i : ℕ) :
    sl Φ h (i + 1) ≤ sl Φ h i := by
  have hc := chord_le (phiR_concave hcc) (a := (i : ℝ) * h) (b := ((i : ℝ) + 1 + 1) * h)
    (x := ((i : ℝ) + 1) * h) (by positivity) (by nlinarith) (by nlinarith) (by nlinarith)
  have e1 : ((i : ℝ) + 1 + 1) * h - (i : ℝ) * h = 2 * h := by ring
  have e2 : ((i : ℝ) + 1) * h - (i : ℝ) * h = h := by ring
  rw [e1, e2] at hc
  have e3 : (phiR Φ (((i : ℝ) + 1 + 1) * h) - phiR Φ ((i : ℝ) * h)) / (2 * h) * h
      = (phiR Φ (((i : ℝ) + 1 + 1) * h) - phiR Φ ((i : ℝ) * h)) / 2 := by
    field_simp
  rw [e3] at hc
  unfold sl
  push_cast
  apply div_le_div_of_nonneg_right _ hh.le
  linarith

lemma acoef_nonneg (hΦ : IsPhi Φ c) (hcc : IsConcavePhi Φ) (hh : 0 < h) (N i : ℕ) :
    0 ≤ acoef Φ h N i := by
  unfold acoef
  by_cases hi : i + 1 < N
  · simp only [hi, if_true]
    exact sub_nonneg.mpr (sl_succ_le hΦ hcc hh i)
  · simp only [hi, if_false, sub_zero]
    exact sl_nonneg hΦ hh i

lemma Bsum_props (hΦ : IsPhi Φ c) (hcc : IsConcavePhi Φ) (hh : 0 < h) (N : ℕ) :
    ∀ r : ℝ, 0 ≤ r →
      ((N : ℝ) * h ≤ r → Bsum Φ h N r = phiR Φ ((N : ℝ) * h)) ∧
      Bsum Φ h N r ≤ phiR Φ (min r ((N : ℝ) * h)) ∧
      phiR Φ (max (min r ((N : ℝ) * h) - h) 0) ≤ Bsum Φ h N r := by
  have hmono := phiR_mono hΦ
  induction N with
  | zero =>
    intro r hr
    have hB0 : Bsum Φ h 0 r = 0 := by simp [Bsum]
    simp only [Nat.cast_zero, zero_mul, min_eq_right hr, zero_sub, hB0, phiR_zero hΦ]
    refine ⟨fun _ => trivial, le_rfl, ?_⟩
    rw [max_eq_right (by linarith), phiR_zero hΦ]
  | succ N ih =>
    intro r hr
    obtain ⟨ih1, ih2, ih3⟩ := ih r hr
    push_cast
    have hB : Bsum Φ h (N + 1) r
        = Bsum Φ h N r + sl Φ h N * (min r (((N : ℝ) + 1) * h) - min r ((N : ℝ) * h)) := by
      unfold Bsum
      rw [Finset.sum_range_succ]
    have hNh : 0 ≤ (N : ℝ) * h := by positivity
    rcases le_or_gt r ((N : ℝ) * h) with hle | hlt
    · have e1 : min r ((N : ℝ) * h) = r := min_eq_left hle
      have e2 : min r (((N : ℝ) + 1) * h) = r := min_eq_left (by nlinarith)
      rw [hB, e1, e2, sub_self, mul_zero, add_zero]
      rw [e1] at ih2 ih3
      exact ⟨fun hc => absurd hc (by push_neg; nlinarith), ih2, ih3⟩
    · have e1 : min r ((N : ℝ) * h) = (N : ℝ) * h := min_eq_right hlt.le
      have hr'1 : (N : ℝ) * h ≤ min r (((N : ℝ) + 1) * h) := le_min hlt.le (by nlinarith)
      have hr'2 : min r (((N : ℝ) + 1) * h) ≤ ((N : ℝ) + 1) * h := min_le_right _ _
      have hBN := ih1 hlt.le
      rw [hB, hBN, e1]
      refine ⟨?_, ?_, ?_⟩
      · intro hc
        rw [min_eq_right hc]
        unfold sl
        field_simp
        ring
      · have := chord_le (phiR_concave hcc) hNh
          (by nlinarith : (N : ℝ) * h < ((N : ℝ) + 1) * h) hr'1 hr'2
        have e3 : ((N : ℝ) + 1) * h - (N : ℝ) * h = h := by ring
        rw [e3] at this
        exact this
      · have hsl : 0 ≤ sl Φ h N := sl_nonneg hΦ hh N
        calc phiR Φ (max (min r (((N : ℝ) + 1) * h) - h) 0)
            ≤ phiR Φ ((N : ℝ) * h) := hmono (max_le (by linarith) hNh)
          _ ≤ phiR Φ ((N : ℝ) * h) + sl Φ h N * (min r (((N : ℝ) + 1) * h) - (N : ℝ) * h) :=
            le_add_of_nonneg_right (mul_nonneg hsl (by linarith))

lemma psi_ofReal (hΦ : IsPhi Φ c) (hcc : IsConcavePhi Φ) (hh : 0 < h) (N : ℕ) (r : ℝ)
    (hr : 0 ≤ r) : psi Φ h N (ENNReal.ofReal r) = ENNReal.ofReal (Bsum Φ h N r) := by
  rw [← Asum_eq_Bsum N r hr]
  unfold psi Asum
  rw [ENNReal.ofReal_sum_of_nonneg
    (fun i _ => mul_nonneg (acoef_nonneg hΦ hcc hh N i) (le_min hr (by positivity)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [ENNReal.ofReal_mul (acoef_nonneg hΦ hcc hh N i), ENNReal.ofReal_min]

lemma psi_top (hh : 0 < h) (N : ℕ) :
    psi Φ h N ⊤ = psi Φ h N (ENNReal.ofReal ((N : ℝ) * h)) := by
  unfold psi
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  congr 1
  rw [min_eq_right le_top, min_eq_right]
  apply ENNReal.ofReal_le_ofReal
  have : (i : ℝ) + 1 ≤ N := by exact_mod_cast hi
  nlinarith

lemma measurable_psi_comp {Ω : Type*} [MeasurableSpace Ω] (N : ℕ) {Z : Ω → ℝ≥0∞}
    (hZ : Measurable Z) : Measurable (fun ω => psi Φ h N (Z ω)) := by
  unfold psi
  exact Finset.measurable_sum _ (fun i _ => (hZ.min measurable_const).const_mul _)

lemma lintegral_psi_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (hh : 0 < h) (N : ℕ)
    {Z W : Ω → ℝ≥0∞} (hZ : Measurable Z) (hW : Measurable W)
    (h202 : ∀ l : ℝ≥0, 0 < l →
      ∫⁻ ω, min (Z ω) (l : ℝ≥0∞) ∂P ≤ 2 * ∫⁻ ω, min (W ω) (l : ℝ≥0∞) ∂P) :
    ∫⁻ ω, psi Φ h N (Z ω) ∂P ≤ 2 * ∫⁻ ω, psi Φ h N (W ω) ∂P := by
  unfold psi
  rw [lintegral_finset_sum _ (fun i _ => (hZ.min measurable_const).const_mul _),
    lintegral_finset_sum _ (fun i _ => (hW.min measurable_const).const_mul _), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [lintegral_const_mul _ (hZ.min measurable_const),
    lintegral_const_mul _ (hW.min measurable_const), mul_left_comm]
  apply mul_le_mul_right
  have := h202 ((((i : ℝ) + 1) * h).toNNReal) (Real.toNNReal_pos.mpr (by positivity))
  exact this

end grid

/-! ### The dyadic sequence of approximations -/

section dyadic
variable {Φ : ℝ≥0∞ → ℝ≥0∞} {c : ℝ≥0}

/-- mesh `2^{-n}` -/
noncomputable def hn (n : ℕ) : ℝ := ((2 : ℝ) ^ n)⁻¹

lemma hn_pos (n : ℕ) : 0 < hn n := by unfold hn; positivity

lemma Nhn (n : ℕ) : ((4 ^ n : ℕ) : ℝ) * hn n = 2 ^ n := by
  unfold hn
  push_cast
  rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
  field_simp

lemma hn_tendsto : Tendsto hn atTop (𝓝 0) := by
  unfold hn
  exact tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)

/-- `ψ_n` -/
noncomputable def psin (Φ : ℝ≥0∞ → ℝ≥0∞) (n : ℕ) (x : ℝ≥0∞) : ℝ≥0∞ := psi Φ (hn n) (4 ^ n) x

lemma psin_top (hΦ : IsPhi Φ c) (hcc : IsConcavePhi Φ) (n : ℕ) :
    psin Φ n ⊤ = Φ (ENNReal.ofReal ((2 : ℝ) ^ n)) := by
  unfold psin
  have hpos : 0 ≤ ((4 ^ n : ℕ) : ℝ) * hn n := mul_nonneg (by positivity) (hn_pos n).le
  rw [psi_top (hn_pos n), psi_ofReal hΦ hcc (hn_pos n) _ _ hpos,
    (Bsum_props hΦ hcc (hn_pos n) (4 ^ n) _ hpos).1 le_rfl, Nhn, ofReal_phiR hΦ]

lemma psin_le (hΦ : IsPhi Φ c) (hcc : IsConcavePhi Φ) (n : ℕ) (x : ℝ≥0∞) :
    psin Φ n x ≤ Φ x := by
  by_cases hx : x = ⊤
  · rw [hx, psin_top hΦ hcc]
    exact hΦ.mono le_top
  · rw [← ENNReal.ofReal_toReal hx]
    unfold psin
    rw [psi_ofReal hΦ hcc (hn_pos n) _ _ ENNReal.toReal_nonneg, ← ofReal_phiR hΦ]
    apply ENNReal.ofReal_le_ofReal
    refine ((Bsum_props hΦ hcc (hn_pos n) (4 ^ n) _ ENNReal.toReal_nonneg).2.1).trans ?_
    exact phiR_mono hΦ (min_le_left _ _)

lemma psin_tendsto (hΦ : IsPhi Φ c) (hcc : IsConcavePhi Φ) (x : ℝ≥0∞) :
    Tendsto (fun n => psin Φ n x) atTop (𝓝 (Φ x)) := by
  have h2 : Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt one_lt_two
  by_cases hx : x = ⊤
  · rw [hx]
    simp_rw [psin_top hΦ hcc]
    exact (hΦ.cont.tendsto ⊤).comp (ENNReal.tendsto_ofReal_atTop.comp h2)
  · rw [← ENNReal.ofReal_toReal hx]
    set r := x.toReal with hr
    have hr0 : 0 ≤ r := ENNReal.toReal_nonneg
    unfold psin
    simp_rw [psi_ofReal hΦ hcc (hn_pos _) _ _ hr0]
    rw [← ofReal_phiR hΦ]
    apply (ENNReal.continuous_ofReal.tendsto _).comp
    -- squeeze
    have hL : Tendsto (fun n => max (min r (((4 ^ n : ℕ) : ℝ) * hn n) - hn n) 0) atTop (𝓝 r) := by
      have hev : ∀ᶠ n in atTop, max (min r (((4 ^ n : ℕ) : ℝ) * hn n) - hn n) 0
          = max (r - hn n) 0 := by
        filter_upwards [h2.eventually_ge_atTop r] with n hn2
        rw [Nhn, min_eq_left hn2]
      refine Tendsto.congr' (EventuallyEq.symm hev) ?_
      have : Tendsto (fun n => max (r - hn n) 0) atTop (𝓝 (max (r - 0) 0)) :=
        (tendsto_const_nhds.sub hn_tendsto).max tendsto_const_nhds
      rwa [sub_zero, max_eq_left hr0] at this
    have hlow : Tendsto (fun n => phiR Φ (max (min r (((4 ^ n : ℕ) : ℝ) * hn n) - hn n) 0))
        atTop (𝓝 (phiR Φ r)) :=
      ((phiR_continuous hΦ).tendsto r).comp hL
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds ?_ ?_
    · intro n
      exact (Bsum_props hΦ hcc (hn_pos n) (4 ^ n) r hr0).2.2
    · intro n
      exact ((Bsum_props hΦ hcc (hn_pos n) (4 ^ n) r hr0).2.1).trans
        (phiR_mono hΦ (min_le_left _ _))

end dyadic

theorem truncation_implies_concave_core {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (Φ : ℝ≥0∞ → ℝ≥0∞) (c : ℝ≥0) (hΦ : BurkholderDFI.SquareFnLp.IsPhi Φ c)
    (hcc : BurkholderDFI.SquareFnLp.IsConcavePhi Φ) (Z W : Ω → ℝ≥0∞) (hZ : Measurable Z)
    (hW : Measurable W)
    (h202 : ∀ l : ℝ≥0, 0 < l →
      ∫⁻ ω, min (Z ω) (l : ℝ≥0∞) ∂P ≤ 2 * ∫⁻ ω, min (W ω) (l : ℝ≥0∞) ∂P) :
    ∫⁻ ω, Φ (Z ω) ∂P ≤ 2 * ∫⁻ ω, Φ (W ω) ∂P := by
  have hlim : ∀ ω, Φ (Z ω) = liminf (fun n => psin Φ n (Z ω)) atTop :=
    fun ω => ((psin_tendsto hΦ hcc (Z ω)).liminf_eq).symm
  calc ∫⁻ ω, Φ (Z ω) ∂P = ∫⁻ ω, liminf (fun n => psin Φ n (Z ω)) atTop ∂P := by
        simp_rw [hlim]
    _ ≤ liminf (fun n => ∫⁻ ω, psin Φ n (Z ω) ∂P) atTop :=
        lintegral_liminf_le (fun n => measurable_psi_comp _ hZ)
    _ ≤ liminf (fun n => 2 * ∫⁻ ω, psin Φ n (W ω) ∂P) atTop := by
        exact liminf_le_liminf
          (Eventually.of_forall (fun n => lintegral_psi_le (hn_pos n) _ hZ hW h202))
    _ ≤ 2 * ∫⁻ ω, Φ (W ω) ∂P := by
        apply liminf_le_of_frequently_le'
        apply Eventually.frequently
        apply Eventually.of_forall
        intro n
        apply mul_le_mul_right
        exact lintegral_mono (fun ω => psin_le hΦ hcc n (W ω))

end BurkholderDFI.ConcavePhi

open BurkholderDFI.ConcavePhi


theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (Φ : ℝ≥0∞ → ℝ≥0∞) (c : ℝ≥0) (hΦ : BurkholderDFI.SquareFnLp.IsPhi Φ c)
    (hcc : BurkholderDFI.SquareFnLp.IsConcavePhi Φ) (Z W : Ω → ℝ≥0∞) (hZ : Measurable Z) (hW : Measurable W)
    (h202 : ∀ l : ℝ≥0, 0 < l →
      ∫⁻ ω, min (Z ω) (l : ℝ≥0∞) ∂P ≤ 2 * ∫⁻ ω, min (W ω) (l : ℝ≥0∞) ∂P) :
    ∫⁻ ω, Φ (Z ω) ∂P ≤ 2 * ∫⁻ ω, Φ (W ω) ∂P := by
  exact truncation_implies_concave_core Φ c hΦ hcc Z W hZ hW h202
