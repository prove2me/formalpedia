-- Prove2me | solution 1 for BurkholderDFI.SquareFnLp.eq_1_3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T10:58:32.254262+00:00
-- url     : https://prove2.me/submissions/9b705f92-8674-4370-9a41-6fd6671e8a63

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace BurkholderDFI.SquareFnLp

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Truncation of a `[0, ∞]`-valued function at the level `N`. -/
noncomputable def trunc (Y : Ω → ℝ≥0∞) (N : ℕ) (ω : Ω) : ℝ≥0∞ := min (Y ω) N

lemma trunc_ne_top (Y : Ω → ℝ≥0∞) (N : ℕ) (ω : Ω) : trunc Y N ω ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.natCast_ne_top N) (min_le_right _ _)

lemma trunc_le (Y : Ω → ℝ≥0∞) (N : ℕ) (ω : Ω) : trunc Y N ω ≤ Y ω := min_le_left _ _

lemma trunc_le_nat (Y : Ω → ℝ≥0∞) (N : ℕ) (ω : Ω) : trunc Y N ω ≤ N := min_le_right _ _

lemma measurable_trunc {Y : Ω → ℝ≥0∞} (hY : Measurable Y) (N : ℕ) : Measurable (trunc Y N) :=
  hY.min measurable_const

lemma trunc_mono (Y : Ω → ℝ≥0∞) (ω : Ω) : Monotone fun N : ℕ => trunc Y N ω := by
  intro a b hab
  exact min_le_min le_rfl (by exact_mod_cast hab)

lemma iSup_trunc (Y : Ω → ℝ≥0∞) (ω : Ω) : ⨆ N : ℕ, trunc Y N ω = Y ω := by
  apply le_antisymm (iSup_le fun N => min_le_left _ _)
  by_cases hY : Y ω = ⊤
  · have : ∀ N : ℕ, trunc Y N ω = N := fun N => by simp [trunc, hY]
    simp only [this, ENNReal.iSup_natCast, hY, le_refl]
  · obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt hY
    calc Y ω = trunc Y N ω := (min_eq_left hN.le).symm
      _ ≤ ⨆ N, trunc Y N ω := le_iSup (fun N => trunc Y N ω) N

/-- The real-valued truncation. -/
noncomputable def truncR (Y : Ω → ℝ≥0∞) (N : ℕ) (ω : Ω) : ℝ := (trunc Y N ω).toReal

lemma truncR_nonneg (Y : Ω → ℝ≥0∞) (N : ℕ) (ω : Ω) : 0 ≤ truncR Y N ω := ENNReal.toReal_nonneg

lemma measurable_truncR {Y : Ω → ℝ≥0∞} (hY : Measurable Y) (N : ℕ) : Measurable (truncR Y N) :=
  (measurable_trunc hY N).ennreal_toReal

lemma ofReal_truncR (Y : Ω → ℝ≥0∞) (N : ℕ) (ω : Ω) :
    ENNReal.ofReal (truncR Y N ω) = trunc Y N ω :=
  ENNReal.ofReal_toReal (trunc_ne_top Y N ω)

lemma lt_truncR_iff (Y : Ω → ℝ≥0∞) (N : ℕ) (ω : Ω) {t : ℝ} (ht : 0 ≤ t) :
    t < truncR Y N ω ↔ ENNReal.ofReal t < trunc Y N ω :=
  (ENNReal.ofReal_lt_iff_lt_toReal ht (trunc_ne_top Y N ω)).symm

/-- Layer cake for the truncation. -/
lemma lintegral_trunc_rpow {Y : Ω → ℝ≥0∞} (hY : Measurable Y) (N : ℕ) {p : ℝ} (hp : 0 < p)
    (P : Measure Ω) :
    ∫⁻ ω, trunc Y N ω ^ p ∂P = ENNReal.ofReal p *
      ∫⁻ t in Set.Ioi (0:ℝ), P {ω | ENNReal.ofReal t < trunc Y N ω} * ENNReal.ofReal (t ^ (p - 1)) := by
  have h := lintegral_rpow_eq_lintegral_meas_lt_mul P (f := truncR Y N)
    (Eventually.of_forall fun ω => truncR_nonneg Y N ω) (measurable_truncR hY N).aemeasurable hp
  have h1 : ∀ ω, ENNReal.ofReal (truncR Y N ω ^ p) = trunc Y N ω ^ p := fun ω => by
    rw [← ENNReal.ofReal_rpow_of_nonneg (truncR_nonneg Y N ω) hp.le, ofReal_truncR]
  simp_rw [h1] at h
  rw [h]
  congr 1
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have hset : {a | t < truncR Y N a} = {ω | ENNReal.ofReal t < trunc Y N ω} := by
    ext ω; simp only [Set.mem_setOf_eq]; exact lt_truncR_iff Y N ω (le_of_lt ht)
  simp only [hset]

/-- Layer cake for `β · trunc` with respect to the measure `X · P`. -/
lemma lintegral_mul_trunc_rpow {X Y : Ω → ℝ≥0∞} (hX : Measurable X) (hY : Measurable Y) (N : ℕ)
    {r : ℝ} (hr : 0 < r) {β : ℝ} (hβ : 0 < β) (P : Measure Ω) [SFinite P] :
    ∫⁻ ω, X ω * (ENNReal.ofReal β * trunc Y N ω) ^ r ∂P = ENNReal.ofReal r *
      ∫⁻ t in Set.Ioi (0:ℝ), (∫⁻ ω in {ω | ENNReal.ofReal (t / β) < trunc Y N ω}, X ω ∂P)
        * ENNReal.ofReal (t ^ (r - 1)) := by
  set ν := P.withDensity X with hν
  set g : Ω → ℝ := fun ω => β * truncR Y N ω with hg
  have hgm : Measurable g := (measurable_truncR hY N).const_mul β
  have hgnn : ∀ ω, 0 ≤ g ω := fun ω => by
    simp only [hg]; exact mul_nonneg hβ.le (truncR_nonneg Y N ω)
  have h := lintegral_rpow_eq_lintegral_meas_lt_mul ν (f := g) (Eventually.of_forall hgnn)
    hgm.aemeasurable hr
  have h1 : ∀ ω, ENNReal.ofReal (g ω ^ r) = (ENNReal.ofReal β * trunc Y N ω) ^ r := fun ω => by
    rw [← ENNReal.ofReal_rpow_of_nonneg (hgnn ω) hr.le]
    simp only [hg]
    rw [ENNReal.ofReal_mul hβ.le, ofReal_truncR]
  simp_rw [h1] at h
  have h2 : ∫⁻ ω, (ENNReal.ofReal β * trunc Y N ω) ^ r ∂ν
      = ∫⁻ ω, X ω * (ENNReal.ofReal β * trunc Y N ω) ^ r ∂P := by
    rw [hν, lintegral_withDensity_eq_lintegral_mul P hX
      (((measurable_trunc hY N).const_mul _).pow_const r)]
    rfl
  rw [← h2, h]
  congr 1
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have hset : {a | t < g a} = {ω | ENNReal.ofReal (t / β) < trunc Y N ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, hg]
    rw [← lt_truncR_iff Y N ω (div_nonneg (le_of_lt ht) hβ.le)]
    constructor
    · intro h; rw [div_lt_iff₀ hβ]; linarith
    · intro h; rw [div_lt_iff₀ hβ] at h; linarith
  simp only [hset, hν, withDensity_apply' X]

/-- The pointwise (in `t`) consequence of the hypothesis (1.2) for the truncation. -/
lemma pointwise_bound {P : Measure Ω} {X Y : Ω → ℝ≥0∞} {α β : ℝ} (hα : 0 < α) (hβ : 1 ≤ β)
    (h12 : ∀ l : ℝ, 0 < l →
      ENNReal.ofReal l * P {ω | ENNReal.ofReal (β * l) < Y ω}
        ≤ ENNReal.ofReal α * ∫⁻ ω in {ω | ENNReal.ofReal l < Y ω}, X ω ∂P)
    (N : ℕ) {p : ℝ} (hp : 1 < p) {t : ℝ} (ht : 0 < t) :
    P {ω | ENNReal.ofReal t < trunc Y N ω} * ENNReal.ofReal (t ^ (p - 1)) ≤
      ENNReal.ofReal (α * β) *
        ((∫⁻ ω in {ω | ENNReal.ofReal (t / β) < trunc Y N ω}, X ω ∂P)
          * ENNReal.ofReal (t ^ (p - 1 - 1))) := by
  have hβ0 : 0 < β := by linarith
  by_cases hN : (N : ℝ) ≤ t
  · have hNt : (N : ℝ≥0∞) ≤ ENNReal.ofReal t := by
      rw [← ENNReal.ofReal_natCast]; exact ENNReal.ofReal_le_ofReal hN
    have : {ω | ENNReal.ofReal t < trunc Y N ω} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      exact (trunc_le_nat Y N ω).trans hNt
    rw [this, measure_empty, zero_mul]
    exact bot_le
  · push_neg at hN
    have htN : ENNReal.ofReal t < (N : ℝ≥0∞) := by
      rw [← ENNReal.ofReal_natCast]; exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hN
    have htβN : ENNReal.ofReal (t / β) < (N : ℝ≥0∞) := by
      refine lt_of_le_of_lt ?_ htN
      apply ENNReal.ofReal_le_ofReal
      rw [div_le_iff₀ hβ0]; nlinarith
    have hset1 : {ω | ENNReal.ofReal t < trunc Y N ω} = {ω | ENNReal.ofReal t < Y ω} := by
      ext ω; simp only [Set.mem_setOf_eq, trunc, lt_min_iff]
      exact ⟨fun h => h.1, fun h => ⟨h, htN⟩⟩
    have hset2 : {ω | ENNReal.ofReal (t / β) < trunc Y N ω}
        = {ω | ENNReal.ofReal (t / β) < Y ω} := by
      ext ω; simp only [Set.mem_setOf_eq, trunc, lt_min_iff]
      exact ⟨fun h => h.1, fun h => ⟨h, htβN⟩⟩
    rw [hset1, hset2]
    have key := h12 (t / β) (by positivity)
    have hβt : β * (t / β) = t := by field_simp
    rw [hβt] at key
    have hc : ENNReal.ofReal (t ^ (p - 1))
        = ENNReal.ofReal (β * t ^ (p - 1 - 1)) * ENNReal.ofReal (t / β) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [Real.rpow_sub_one ht.ne' (p - 1), Real.rpow_sub_one ht.ne' p]
      first | (field_simp; ring) | field_simp
    calc P {ω | ENNReal.ofReal t < Y ω} * ENNReal.ofReal (t ^ (p - 1))
        = ENNReal.ofReal (β * t ^ (p - 1 - 1))
            * (ENNReal.ofReal (t / β) * P {ω | ENNReal.ofReal t < Y ω}) := by rw [hc]; ring
      _ ≤ ENNReal.ofReal (β * t ^ (p - 1 - 1))
            * (ENNReal.ofReal α * ∫⁻ ω in {ω | ENNReal.ofReal (t / β) < Y ω}, X ω ∂P) := by
          gcongr
      _ = _ := by
          rw [ENNReal.ofReal_mul hβ0.le, ENNReal.ofReal_mul hα.le]; ring

lemma q_eq {p q : ℝ} (hp : 1 < p) (hpq : p⁻¹ + q⁻¹ = 1) : q = p / (p - 1) := by
  have h1 : q⁻¹ = (p - 1) / p := by
    have : q⁻¹ = 1 - p⁻¹ := by linarith
    rw [this]; field_simp
  rw [← inv_inv q, h1, inv_div]

lemma q_pos {p q : ℝ} (hp : 1 < p) (hpq : p⁻¹ + q⁻¹ = 1) : 0 < q := by
  rw [q_eq hp hpq]; exact div_pos (by linarith) (by linarith)

/-- The main estimate for the truncation. -/
lemma trunc_bound {P : Measure Ω} [IsProbabilityMeasure P] {X Y : Ω → ℝ≥0∞}
    (hX : Measurable X) (hY : Measurable Y) {α β : ℝ} (hα : 0 < α) (hβ : 1 ≤ β)
    (h12 : ∀ l : ℝ, 0 < l →
      ENNReal.ofReal l * P {ω | ENNReal.ofReal (β * l) < Y ω}
        ≤ ENNReal.ofReal α * ∫⁻ ω in {ω | ENNReal.ofReal l < Y ω}, X ω ∂P)
    (N : ℕ) {p q : ℝ} (hp : 1 < p) (hpq : p⁻¹ + q⁻¹ = 1) :
    ∫⁻ ω, trunc Y N ω ^ p ∂P ≤
      ENNReal.ofReal (α * β ^ p * q) * ∫⁻ ω, X ω * trunc Y N ω ^ (p - 1) ∂P := by
  have hβ0 : 0 < β := by linarith
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  rw [lintegral_trunc_rpow hY N hp0 P]
  have hL2 := lintegral_mul_trunc_rpow hX hY N hp1 hβ0 P
  set J := ∫⁻ t in Set.Ioi (0:ℝ), (∫⁻ ω in {ω | ENNReal.ofReal (t / β) < trunc Y N ω}, X ω ∂P)
        * ENNReal.ofReal (t ^ (p - 1 - 1)) with hJ
  have hJle : ∫⁻ t in Set.Ioi (0:ℝ), P {ω | ENNReal.ofReal t < trunc Y N ω}
      * ENNReal.ofReal (t ^ (p - 1)) ≤ ENNReal.ofReal (α * β) * J := by
    rw [hJ, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact pointwise_bound hα hβ h12 N hp ht
  have hne0 : ENNReal.ofReal (p - 1) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hp1
  have hnet : ENNReal.ofReal (p - 1) ≠ ⊤ := ENNReal.ofReal_ne_top
  calc ENNReal.ofReal p * ∫⁻ t in Set.Ioi (0:ℝ), P {ω | ENNReal.ofReal t < trunc Y N ω}
          * ENNReal.ofReal (t ^ (p - 1))
      ≤ ENNReal.ofReal p * (ENNReal.ofReal (α * β) * J) := by gcongr
    _ = ENNReal.ofReal p * ENNReal.ofReal (α * β) * (ENNReal.ofReal (p - 1))⁻¹
          * (ENNReal.ofReal (p - 1) * J) := by
        rw [mul_assoc _ (ENNReal.ofReal (p - 1))⁻¹, ← mul_assoc (ENNReal.ofReal (p - 1))⁻¹,
          ENNReal.inv_mul_cancel hne0 hnet, one_mul, mul_assoc]
    _ = ENNReal.ofReal p * ENNReal.ofReal (α * β) * (ENNReal.ofReal (p - 1))⁻¹
          * ∫⁻ ω, X ω * (ENNReal.ofReal β * trunc Y N ω) ^ (p - 1) ∂P := by rw [hL2]
    _ = ENNReal.ofReal (α * β ^ p * q) * ∫⁻ ω, X ω * trunc Y N ω ^ (p - 1) ∂P := by
        have hpt : ∀ ω, X ω * (ENNReal.ofReal β * trunc Y N ω) ^ (p - 1)
            = ENNReal.ofReal (β ^ (p - 1)) * (X ω * trunc Y N ω ^ (p - 1)) := fun ω => by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hp1.le,
            ENNReal.ofReal_rpow_of_nonneg hβ0.le hp1.le]
          ring
        simp_rw [hpt]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc]
        congr 1
        rw [← ENNReal.ofReal_inv_of_pos hp1, ← ENNReal.ofReal_mul hp0.le,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [q_eq hp hpq, Real.rpow_sub_one hβ0.ne' p]
        first | (field_simp; ring) | field_simp

/-- Hölder's inequality for the truncation. -/
lemma holder_trunc {P : Measure Ω} {X Y : Ω → ℝ≥0∞}
    (hX : Measurable X) (hY : Measurable Y) (N : ℕ) {p q : ℝ} (hp : 1 < p)
    (hpq : p⁻¹ + q⁻¹ = 1) :
    ∫⁻ ω, X ω * trunc Y N ω ^ (p - 1) ∂P
      ≤ lpNormE P p X * (∫⁻ ω, trunc Y N ω ^ p ∂P) ^ (1 / q) := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := q_pos hp hpq
  have hconj : p.HolderConjugate q := ⟨by rw [inv_one]; exact hpq, hp0, hq0⟩
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq P hconj hX.aemeasurable
    ((measurable_trunc hY N).pow_const (p - 1)).aemeasurable
  have hpow : ∀ ω, (trunc Y N ω ^ (p - 1)) ^ q = trunc Y N ω ^ p := fun ω => by
    rw [← ENNReal.rpow_mul]
    congr 1
    rw [q_eq hp hpq]; field_simp
    exact div_self (by linarith)
  simp_rw [hpow] at h
  exact h

lemma rpow_div_lemma {a K : ℝ≥0∞} (ha : a ≠ ⊤) {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hpq : 1 / p + 1 / q = 1) (h : a ≤ K * a ^ (1 / q)) : a ^ (1 / p) ≤ K := by
  by_cases ha0 : a = 0
  · rw [ha0, ENNReal.zero_rpow_of_pos (by positivity)]; exact bot_le
  have hsplit : a = a ^ (1 / p) * a ^ (1 / q) := by
    rw [← ENNReal.rpow_add _ _ ha0 ha, hpq, ENNReal.rpow_one]
  have hne : a ^ (1 / q) ≠ 0 := by
    intro h0
    rcases ENNReal.rpow_eq_zero_iff.mp h0 with ⟨h, _⟩ | ⟨h, _⟩
    · exact ha0 h
    · exact ha h
  have hnt : a ^ (1 / q) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) ha
  have h' : a ^ (1 / p) * a ^ (1 / q) ≤ K * a ^ (1 / q) := by
    calc a ^ (1 / p) * a ^ (1 / q) = a := hsplit.symm
      _ ≤ K * a ^ (1 / q) := h
  calc a ^ (1 / p) = a ^ (1 / p) * a ^ (1 / q) * (a ^ (1 / q))⁻¹ := by
        rw [mul_assoc, ENNReal.mul_inv_cancel hne hnt, mul_one]
    _ ≤ K * a ^ (1 / q) * (a ^ (1 / q))⁻¹ := by gcongr
    _ = K := by rw [mul_assoc, ENNReal.mul_inv_cancel hne hnt, mul_one]

theorem eq_1_3_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ≥0∞) (hX : Measurable X) (hY : Measurable Y)
    (α β : ℝ) (hα : 0 < α) (hβ : 1 ≤ β)
    (h12 : ∀ l : ℝ, 0 < l →
      ENNReal.ofReal l * P {ω | ENNReal.ofReal (β * l) < Y ω}
        ≤ ENNReal.ofReal α * ∫⁻ ω in {ω | ENNReal.ofReal l < Y ω}, X ω ∂P)
    (p q : ℝ) (hp : 1 < p) (hpq : p⁻¹ + q⁻¹ = 1) :
    lpNormE P p Y ≤ ENNReal.ofReal (α * β ^ p * q) * lpNormE P p X := by
  set C := ENNReal.ofReal (α * β ^ p * q) with hC
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := q_pos hp hpq
  have hfin : ∀ N, ∫⁻ ω, trunc Y N ω ^ p ∂P ≠ ⊤ := by
    intro N
    refine ne_top_of_le_ne_top (b := (N : ℝ≥0∞) ^ p * P Set.univ) ?_ ?_
    · exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hp0.le (ENNReal.natCast_ne_top N))
        (measure_ne_top _ _)
    · calc ∫⁻ ω, trunc Y N ω ^ p ∂P ≤ ∫⁻ ω, (N : ℝ≥0∞) ^ p ∂P :=
            lintegral_mono fun ω => ENNReal.rpow_le_rpow (trunc_le_nat Y N ω) hp0.le
        _ = (N : ℝ≥0∞) ^ p * P Set.univ := lintegral_const _
  have hN : ∀ N, (∫⁻ ω, trunc Y N ω ^ p ∂P) ^ (1 / p) ≤ C * lpNormE P p X := by
    intro N
    apply rpow_div_lemma (hfin N) hp0 hq0 (by simpa [one_div] using hpq)
    calc ∫⁻ ω, trunc Y N ω ^ p ∂P
        ≤ C * ∫⁻ ω, X ω * trunc Y N ω ^ (p - 1) ∂P := trunc_bound hX hY hα hβ h12 N hp hpq
      _ ≤ C * (lpNormE P p X * (∫⁻ ω, trunc Y N ω ^ p ∂P) ^ (1 / q)) := by
          gcongr; exact holder_trunc hX hY N hp hpq
      _ = C * lpNormE P p X * (∫⁻ ω, trunc Y N ω ^ p ∂P) ^ (1 / q) := by ring
  have hsup : ∫⁻ ω, Y ω ^ p ∂P = ⨆ N, ∫⁻ ω, trunc Y N ω ^ p ∂P := by
    rw [← lintegral_iSup (fun N => (measurable_trunc hY N).pow_const p)
      (fun a b hab ω => ENNReal.rpow_le_rpow (trunc_mono Y ω hab) hp0.le)]
    congr 1; funext ω
    rw [← iSup_trunc Y ω]
    exact Monotone.map_iSup_of_continuousAt (f := fun x : ℝ≥0∞ => x ^ p)
      ENNReal.continuous_rpow_const.continuousAt
      (fun a b hab => ENNReal.rpow_le_rpow hab hp0.le) (by simp [ENNReal.zero_rpow_of_pos hp0])
  show (∫⁻ ω, Y ω ^ p ∂P) ^ (1 / p) ≤ C * lpNormE P p X
  rw [hsup]
  have hmono : Monotone fun x : ℝ≥0∞ => x ^ (1 / p) :=
    fun a b hab => ENNReal.rpow_le_rpow hab (by positivity)
  rw [Monotone.map_iSup_of_continuousAt (f := fun x : ℝ≥0∞ => x ^ (1 / p))
      ENNReal.continuous_rpow_const.continuousAt hmono (by
        show (0 : ℝ≥0∞) ^ (1 / p) = 0
        exact ENNReal.zero_rpow_of_pos (by positivity))]
  exact iSup_le hN

end BurkholderDFI.SquareFnLp

open BurkholderDFI.SquareFnLp


theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ≥0∞) (hX : Measurable X) (hY : Measurable Y)
    (α β : ℝ) (hα : 0 < α) (hβ : 1 ≤ β)
    (h12 : ∀ l : ℝ, 0 < l →
      ENNReal.ofReal l * P {ω | ENNReal.ofReal (β * l) < Y ω}
        ≤ ENNReal.ofReal α * ∫⁻ ω in {ω | ENNReal.ofReal l < Y ω}, X ω ∂P)
    (p q : ℝ) (hp : 1 < p) (hpq : p⁻¹ + q⁻¹ = 1) :
    lpNormE P p Y ≤ ENNReal.ofReal (α * β ^ p * q) * lpNormE P p X := by
  exact eq_1_3_core P X Y hX hY α β hα hβ h12 p q hp hpq
