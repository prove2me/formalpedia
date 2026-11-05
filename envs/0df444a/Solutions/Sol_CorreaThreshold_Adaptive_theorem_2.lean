-- Prove2me | solution 1 for CorreaThreshold.Adaptive.theorem_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T20:56:04.77608+00:00
-- url     : https://prove2.me/submissions/6588ab94-dd8c-438f-b815-841e2dd0c017
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_CorreaThreshold_Adaptive_Setting
import Theorems.Thm_CorreaThreshold_Adaptive_lemma_5
import Theorems.Thm_CorreaThreshold_Adaptive_quantile_le_dp
import Theorems.Thm_CorreaThreshold_Adaptive_n_gamma_one_le_beta
import Theorems.Thm_CorreaThreshold_Adaptive_rho_equal_iff

namespace Correa2Red

open MeasureTheory ProbabilityTheory

/-- The recursion (9) for `wᵢ = xᵢ^{n-1}`, started at `w₀ = 1`, with parameter `a = x₁^{n-1}`:
`w_{i+1} = c·max(wᵢ,0)^p + a − c`, where `c = (n-1)/n`, `p = n/(n-1)`. -/
noncomputable def V (c p a : ℝ) : ℕ → ℝ
  | 0 => 1
  | (i + 1) => c * (max (V c p a i) 0) ^ p + a - c

lemma V_zero (c p a : ℝ) : V c p a 0 = 1 := rfl
lemma V_succ (c p a : ℝ) (i : ℕ) : V c p a (i + 1) = c * (max (V c p a i) 0) ^ p + a - c := rfl

lemma V_one (c p a : ℝ) : V c p a 1 = a := by
  simp [V_succ, V_zero]

lemma V_cont (c p : ℝ) (hp : 0 < p) (i : ℕ) : Continuous (fun a => V c p a i) := by
  induction i with
  | zero => simp only [V_zero]; exact continuous_const
  | succ i ih =>
    simp only [V_succ]
    have h1 : Continuous (fun a => (max (V c p a i) 0) ^ p) :=
      (ih.max continuous_const).rpow_const (fun _ => Or.inr hp.le)
    exact ((continuous_const.mul h1).add continuous_id).sub continuous_const

lemma V_at_one (c p : ℝ) (i : ℕ) : V c p 1 i = 1 := by
  induction i with
  | zero => rfl
  | succ i ih => simp [V_succ, ih]

lemma V_at_zero (c p : ℝ) (hc : 0 ≤ c) (hp : 0 < p) (i : ℕ) (hi : 2 ≤ i) : V c p 0 i = -c := by
  induction i with
  | zero => omega
  | succ i ih =>
    rcases Nat.lt_or_ge i 2 with h | h
    · interval_cases i
      · omega
      · show V c p 0 (1 + 1) = -c
        rw [V_succ, V_one, max_self, Real.zero_rpow hp.ne']
        ring
    · rw [V_succ, ih h, max_eq_right (by linarith), Real.zero_rpow hp.ne']
      ring

lemma M_mono {p : ℝ} (hp : 0 < p) {u v : ℝ} (h : u ≤ v) : (max u 0) ^ p ≤ (max v 0) ^ p :=
  Real.rpow_le_rpow (le_max_right _ _) (max_le_max h le_rfl) hp.le

lemma V_succ_le (c p a : ℝ) (hc : 0 ≤ c) (hp : 0 < p) (ha : a ≤ 1) (i : ℕ) :
    V c p a (i + 1) ≤ V c p a i := by
  induction i with
  | zero => rw [V_one, V_zero]; exact ha
  | succ i ih =>
    have e1 := V_succ c p a (i + 1)
    have e2 := V_succ c p a i
    have := mul_le_mul_of_nonneg_left (M_mono hp ih) hc
    linarith

lemma V_anti (c p a : ℝ) (hc : 0 ≤ c) (hp : 0 < p) (ha : a ≤ 1) : Antitone (V c p a) :=
  antitone_nat_of_succ_le (V_succ_le c p a hc hp ha)

lemma V_tail (c p a : ℝ) (hc : 0 ≤ c) (hp : 0 < p) (ha : a ≤ 1) (i : ℕ) (hi : V c p a i ≤ 0)
    (m : ℕ) : V c p a (i + m + 1) = a - c := by
  rw [V_succ]
  have : V c p a (i + m) ≤ 0 := le_trans (V_anti c p a hc hp ha (by omega)) hi
  rw [max_eq_right this, Real.zero_rpow hp.ne']
  ring

lemma V_pos (c p a : ℝ) (hc : 0 < c) (hp : 0 < p) (ha : a ≤ 1) (n : ℕ) (hn : V c p a n = 0) :
    ∀ i < n, 0 < V c p a i := by
  intro i
  induction i with
  | zero => intro _; rw [V_zero]; norm_num
  | succ i ih =>
    intro hi
    have hVi := ih (by omega)
    by_contra h
    replace h := not_lt.mp h
    have ht := V_tail c p a hc.le hp ha (i + 1) h (n - i - 2)
    have he : i + 1 + (n - i - 2) + 1 = n := by omega
    rw [he, hn] at ht
    rw [V_succ, max_eq_left hVi.le] at h
    have := Real.rpow_pos_of_pos hVi p
    nlinarith

lemma V_strict (c p a : ℝ) (hc : 0 < c) (hp : 0 < p) (ha : a < 1) (n : ℕ)
    (hpos : ∀ i < n, 0 < V c p a i) : ∀ i < n, V c p a (i + 1) < V c p a i := by
  intro i
  induction i with
  | zero => intro _; rw [V_one, V_zero]; exact ha
  | succ i ih =>
    intro hi
    have h1 := ih (by omega)
    have hp1 := hpos (i + 1) hi
    have hp0 := hpos i (by omega)
    have e1 := V_succ c p a (i + 1)
    have e2 := V_succ c p a i
    rw [max_eq_left hp1.le] at e1
    rw [max_eq_left hp0.le] at e2
    have := mul_lt_mul_of_pos_left (Real.rpow_lt_rpow hp1.le h1 hp) hc
    linarith

/-- Existence of a solution of the recursion (8) with `x₀ = 1`, `xₙ = 0`, decreasing and positive
in between (the choice of the `εᵢ` in Lemma 5). -/
lemma exists_x (n : ℕ) (hn : 2 ≤ n) :
    ∃ x : ℕ → ℝ, x 0 = 1 ∧ x n = 0 ∧ (∀ i < n, x (i + 1) < x i) ∧ (∀ i < n, 0 < x i) ∧
      ∀ i ∈ Finset.Icc 1 (n - 1),
        ((n : ℝ) - 1) / n * (x (i - 1) ^ n - x i ^ n) = x i ^ (n - 1) - x (i + 1) ^ (n - 1) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  set c : ℝ := ((n : ℝ) - 1) / n with hcdef
  set p : ℝ := (n : ℝ) / ((n : ℝ) - 1) with hpdef
  have hc : 0 < c := div_pos (by linarith) (by linarith)
  have hc1 : c < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hp : 0 < p := div_pos (by linarith) (by linarith)
  -- IVT on `a ↦ V a n`
  have hcont : ContinuousOn (fun a => V c p a n) (Set.Icc 0 1) := (V_cont c p hp n).continuousOn
  have h0 : V c p 0 n = -c := V_at_zero c p hc.le hp n hn
  have h1 : V c p 1 n = 1 := V_at_one c p n
  have hmem : (0 : ℝ) ∈ Set.Icc (V c p 0 n) (V c p 1 n) := by
    rw [h0, h1]; constructor <;> linarith
  obtain ⟨a, ⟨ha0, ha1⟩, hVa⟩ := intermediate_value_Icc (zero_le_one) hcont hmem
  simp only at hVa
  have ha1' : a < 1 := by
    rcases lt_or_eq_of_le ha1 with h | h
    · exact h
    · rw [h, h1] at hVa; norm_num at hVa
  have hpos := V_pos c p a hc hp ha1 n hVa
  have hstr := V_strict c p a hc hp ha1' n hpos
  have hnn : ∀ i ≤ n, 0 ≤ V c p a i := by
    intro i hi
    rcases lt_or_eq_of_le hi with h | h
    · exact (hpos i h).le
    · rw [h, hVa]
  have hk : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  set r : ℝ := 1 / ((n : ℝ) - 1) with hr
  have hr0 : 0 < r := by positivity
  refine ⟨fun i => V c p a i ^ r, ?_, ?_, ?_, ?_, ?_⟩
  · simp [V_zero]
  · simp only [hVa]; exact Real.zero_rpow hr0.ne'
  · intro i hi
    exact Real.rpow_lt_rpow (hnn (i + 1) (by omega)) (hstr i hi) hr0
  · intro i hi
    exact Real.rpow_pos_of_pos (hpos i hi) r
  · -- powers
    have hpow1 : ∀ i ≤ n, (V c p a i ^ r) ^ (n - 1) = V c p a i := by
      intro i hi
      rw [← Real.rpow_natCast, ← Real.rpow_mul (hnn i hi)]
      have : r * ((n - 1 : ℕ) : ℝ) = 1 := by
        rw [Nat.cast_sub (by omega)]; push_cast; rw [hr]; field_simp
      rw [this, Real.rpow_one]
    have hpow2 : ∀ i ≤ n, (V c p a i ^ r) ^ n = (max (V c p a i) 0) ^ p := by
      intro i hi
      rw [← Real.rpow_natCast, ← Real.rpow_mul (hnn i hi), max_eq_left (hnn i hi)]
      congr 1
      rw [hr, hpdef]; field_simp
    intro i hi
    rw [Finset.mem_Icc] at hi
    simp only
    rw [hpow1 i (by omega), hpow1 (i + 1) (by omega), hpow2 (i - 1) (by omega), hpow2 i (by omega)]
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [V_succ c p a (j + 1), V_succ c p a j]
    ring

open CorreaThreshold.Adaptive in
lemma stopReward_zero {n : ℕ} [NeZero n] (x : Fin n → ℝ) (hx : 0 ≤ x 0) :
    stopReward (fun _ : Fin n => (0 : ℝ)) x = x 0 := by
  classical
  unfold stopReward firstReward
  have hmem : (0 : Fin n) ∈ Finset.univ.filter (fun i : Fin n => (0 : ℝ) ≤ x i) := by simp [hx]
  have hne : (Finset.univ.filter (fun i : Fin n => (0 : ℝ) ≤ x i)).Nonempty := ⟨0, hmem⟩
  rw [dif_pos hne]
  congr 1
  exact le_antisymm (Finset.min'_le _ _ hmem) (Fin.zero_le _)

lemma ae_nonneg_zero (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0)
    {n : ℕ} [NeZero n] :
    ∀ᵐ x ∂(SamuelCahnProphet.IID.iidLaw μ n), 0 ≤ x 0 := by
  rw [ae_iff]
  have : {a : Fin n → ℝ | ¬ 0 ≤ a 0} = Function.eval (0 : Fin n) ⁻¹' (Set.Iio 0) := by
    ext a; simp
  rw [this]
  exact Measure.pi_eval_preimage_null (fun _ : Fin n => μ) hμ

lemma lintegral_coord (μ : Measure ℝ) [IsProbabilityMeasure μ] {n : ℕ} [NeZero n] :
    ∫⁻ x, ENNReal.ofReal (x 0) ∂(SamuelCahnProphet.IID.iidLaw μ n) = ∫⁻ y, ENNReal.ofReal y ∂μ :=
  (measurePreserving_eval (fun _ : Fin n => μ) (0 : Fin n)).lintegral_comp
    (f := fun y => ENNReal.ofReal y) ENNReal.measurable_ofReal

open CorreaThreshold.Adaptive in
lemma lintegral_stop_zero (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0)
    {n : ℕ} [NeZero n] :
    ∫⁻ x, ENNReal.ofReal (stopReward (fun _ : Fin n => (0 : ℝ)) x)
        ∂(SamuelCahnProphet.IID.iidLaw μ n) = ∫⁻ y, ENNReal.ofReal y ∂μ := by
  rw [← lintegral_coord μ (n := n)]
  apply lintegral_congr_ae
  filter_upwards [ae_nonneg_zero μ hμ] with x hx
  rw [stopReward_zero x hx]

end Correa2Red

open MeasureTheory ProbabilityTheory CorreaThreshold.Adaptive Correa2Red

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0)
    {n : ℕ} [NeZero n] (β : ℝ) (hβ1 : 1 < β)
    (hβ : ∫ y in (0 : ℝ)..1, 1 / (y * (1 - Real.log y) + (β - 1)) = 1) :
    ∃ τ : Fin n → ℝ, SamuelCahnProphet.IID.Emax μ n ≤
      ENNReal.ofReal β *
        ∫⁻ x, ENNReal.ofReal (stopReward τ x) ∂(SamuelCahnProphet.IID.iidLaw μ n) := by
  have hβ0 : ENNReal.ofReal β ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero]; linarith
  have hβ1' : (1 : ENNReal) ≤ ENNReal.ofReal β := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hβ1.le
  by_cases hint : Integrable (fun x : ℝ => x) μ
  swap
  · -- infinite mean: stop at the first variable
    refine ⟨fun _ => 0, ?_⟩
    rw [lintegral_stop_zero μ hμ]
    have htop : ∫⁻ y, ENNReal.ofReal y ∂μ = ⊤ := by
      by_contra h
      apply hint
      have h0 : 0 ≤ᵐ[μ] (fun x : ℝ => x) := by
        rw [Filter.EventuallyLE, ae_iff]
        convert hμ using 2
        ext a
        simp
      refine ⟨measurable_id.aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal h0]
      exact lt_top_iff_ne_top.2 h
    rw [htop, ENNReal.mul_top hβ0]
    exact le_top
  rcases Nat.lt_or_ge n 2 with hn | hn
  · -- n = 1
    have hn1 : n = 1 := by have := NeZero.ne n; omega
    subst hn1
    refine ⟨fun _ => 0, ?_⟩
    have heq : SamuelCahnProphet.IID.Emax μ 1 =
        ∫⁻ x, ENNReal.ofReal (stopReward (fun _ : Fin 1 => (0 : ℝ)) x)
          ∂(SamuelCahnProphet.IID.iidLaw μ 1) := by
      unfold SamuelCahnProphet.IID.Emax
      apply lintegral_congr_ae
      filter_upwards [ae_nonneg_zero μ hμ] with x hx
      have hm : SamuelCahnProphet.IID.maxV x = x 0 := by
        unfold SamuelCahnProphet.IID.maxV
        apply le_antisymm
        · apply Finset.sup'_le
          intro i _
          rw [Subsingleton.elim i 0]
        · exact Finset.le_sup' x (Finset.mem_univ 0)
      rw [stopReward_zero x hx, hm]
    rw [heq]
    exact le_mul_of_one_le_left bot_le hβ1'
  · obtain ⟨x, hx0, hxn, hxdec, hxpos, hx8⟩ := exists_x n hn
    set ε : ℕ → ℝ := fun i => 1 - x i with hε
    have hε0 : ε 0 = 0 := by simp [hε, hx0]
    have hεn : ε n = 1 := by simp [hε, hxn]
    have hεmono : ∀ i < n, ε i < ε (i + 1) := by
      intro i hi; simp only [hε]; linarith [hxdec i hi]
    have hR := rho_equal_iff hn ε hε0 hεn hεmono
    have hρ : ∀ i ∈ Finset.Icc 1 n, rho n ε i = rho n ε 1 := by
      rw [hR.2.1]
      intro i hi
      simp only [hε, sub_sub_cancel]
      exact hx8 i hi
    have hgam : gam n ε 1 = 1 - x 1 ^ (n - 1) := by
      rw [hR.2.2]; simp [hε]
    have h5 := lemma_5 μ hμ hn ε hε0 hεn hεmono hρ
    have hle := quantile_le_dp μ hμ hint hn ε hε0 hεn hεmono
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hNG : (n : ℝ) * (1 - x 1 ^ (n - 1)) ≤ β := by
      apply n_gamma_one_le_beta hn β hβ1 hβ x hx0 hxn
      · intro i hi; rw [Finset.mem_Icc] at hi; exact hxpos i (by omega)
      · intro i hi
        have h := hx8 i hi
        have hk : (0 : ℝ) < (n : ℝ) - 1 := by linarith
        have hn0 : (0 : ℝ) < n := by linarith
        field_simp
        field_simp at h
        linarith
    refine ⟨tauDP μ n, ?_⟩
    rw [h5, hgam]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal hNG) hle
