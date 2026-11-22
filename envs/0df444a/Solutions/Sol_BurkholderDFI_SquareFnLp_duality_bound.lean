-- Prove2me | solution 1 for BurkholderDFI.SquareFnLp.duality_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T20:12:00.217835+00:00
-- url     : https://prove2.me/submissions/01e8f06b-4cca-4b82-bb08-cecf9b5bc0bf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale
import Theorems.Thm_BurkholderDFI_SquareFnLp_eq_3_7

set_option autoImplicit false

namespace BurkholderDFI.SquareFnLp.DualityProof

open MeasureTheory ProbabilityTheory Filter Topology BurkholderDFI.SquareFnLp Finset
open scoped ENNReal NNReal

variable {Ω : Type*}

theorem measurable_dseq [MeasurableSpace Ω] {g : ℕ → Ω → ℝ} (hg : ∀ k, Measurable (g k))
    (k : ℕ) : Measurable (dseq g k) := by
  by_cases h0 : k = 0
  · subst h0
    have : dseq g 0 = fun _ => (0 : ℝ) := by funext ω; simp [dseq]
    rw [this]
    exact measurable_const
  by_cases h1 : k = 1
  · subst h1
    have : dseq g 1 = g 1 := by funext ω; simp [dseq]
    rw [this]
    exact hg 1
  · have : dseq g k = fun ω => g k ω - g (k - 1) ω := by funext ω; simp [dseq, h0, h1]
    rw [this]
    exact (hg k).sub (hg (k - 1))

theorem measurable_sqFnN [MeasurableSpace Ω] {g : ℕ → Ω → ℝ} (hg : ∀ k, Measurable (g k))
    (n : ℕ) : Measurable (sqFnN g n) := by
  unfold sqFnN
  refine ENNReal.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp ?_)
  exact Finset.measurable_sum _ fun k _ => (measurable_dseq hg k).pow_const 2

theorem memLp_dseq [MeasurableSpace Ω] {μ : Measure Ω} {r : ℝ≥0∞} {h : ℕ → Ω → ℝ}
    (hh : ∀ k, MemLp (h k) r μ) (k : ℕ) : MemLp (dseq h k) r μ := by
  by_cases h0 : k = 0
  · have : dseq h k = 0 := by funext ω; simp [dseq, h0]
    rw [this]
    exact MemLp.zero
  by_cases h1 : k = 1
  · have : dseq h k = h 1 := by funext ω; simp [dseq, h0, h1]
    rw [this]
    exact hh 1
  · have : dseq h k = h k - h (k - 1) := by funext ω; simp [dseq, h0, h1]
    rw [this]
    exact (hh k).sub (hh (k - 1))

/-- The real-valued square function `S_n(f)`. -/
noncomputable def sf (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  Real.sqrt (∑ k ∈ Icc 1 n, dseq f k ω ^ 2)

theorem sf_nonneg (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : 0 ≤ sf f n ω := Real.sqrt_nonneg _

theorem sqFnN_eq (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : sqFnN f n ω = ENNReal.ofReal (sf f n ω) :=
  rfl

theorem dseq_telescope (f : ℕ → Ω → ℝ) (ω : Ω) :
    ∀ m, 1 ≤ m → ∑ k ∈ Icc 1 m, dseq f k ω = f m ω := by
  intro m hm
  induction m with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm'
    · simp [dseq]
    · rw [sum_Icc_succ_top (by omega), ih hm',
        show dseq f (m + 1) ω = f (m + 1) ω - f m ω by simp [dseq, show m ≠ 0 by omega]]
      ring

theorem abs_dseq_le (f : ℕ → Ω → ℝ) (n k : ℕ) (hk : k ∈ Icc 1 n) (ω : Ω) :
    |dseq f k ω| ≤ sf f n ω := by
  unfold sf
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt
    (single_le_sum (f := fun k => dseq f k ω ^ 2) (fun _ _ => sq_nonneg _) hk)

theorem abs_f_le (f : ℕ → Ω → ℝ) (n : ℕ) (hn : 1 ≤ n) (ω : Ω) :
    |f n ω| ≤ Real.sqrt n * sf f n ω := by
  rw [← dseq_telescope f ω n hn]
  unfold sf
  rw [← Real.sqrt_mul (Nat.cast_nonneg n), ← Real.sqrt_sq_eq_abs]
  refine Real.sqrt_le_sqrt ?_
  have := sq_sum_le_card_mul_sum_sq (s := Icc 1 n) (f := fun k => dseq f k ω)
  simpa using this

theorem abs_sum_mul_le (f g : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    |∑ k ∈ Icc 1 n, dseq f k ω * dseq g k ω| ≤ sf f n ω * sf g n ω := by
  unfold sf
  rw [← Real.sqrt_mul (sum_nonneg fun _ _ => sq_nonneg _), ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (sum_mul_sq_le_sq_mul_sq _ _ _)

theorem lpNormE_eq_eLpNorm [MeasurableSpace Ω] (P : Measure Ω) {p : ℝ} (hp : 0 < p)
    (h : Ω → ℝ) :
    lpNormE P p (fun ω => ENNReal.ofReal |h ω|) = eLpNorm h (ENNReal.ofReal p) P := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hp).ne'
    ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp.le]
  unfold lpNormE
  simp_rw [Real.enorm_eq_ofReal_abs]

end BurkholderDFI.SquareFnLp.DualityProof

open MeasureTheory ProbabilityTheory Filter Topology BurkholderDFI.SquareFnLp
  BurkholderDFI.SquareFnLp.DualityProof Finset
open scoped ENNReal NNReal

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P) (n : ℕ) (hn : 1 ≤ n) (p q : ℝ) (hp : 1 < p) (hpq : p⁻¹ + q⁻¹ = 1) :
    lpNormE P p (fun ω => ENNReal.ofReal |f n ω|)
      ≤ ENNReal.ofReal (18 * Real.sqrt q * p) * lpNormE P p (sqFnN f n) := by
  -- Exponents.
  have hp0 : 0 < p := by linarith
  have hqi : q⁻¹ = 1 - p⁻¹ := by linarith
  have hpinv : p⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp
  have hpinv0 : 0 < p⁻¹ := inv_pos.mpr hp0
  have hq0 : 0 < q := inv_pos.mp (by rw [hqi]; linarith)
  have hq1 : 1 < q := by
    have hlt : q⁻¹ < 1 := by rw [hqi]; linarith
    by_contra hcon
    push Not at hcon
    have : 1 ≤ q⁻¹ := one_le_inv_iff₀.mpr ⟨hq0, hcon⟩
    linarith
  have hpq' : q⁻¹ + p⁻¹ = 1 := by linarith
  have hpqmul : (p - 1) * q = p := by
    have h := hpq
    rw [inv_add_inv hp0.ne' hq0.ne', div_eq_one_iff_eq (mul_pos hp0 hq0).ne'] at h
    linear_combination (-1 : ℝ) * h
  have hc : 0 < 18 * Real.sqrt q * p := by
    have := Real.sqrt_pos.mpr hq0
    positivity
  set L := lpNormE P p (sqFnN f n) with hLdef
  -- Trivial if `‖S_n(f)‖_p = ∞`.
  by_cases hLtop : L = ⊤
  · rw [hLtop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hc).ne']
    exact le_top
  -- Measurability and `L^p` membership.
  have hfm : ∀ k, Measurable (f k) := fun k => ((hf.1 k).mono (ℱ.le k)).measurable
  have hsfm : Measurable (sf f n) := by
    unfold sf
    exact Real.continuous_sqrt.measurable.comp
      (Finset.measurable_sum _ fun k _ => (measurable_dseq hfm k).pow_const 2)
  have hLeq : L = eLpNorm (sf f n) (ENNReal.ofReal p) P := by
    rw [hLdef, ← lpNormE_eq_eLpNorm P hp0]
    congr 1
    funext ω
    rw [sqFnN_eq, abs_of_nonneg (sf_nonneg f n ω)]
  have hsfLp : MemLp (sf f n) (ENNReal.ofReal p) P :=
    ⟨hsfm.aestronglyMeasurable, by rw [← hLeq]; exact lt_top_iff_ne_top.mpr hLtop⟩
  have hdLp : ∀ k ∈ Icc 1 n, MemLp (dseq f k) (ENNReal.ofReal p) P := fun k hk =>
    hsfLp.of_le (measurable_dseq hfm k).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sf_nonneg f n ω)]
        exact abs_dseq_le f n k hk ω)
  have hfnLp : MemLp (f n) (ENNReal.ofReal p) P :=
    (hsfLp.const_mul (Real.sqrt n)).of_le (hfm n).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
          abs_of_nonneg (sf_nonneg f n ω)]
        exact abs_f_le f n hn ω)
  -- `B = E|f_n|^p`, so that the left side is `B^{1/p}`.
  set B : ℝ≥0∞ := ∫⁻ ω, ENNReal.ofReal |f n ω| ^ p ∂P with hBdef
  have hA : lpNormE P p (fun ω => ENNReal.ofReal |f n ω|) = B ^ (1 / p) := rfl
  have hBtop : B ≠ ⊤ := by
    have h1 : B ^ (1 / p) < ⊤ := by
      rw [← hA, lpNormE_eq_eLpNorm P hp0]
      exact hfnLp.2
    exact ((ENNReal.rpow_lt_top_iff_of_pos (by positivity)).mp h1).ne
  by_cases hB0 : B = 0
  · rw [hA, hB0, ENNReal.zero_rpow_of_pos (by positivity)]
    exact zero_le
  -- The dual function `Y = f_n |f_n|^{p-2}`.
  set Y : Ω → ℝ := fun ω => f n ω * |f n ω| ^ (p - 2) with hYdef
  have hYabs : ∀ ω, |Y ω| = |f n ω| ^ (p - 1) := by
    intro ω
    simp only [hYdef]
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    by_cases h0 : f n ω = 0
    · rw [h0, abs_zero, zero_mul, Real.zero_rpow (by linarith)]
    · have hpos : 0 < |f n ω| := abs_pos.mpr h0
      rw [show p - 1 = 1 + (p - 2) by ring, Real.rpow_add hpos, Real.rpow_one]
  have hfY : ∀ ω, f n ω * Y ω = |f n ω| ^ p := by
    intro ω
    simp only [hYdef]
    by_cases h0 : f n ω = 0
    · rw [h0, zero_mul, abs_zero, Real.zero_rpow hp0.ne']
    · have hpos : 0 < |f n ω| := abs_pos.mpr h0
      rw [← mul_assoc, ← sq, ← sq_abs, show p = 2 + (p - 2) by ring, Real.rpow_add hpos,
        Real.rpow_two]
      ring_nf
  have hYq : ∀ ω, |Y ω| ^ q = |f n ω| ^ p := by
    intro ω
    rw [hYabs, ← Real.rpow_mul (abs_nonneg _), hpqmul]
  have hh : Measurable (fun x : ℝ => x * |x| ^ (p - 2)) :=
    measurable_id.mul (measurable_id.abs.pow_const _)
  have hfn_m : Measurable[ℱ n] (f n) := (hf.1 n).measurable
  have hYmn : Measurable[ℱ n] Y := hh.comp hfn_m
  have hYm : Measurable Y := hYmn.mono (ℱ.le n) le_rfl
  have hBY : ∫⁻ ω, ENNReal.ofReal |Y ω| ^ q ∂P = B := by
    rw [hBdef]
    refine lintegral_congr fun ω => ?_
    rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hq0.le,
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp0.le, hYq]
  have hYLp : MemLp Y (ENNReal.ofReal q) P := by
    refine ⟨hYm.aestronglyMeasurable, ?_⟩
    rw [← lpNormE_eq_eLpNorm P hq0]
    unfold lpNormE
    rw [hBY]
    exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hBtop
  have hq1' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := ENNReal.one_le_ofReal.mpr hq1.le
  have hYint : Integrable Y P := hYLp.integrable hq1'
  -- The dual martingale `g_k = E[Y | ℱ_k]`.
  set g : ℕ → Ω → ℝ := fun k => P[Y | ℱ k] with hgdef
  have hg : Martingale g ℱ P := martingale_condExp Y ℱ P
  have hgn : g n = Y := condExp_of_stronglyMeasurable (ℱ.le n) hYmn.stronglyMeasurable hYint
  have hgLp : ∀ k, MemLp (g k) (ENNReal.ofReal q) P := fun k => hYLp.condExp hq1'
  have heLp : ∀ k, MemLp (dseq g k) (ENNReal.ofReal q) P := memLp_dseq hgLp
  have : ENNReal.HolderTriple (ENNReal.ofReal p) (ENNReal.ofReal q) 1 := ⟨by
    rw [inv_one, ← ENNReal.ofReal_inv_of_pos hp0, ← ENNReal.ofReal_inv_of_pos hq0,
      ← ENNReal.ofReal_add hpinv0.le (inv_pos.mpr hq0).le, hpq, ENNReal.ofReal_one]⟩
  -- Orthogonality: `E[d_k Y] = E[d_k e_k]` for `1 ≤ k ≤ n`.
  have horth : ∀ k ∈ Icc 1 n,
      ∫ ω, dseq f k ω * Y ω ∂P = ∫ ω, dseq f k ω * dseq g k ω ∂P := by
    intro k hk
    rw [mem_Icc] at hk
    have hdkm : Measurable[ℱ k] (dseq f k) := by
      have hfk : ∀ j, j ≤ k → Measurable[ℱ k] (f j) := fun j hj =>
        ((hf.1 j).mono (ℱ.mono hj)).measurable
      by_cases h1 : k = 1
      · have : dseq f k = f 1 := by funext ω; simp [dseq, h1]
        rw [this]
        exact hfk 1 (by omega)
      · have : dseq f k = fun ω => f k ω - f (k - 1) ω := by
          funext ω; simp [dseq, show k ≠ 0 by omega, h1]
        rw [this]
        exact (hfk k le_rfl).sub (hfk (k - 1) (by omega))
    have hdY : Integrable (fun ω => dseq f k ω * Y ω) P := (hdLp k (mem_Icc.mpr hk)).integrable_mul hYLp
    -- `E[d_k Y] = E[d_k g_k]`.
    have hstep1 : ∫ ω, dseq f k ω * Y ω ∂P = ∫ ω, dseq f k ω * g k ω ∂P := by
      have hpull := condExp_mul_of_stronglyMeasurable_left (m := ℱ k) hdkm.stronglyMeasurable hdY
        hYint
      rw [← integral_condExp (ℱ.le k)]
      exact integral_congr_ae hpull
    rw [hstep1]
    by_cases h1 : k = 1
    · subst h1
      have : dseq g 1 = g 1 := by funext ω; simp [dseq]
      rw [this]
    · -- `g_k = e_k + g_{k-1}` and `E[d_k g_{k-1}] = 0`.
      have hgk : ∀ ω, g k ω = dseq g k ω + g (k - 1) ω := by
        intro ω
        simp [dseq, show k ≠ 0 by omega, h1]
      have hde : Integrable (fun ω => dseq f k ω * dseq g k ω) P :=
        (hdLp k (mem_Icc.mpr hk)).integrable_mul (heLp k)
      have hdg : Integrable (fun ω => dseq f k ω * g (k - 1) ω) P :=
        (hdLp k (mem_Icc.mpr hk)).integrable_mul (hgLp (k - 1))
      have hzero : ∫ ω, dseq f k ω * g (k - 1) ω ∂P = 0 := by
        have hdk : Integrable (dseq f k) P := (hdLp k (mem_Icc.mpr hk)).integrable
          (ENNReal.one_le_ofReal.mpr hp.le)
        have hgd : Integrable (fun ω => g (k - 1) ω * dseq f k ω) P := by
          simpa [mul_comm] using hdg
        have hpull := condExp_mul_of_stronglyMeasurable_left (m := ℱ (k - 1))
          (stronglyMeasurable_condExp (f := Y)) hgd hdk
        -- `E[d_k | ℱ_{k-1}] = 0`.
        have hce : P[dseq f k | ℱ (k - 1)] =ᵐ[P] 0 := by
          have hd : dseq f k = f k - f (k - 1) := by
            funext ω; simp [dseq, show k ≠ 0 by omega, h1]
          rw [hd]
          have h1' := condExp_sub (hf.integrable k) (hf.integrable (k - 1)) (ℱ (k - 1))
          have h2' := hf.condExp_ae_eq (show k - 1 ≤ k by omega)
          have h3' : P[f (k - 1) | ℱ (k - 1)] = f (k - 1) :=
            condExp_of_stronglyMeasurable (ℱ.le (k - 1)) (hf.1 (k - 1)) (hf.integrable (k - 1))
          filter_upwards [h1', h2'] with ω h1ω h2ω
          rw [h1ω, Pi.sub_apply, h2ω, h3']
          simp
        calc ∫ ω, dseq f k ω * g (k - 1) ω ∂P
            = ∫ ω, g (k - 1) ω * dseq f k ω ∂P := by simp_rw [mul_comm]
          _ = ∫ ω, P[fun ω => g (k - 1) ω * dseq f k ω | ℱ (k - 1)] ω ∂P :=
              (integral_condExp (ℱ.le (k - 1))).symm
          _ = ∫ ω, g (k - 1) ω * P[dseq f k | ℱ (k - 1)] ω ∂P := integral_congr_ae hpull
          _ = 0 := by
              refine integral_eq_zero_of_ae ?_
              filter_upwards [hce] with ω hω
              simp [hω]
      calc ∫ ω, dseq f k ω * g k ω ∂P
          = ∫ ω, (dseq f k ω * dseq g k ω + dseq f k ω * g (k - 1) ω) ∂P := by
            congr 1; funext ω; rw [hgk ω]; ring
        _ = ∫ ω, dseq f k ω * dseq g k ω ∂P := by
            rw [integral_add hde hdg, hzero, add_zero]
  -- `E|f_n|^p = E[f_n Y] = Σ_k E[d_k e_k] = E[Σ_k d_k e_k]`.
  have hsum : ∫ ω, |f n ω| ^ p ∂P = ∫ ω, ∑ k ∈ Icc 1 n, dseq f k ω * dseq g k ω ∂P := by
    calc ∫ ω, |f n ω| ^ p ∂P = ∫ ω, ∑ k ∈ Icc 1 n, dseq f k ω * Y ω ∂P := by
          congr 1; funext ω
          rw [← hfY ω, ← dseq_telescope f ω n hn, sum_mul]
      _ = ∑ k ∈ Icc 1 n, ∫ ω, dseq f k ω * Y ω ∂P :=
          integral_finsetSum _ fun k hk => (hdLp k hk).integrable_mul hYLp
      _ = ∑ k ∈ Icc 1 n, ∫ ω, dseq f k ω * dseq g k ω ∂P := sum_congr rfl horth
      _ = ∫ ω, ∑ k ∈ Icc 1 n, dseq f k ω * dseq g k ω ∂P :=
          (integral_finsetSum _ fun k hk => (hdLp k hk).integrable_mul (heLp k)).symm
  -- `B ≤ L · ‖S_n(g)‖_q`.
  have hgm : ∀ k, Measurable (g k) := fun k =>
    (stronglyMeasurable_condExp.mono (ℱ.le k)).measurable
  have hfpint : Integrable (fun ω => |f n ω| ^ p) P := by
    have := hfnLp.integrable_norm_rpow (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top
    simpa [ENNReal.toReal_ofReal hp0.le] using this
  have hB1 : B ≤ L * lpNormE P q (sqFnN g n) := by
    calc B = ENNReal.ofReal (∫ ω, |f n ω| ^ p ∂P) := by
          rw [hBdef, ofReal_integral_eq_lintegral_ofReal hfpint
            (Eventually.of_forall fun ω => Real.rpow_nonneg (abs_nonneg _) _)]
          refine lintegral_congr fun ω => ?_
          rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp0.le]
      _ = ENNReal.ofReal (∫ ω, ∑ k ∈ Icc 1 n, dseq f k ω * dseq g k ω ∂P) := by rw [hsum]
      _ ≤ ‖∫ ω, ∑ k ∈ Icc 1 n, dseq f k ω * dseq g k ω ∂P‖ₑ := by
          rw [Real.enorm_eq_ofReal_abs]
          exact ENNReal.ofReal_le_ofReal (le_abs_self _)
      _ ≤ ∫⁻ ω, ‖∑ k ∈ Icc 1 n, dseq f k ω * dseq g k ω‖ₑ ∂P :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ ω, (sqFnN f n * sqFnN g n) ω ∂P := by
          refine lintegral_mono fun ω => ?_
          rw [Real.enorm_eq_ofReal_abs, Pi.mul_apply, sqFnN_eq, sqFnN_eq,
            ← ENNReal.ofReal_mul (sf_nonneg f n ω)]
          exact ENNReal.ofReal_le_ofReal (abs_sum_mul_le f g n ω)
      _ ≤ L * lpNormE P q (sqFnN g n) := by
          have hH : p.HolderConjugate q := ⟨by rw [inv_one]; exact hpq, hp0, hq0⟩
          exact ENNReal.lintegral_mul_le_Lp_mul_Lq P hH
            (measurable_sqFnN hfm n).aemeasurable (measurable_sqFnN hgm n).aemeasurable
  -- (3.7) for `g` with the exponents exchanged, and `‖g_n‖_q = B^{1/q}`.
  have h37 := eq_3_7 hg n hn q p hq1 hpq'
  have hgnorm : lpNormE P q (fun ω => ENNReal.ofReal |g n ω|) = B ^ (1 / q) := by
    rw [hgn]
    unfold lpNormE
    rw [hBY]
  rw [hgnorm] at h37
  have hB2 : B ≤ L * (ENNReal.ofReal (18 * Real.sqrt q * p) * B ^ (1 / q)) :=
    hB1.trans (mul_le_mul' le_rfl h37)
  -- Cancel `B^{1/q}`.
  have hsplit : B = B ^ (1 / q) * B ^ (1 / p) := by
    rw [← ENNReal.rpow_add _ _ hB0 hBtop, one_div, one_div, hpq', ENNReal.rpow_one]
  have hBq0 : B ^ (1 / q) ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hB0) hBtop).ne'
  have hBqtop : B ^ (1 / q) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hBtop
  rw [hA]
  have h3 : B ^ (1 / q) * B ^ (1 / p)
      ≤ B ^ (1 / q) * (ENNReal.ofReal (18 * Real.sqrt q * p) * L) := by
    rw [← hsplit]
    calc B ≤ L * (ENNReal.ofReal (18 * Real.sqrt q * p) * B ^ (1 / q)) := hB2
      _ = B ^ (1 / q) * (ENNReal.ofReal (18 * Real.sqrt q * p) * L) := by ring
  exact (ENNReal.mul_le_mul_iff_right hBq0 hBqtop).mp h3
