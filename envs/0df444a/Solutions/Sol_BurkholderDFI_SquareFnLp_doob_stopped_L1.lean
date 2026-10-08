-- Prove2me | solution 1 for BurkholderDFI.SquareFnLp.doob_stopped_L1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T10:49:07.839642+00:00
-- url     : https://prove2.me/submissions/5134e782-793d-4049-a7c6-5873464d2e8d

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace BurkholderDFI.SquareFnLp

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}

/-- `|f_n|` with the convention `f_0 = 0`. -/
noncomputable def absZ (f : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun n ω => if n = 0 then 0 else |f n ω|

lemma absZ_nonneg (f : ℕ → Ω → ℝ) : 0 ≤ absZ f := by
  intro n ω
  simp only [absZ, Pi.zero_apply]
  split_ifs <;> simp [abs_nonneg]

lemma absZ_pos (f : ℕ → Ω → ℝ) {n : ℕ} (hn : 1 ≤ n) : absZ f n = fun ω => |f n ω| := by
  funext ω; simp [absZ, Nat.one_le_iff_ne_zero.mp hn]

lemma absZ_zero (f : ℕ → Ω → ℝ) : absZ f 0 = 0 := by
  funext ω; simp [absZ]

lemma absZ_submartingale [IsFiniteMeasure P]
    (hf : Martingale f ℱ P ∨ (Submartingale f ℱ P ∧ ∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n)) :
    Submartingale (absZ f) ℱ P := by
  have hsub : Submartingale f ℱ P := hf.elim (fun h => h.submartingale) (fun h => h.1)
  have hadp : StronglyAdapted ℱ (absZ f) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [absZ_zero]; exact stronglyMeasurable_const
    · rw [absZ_pos f hn]
      have := (hsub.stronglyAdapted n).norm
      simpa [Real.norm_eq_abs] using this
  have hint : ∀ n, Integrable (absZ f n) P := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [absZ_zero]; exact integrable_zero _ _ _
    · rw [absZ_pos f hn]; exact (hsub.integrable n).abs
  refine ⟨hadp, fun i j hij => ?_, hint⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [absZ_zero]
    exact condExp_nonneg (Eventually.of_forall (absZ_nonneg f j))
  · have hj : 1 ≤ j := le_trans hi hij
    rw [absZ_pos f hi, absZ_pos f hj]
    rcases hf with hm | ⟨hs, hnn⟩
    · have h := (hm.submartingale.sup hm.neg.submartingale).2.1 i j hij
      have e : ∀ k, (f ⊔ -f) k = fun ω => |f k ω| := by
        intro k; funext ω; simp [abs_eq_max_neg]
      simpa [e] using h
    · have h1 := hs.2.1 i j hij
      have e1 : f i =ᵐ[P] fun ω => |f i ω| := by
        filter_upwards [hnn i hi] with ω hω; simp [abs_of_nonneg hω]
      have e2 : f j =ᵐ[P] fun ω => |f j ω| := by
        filter_upwards [hnn j hj] with ω hω; simp [abs_of_nonneg hω]
      have h2 : P[f j | ℱ i] =ᵐ[P] P[fun ω => |f j ω| | ℱ i] := condExp_congr_ae e2
      filter_upwards [h1, e1, h2] with ω h1 e1 h2
      rw [← e1, ← h2]; exact h1


lemma abs_valAt_coe (f : ℕ → Ω → ℝ) (fInf : Ω → ℝ) (k : ℕ) (ω : Ω) :
    |valAt f fInf (k : ℕ∞) ω| = absZ f k ω := by
  by_cases hk : k = 0
  · subst hk; simp [valAt, absZ]
  · simp [valAt, absZ, hk]

lemma untopA_coe' (n : ℕ) : ((n : ℕ∞)).untopA = n := rfl

lemma abs_valAt_untopA (f : ℕ → Ω → ℝ) (fInf : Ω → ℝ) (t : ℕ∞) (ht : t ≠ ⊤) (ω : Ω) :
    |valAt f fInf t ω| = absZ f t.untopA ω := by
  induction t using ENat.recTopCoe with
  | top => exact absurd rfl ht
  | coe k => exact abs_valAt_coe f fInf k ω

lemma stoppedValue_coe_eq (f : ℕ → Ω → ℝ) (fInf : Ω → ℝ) (μ : Ω → ℕ∞) (n : ℕ) (ω : Ω) :
    ENNReal.ofReal |valAt f fInf (min (μ ω) n) ω|
      = ENNReal.ofReal (stoppedValue (absZ f) (fun ω => min (μ ω) n) ω) := by
  have ht : min (μ ω) (n : ℕ∞) ≠ ⊤ :=
    ne_top_of_le_ne_top (WithTop.coe_ne_top) (min_le_right _ _)
  rw [stoppedValue, abs_valAt_untopA f fInf _ ht]; rfl

lemma eLpNorm_one_le_pNorm (P : Measure Ω) (f : ℕ → Ω → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    eLpNorm (f n) 1 P ≤ pNorm P 1 f := by
  refine le_trans ?_ (le_iSup₂ (f := fun n (_ : n ∈ Set.Ici 1) =>
    lpNormE P 1 (fun ω => ENNReal.ofReal |f n ω|)) n hn)
  simp only [lpNormE, ENNReal.rpow_one, one_div, inv_one, eLpNorm_one_eq_lintegral_enorm,
    Real.enorm_eq_ofReal_abs]
  exact le_rfl

theorem doob_stopped_L1_core {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P ∨ (Submartingale f ℱ P ∧ ∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n))
    (hL1 : BurkholderDFI.SquareFnLp.pNorm P 1 f < ⊤) (μ : Ω → ℕ∞) (hμ : IsStoppingTime ℱ μ) :
    ∃ fInf : Ω → ℝ, (∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (fInf ω))) ∧
      ∫⁻ ω, ENNReal.ofReal |BurkholderDFI.SquareFnLp.valAt f fInf (μ ω) ω| ∂P ≤ BurkholderDFI.SquareFnLp.pNorm P 1 f := by
  have hsub : Submartingale f ℱ P := hf.elim (fun h => h.submartingale) (fun h => h.1)
  have hG := absZ_submartingale hf
  -- a.e. convergence
  set R : ℝ≥0 := (max (eLpNorm (f 0) 1 P) (pNorm P 1 f)).toNNReal with hR
  have hRtop : max (eLpNorm (f 0) 1 P) (pNorm P 1 f) ≠ ⊤ := by
    have h0 : eLpNorm (f 0) 1 P < ⊤ :=
      (memLp_one_iff_integrable.mpr (hsub.integrable 0)).eLpNorm_lt_top
    exact (max_lt h0 hL1).ne
  have hbdd : ∀ n, eLpNorm (f n) 1 P ≤ R := by
    intro n
    rw [hR, ENNReal.coe_toNNReal hRtop]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact le_max_left _ _
    · exact (eLpNorm_one_le_pNorm P f hn).trans (le_max_right _ _)
  have hlim := hsub.ae_tendsto_limitProcess hbdd
  set fInf := ℱ.limitProcess f P with hfInf
  refine ⟨fInf, hlim, ?_⟩
  -- the L¹ bound via Fatou and optional stopping
  set τ : ℕ → Ω → ℕ∞ := fun n ω => min (μ ω) n with hτdef
  have hτ : ∀ n, IsStoppingTime ℱ (τ n) := fun n => hμ.min_const n
  have hτle : ∀ n ω, τ n ω ≤ n := fun n ω => min_le_right _ _
  set u : ℕ → Ω → ℝ≥0∞ := fun n ω => ENNReal.ofReal |valAt f fInf (τ n ω) ω| with hu
  have hu_eq : ∀ n, u n = fun ω => ENNReal.ofReal (stoppedValue (absZ f) (τ n) ω) := by
    intro n; funext ω; exact stoppedValue_coe_eq f fInf μ n ω
  have hu_meas : ∀ n, AEMeasurable (u n) P := by
    intro n; rw [hu_eq n]
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      (hG.integrable_stoppedValue (hτ n) (hτle n)).aemeasurable
  have hu_bound : ∀ n, 1 ≤ n → ∫⁻ ω, u n ω ∂P ≤ pNorm P 1 f := by
    intro n hn
    have hrw : ∫⁻ ω, u n ω ∂P
        = ∫⁻ ω, ENNReal.ofReal (stoppedValue (absZ f) (τ n) ω) ∂P := by
      rw [hu_eq n]
    rw [hrw]
    have hnn : ∀ τ : Ω → ℕ∞, 0 ≤ᵐ[P] stoppedValue (absZ f) τ :=
      fun τ => Eventually.of_forall fun ω => absZ_nonneg f _ ω
    rw [← ofReal_integral_eq_lintegral_ofReal
      (hG.integrable_stoppedValue (hτ n) (hτle n)) (hnn _)]
    have hos := hG.expected_stoppedValue_mono (hτ n) (isStoppingTime_const ℱ n)
      (hτle n) (N := n) (fun ω => le_rfl)
    rw [stoppedValue_const] at hos
    calc ENNReal.ofReal (∫ ω, stoppedValue (absZ f) (τ n) ω ∂P)
        ≤ ENNReal.ofReal (∫ ω, absZ f n ω ∂P) := ENNReal.ofReal_le_ofReal hos
      _ = ∫⁻ ω, ENNReal.ofReal (absZ f n ω) ∂P :=
          ofReal_integral_eq_lintegral_ofReal (hG.integrable n)
            (Eventually.of_forall (absZ_nonneg f n))
      _ = eLpNorm (f n) 1 P := by
          rw [eLpNorm_one_eq_lintegral_enorm, absZ_pos f hn]
          simp only [Real.enorm_eq_ofReal_abs]
      _ ≤ pNorm P 1 f := eLpNorm_one_le_pNorm P f hn
  have hconv : ∀ᵐ ω ∂P, Tendsto (fun n => u n ω) atTop
      (𝓝 (ENNReal.ofReal |valAt f fInf (μ ω) ω|)) := by
    filter_upwards [hlim] with ω hω
    show Tendsto (fun n : ℕ => ENNReal.ofReal |valAt f fInf (min (μ ω) (n : ℕ∞)) ω|) atTop _
    by_cases hμω : μ ω = ⊤
    · rw [hμω]
      have hmin : ∀ n : ℕ, min (⊤ : ℕ∞) n = n := fun n => min_eq_right le_top
      simp only [hmin]
      have hv : valAt f fInf ⊤ ω = fInf ω := by simp [valAt]
      rw [hv]
      have h1 : Tendsto (fun n => ENNReal.ofReal |f n ω|) atTop (𝓝 (ENNReal.ofReal |fInf ω|)) :=
        (ENNReal.continuous_ofReal.tendsto _).comp ((continuous_abs.tendsto _).comp hω)
      refine h1.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      simp [valAt, Nat.one_le_iff_ne_zero.mp hn]
    · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hμω
      rw [← hm]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop m] with n hn
      have : min (m : ℕ∞) n = m := min_eq_left (by exact_mod_cast hn)
      rw [this]
  have hliminf : (fun ω => ENNReal.ofReal |valAt f fInf (μ ω) ω|)
      =ᵐ[P] fun ω => liminf (fun n => u n ω) atTop := by
    filter_upwards [hconv] with ω hω
    exact hω.liminf_eq.symm
  calc ∫⁻ ω, ENNReal.ofReal |valAt f fInf (μ ω) ω| ∂P
      = ∫⁻ ω, liminf (fun n => u n ω) atTop ∂P := lintegral_congr_ae hliminf
    _ ≤ liminf (fun n => ∫⁻ ω, u n ω ∂P) atTop := lintegral_liminf_le' hu_meas
    _ ≤ pNorm P 1 f := by
        apply Filter.liminf_le_of_frequently_le'
        exact (Filter.eventually_atTop.mpr ⟨1, fun n hn => hu_bound n hn⟩).frequently

end BurkholderDFI.SquareFnLp

open BurkholderDFI.SquareFnLp


theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P ∨ (Submartingale f ℱ P ∧ ∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n))
    (hL1 : pNorm P 1 f < ⊤) (μ : Ω → ℕ∞) (hμ : IsStoppingTime ℱ μ) :
    ∃ fInf : Ω → ℝ, (∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (fInf ω))) ∧
      ∫⁻ ω, ENNReal.ofReal |valAt f fInf (μ ω) ω| ∂P ≤ pNorm P 1 f := by
  exact doob_stopped_L1_core hf hL1 μ hμ
