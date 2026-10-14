-- Prove2me | solution 1 for DbarRegularity.eLpNorm_le_of_forall_enorm_integral_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T17:00:39.949836+00:00
-- url     : https://prove2.me/submissions/7c93ea2d-9410-4fb2-a380-d65e89979b93

import Definitions.Def_DbarRegularity_Setting
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity



namespace DbarRegularity

open MeasureTheory Set Metric
open scoped ENNReal

/-- `L^p` norm by testing: if `|∫ h g| ≤ M ‖g‖_q` (with `1/p + 1/q = 1`, `1 < p < ∞`) for every
`g : ℝ^d → ℂ` lying in every `L^r`, `1 ≤ r ≤ ∞`, then `‖h‖_p ≤ M`. -/
theorem eLpNorm_le_of_forall_enorm_integral_mul_le {d : ℕ} {h : EuclideanSpace ℝ (Fin d) → ℂ}
    (hh : AEStronglyMeasurable h volume) {p q : ℝ} (hp : 1 < p) (hq : q = p / (p - 1))
    (M : ℝ≥0∞)
    (H : ∀ g : EuclideanSpace ℝ (Fin d) → ℂ, (∀ r : ℝ≥0∞, 1 ≤ r → MemLp g r volume) →
      ‖∫ x, h x * g x‖ₑ ≤ M * eLpNorm g (ENNReal.ofReal q) volume) :
    eLpNorm h (ENNReal.ofReal p) volume ≤ M := by
  have hp0 : 0 < p := by linarith
  have hp1 : p - 1 ≠ 0 := by linarith
  have hq0 : 0 < q := by rw [hq]; exact div_pos hp0 (by linarith)
  have hpq : (p - 1) * q = p := by rw [hq]; field_simp
  have hpq' : 1 / p + 1 / q = 1 := by rw [hq]; field_simp; try ring
  set h' := hh.mk h with hh'
  have hm : StronglyMeasurable h' := hh.stronglyMeasurable_mk
  have hae : h =ᵐ[volume] h' := hh.ae_eq_mk
  have hm' : Measurable h' := hm.measurable
  -- pointwise identities
  have hprod : ∀ z : ℂ, z * (((‖z‖ ^ (p - 2) : ℝ) : ℂ) * (starRingEnd ℂ) z) =
      ((‖z‖ ^ p : ℝ) : ℂ) := by
    intro z
    by_cases hz : z = 0
    · simp [hz, Real.zero_rpow hp0.ne']
    · have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
      have h2 : z * (starRingEnd ℂ) z = ((‖z‖ ^ (2 : ℝ) : ℝ) : ℂ) := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Real.rpow_two]
      calc z * (((‖z‖ ^ (p - 2) : ℝ) : ℂ) * (starRingEnd ℂ) z)
          = ((‖z‖ ^ (p - 2) : ℝ) : ℂ) * (z * (starRingEnd ℂ) z) := by ring
        _ = ((‖z‖ ^ (p - 2) : ℝ) : ℂ) * ((‖z‖ ^ (2 : ℝ) : ℝ) : ℂ) := by rw [h2]
        _ = ((‖z‖ ^ p : ℝ) : ℂ) := by
            rw [← Complex.ofReal_mul, ← Real.rpow_add hn, sub_add_cancel]
  have hnorm : ∀ z : ℂ, ‖((‖z‖ ^ (p - 2) : ℝ) : ℂ) * (starRingEnd ℂ) z‖ = ‖z‖ ^ (p - 1) := by
    intro z
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
      Complex.norm_conj]
    by_cases hz : z = 0
    · simp [hz, Real.zero_rpow hp1]
    · rw [← Real.rpow_add_one (norm_ne_zero_iff.2 hz)]; congr 1; ring
  -- truncation sets
  set E : ℕ → Set (EuclideanSpace ℝ (Fin d)) := fun N => {x | ‖x‖ ≤ N ∧ ‖h' x‖ ≤ N} with hEdef
  have hE : ∀ N, MeasurableSet (E N) := fun N =>
    (measurableSet_le measurable_norm measurable_const).inter
      (measurableSet_le hm'.norm measurable_const)
  have hEfin : ∀ N, volume (E N) < ⊤ := fun N =>
    (measure_mono fun x hx => by
      simpa [mem_closedBall, dist_zero_right] using hx.1).trans_lt
      (measure_closedBall_lt_top (x := (0 : EuclideanSpace ℝ (Fin d))) (r := N))
  set G : EuclideanSpace ℝ (Fin d) → ℂ :=
    fun x => ((‖h' x‖ ^ (p - 2) : ℝ) : ℂ) * (starRingEnd ℂ) (h' x) with hGdef
  have hGm : Measurable G := by
    simp only [hGdef]
    exact (Complex.measurable_ofReal.comp (hm'.norm.pow_const _)).mul
      (Complex.continuous_conj.measurable.comp hm')
  set g : ℕ → EuclideanSpace ℝ (Fin d) → ℂ := fun N => (E N).indicator G with hgdef
  have hgmem : ∀ N, ∀ r : ℝ≥0∞, 1 ≤ r → MemLp (g N) r volume := by
    intro N r _
    haveI : IsFiniteMeasure (volume.restrict (E N)) := isFiniteMeasure_restrict.2 (hEfin N).ne
    refine (memLp_indicator_iff_restrict (hE N)).2 ?_
    refine MemLp.of_bound hGm.aestronglyMeasurable ((N : ℝ) ^ (p - 1)) ?_
    filter_upwards [ae_restrict_mem (hE N)] with x hx
    rw [hnorm]
    exact Real.rpow_le_rpow (norm_nonneg _) hx.2 (by linarith)
  set F : EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := fun x => ‖h' x‖ₑ ^ p with hFdef
  have hFm : Measurable F := hm'.enorm.pow_const p
  set I : ℕ → ℝ≥0∞ := fun N => ∫⁻ x in E N, F x with hIdef
  have hItop : ∀ N, I N < ⊤ := by
    intro N
    calc I N ≤ ∫⁻ x in E N, (N : ℝ≥0∞) ^ p := by
          refine setLIntegral_mono measurable_const fun x hx => ?_
          refine ENNReal.rpow_le_rpow ?_ hp0.le
          rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_natCast]
          exact ENNReal.ofReal_le_ofReal hx.2
      _ = (N : ℝ≥0∞) ^ p * volume (E N) := setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top
          (ENNReal.rpow_lt_top_of_nonneg hp0.le (ENNReal.natCast_ne_top N)) (hEfin N)
  -- the pairing
  have hpair : ∀ N, ‖∫ x, h x * g N x‖ₑ = I N := by
    intro N
    have hpt : ∀ x, h' x * g N x = (((E N).indicator (fun x => ‖h' x‖ ^ p) x : ℝ) : ℂ) := by
      intro x
      by_cases hx : x ∈ E N
      · simp only [hgdef, indicator_of_mem hx, hGdef]; exact hprod _
      · simp [hgdef, indicator_of_notMem hx]
    have hint : Integrable ((E N).indicator (fun x => ‖h' x‖ ^ p)) volume := by
      haveI : IsFiniteMeasure (volume.restrict (E N)) :=
        isFiniteMeasure_restrict.2 (hEfin N).ne
      refine (integrable_indicator_iff (hE N)).2 ?_
      refine (memLp_one_iff_integrable).1 (MemLp.of_bound
        (hm'.norm.pow_const p).aestronglyMeasurable ((N : ℝ) ^ p) ?_)
      filter_upwards [ae_restrict_mem (hE N)] with x hx
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      exact Real.rpow_le_rpow (norm_nonneg _) hx.2 hp0.le
    have hnn : 0 ≤ᵐ[volume] (E N).indicator (fun x => ‖h' x‖ ^ p) :=
      ae_of_all _ fun x => indicator_nonneg (fun x _ => Real.rpow_nonneg (norm_nonneg _) _) x
    calc ‖∫ x, h x * g N x‖ₑ = ‖∫ x, h' x * g N x‖ₑ := by
          congr 1; exact integral_congr_ae (hae.mono fun x hx => by simp only [hx])
      _ = ‖((∫ x, (E N).indicator (fun x => ‖h' x‖ ^ p) x : ℝ) : ℂ)‖ₑ := by
          simp only [hpt]; rw [integral_complex_ofReal]
      _ = ENNReal.ofReal (∫ x, (E N).indicator (fun x => ‖h' x‖ ^ p) x) := by
          rw [← ofReal_norm_eq_enorm, Complex.norm_real,
            Real.norm_of_nonneg (integral_nonneg_of_ae hnn)]
      _ = ∫⁻ x, ENNReal.ofReal ((E N).indicator (fun x => ‖h' x‖ ^ p) x) :=
          ofReal_integral_eq_lintegral_ofReal hint hnn
      _ = ∫⁻ x, (E N).indicator F x := by
          refine lintegral_congr fun x => ?_
          by_cases hx : x ∈ E N
          · rw [indicator_of_mem hx, indicator_of_mem hx]; simp only [hFdef]
            rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le]
          · rw [indicator_of_notMem hx, indicator_of_notMem hx, ENNReal.ofReal_zero]
      _ = I N := by rw [lintegral_indicator (hE N)]
  -- the `L^q` norm of the test function
  have hgq : ∀ N, eLpNorm (g N) (ENNReal.ofReal q) volume = I N ^ (1 / q) := by
    intro N
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hq0)
      ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hq0.le]
    congr 1
    simp only [hIdef]; rw [← lintegral_indicator (hE N)]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ E N
    · rw [indicator_of_mem hx]; simp only [hFdef, hgdef, hGdef]
      rw [indicator_of_mem hx, ← ofReal_norm_eq_enorm, hnorm,
        ← ofReal_norm_eq_enorm, ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
          hq0.le, ← Real.rpow_mul (norm_nonneg _), hpq,
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le]
    · rw [indicator_of_notMem hx]; simp only [hgdef]
      rw [indicator_of_notMem hx, enorm_zero, ENNReal.zero_rpow_of_pos hq0]
  -- each truncation is bounded by `M^p`
  have hIle : ∀ N, I N ≤ M ^ p := by
    intro N
    have key : I N ≤ M * I N ^ (1 / q) := by
      have := H _ (hgmem N); rwa [hpair, hgq] at this
    by_cases h0 : I N = 0
    · rw [h0]; exact zero_le
    have htop := (hItop N).ne
    have hsplit : I N = I N ^ (1 / p) * I N ^ (1 / q) := by
      rw [← ENNReal.rpow_add _ _ h0 htop, hpq', ENNReal.rpow_one]
    have hqne : I N ^ (1 / q) ≠ 0 := by
      simp [ENNReal.rpow_eq_zero_iff, h0, htop, hq0]
    have hqtop : I N ^ (1 / q) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (by positivity) htop
    have h1 : I N ^ (1 / p) ≤ M := by
      have key' : I N ^ (1 / p) * I N ^ (1 / q) ≤ M * I N ^ (1 / q) := by
        rw [← hsplit]; exact key
      calc I N ^ (1 / p) = I N ^ (1 / p) * I N ^ (1 / q) / I N ^ (1 / q) :=
            (ENNReal.mul_div_cancel_right hqne hqtop).symm
        _ ≤ M * I N ^ (1 / q) / I N ^ (1 / q) := ENNReal.div_le_div_right key' _
        _ = M := ENNReal.mul_div_cancel_right hqne hqtop
    calc I N = (I N ^ (1 / p)) ^ p := by
          rw [← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne', ENNReal.rpow_one]
      _ ≤ M ^ p := ENNReal.rpow_le_rpow h1 hp0.le
  -- monotone convergence
  have hmono : Monotone fun N => (E N).indicator F := by
    intro N K hNK x
    refine indicator_le_indicator_of_subset (fun y hy => ?_) (fun _ => zero_le) x
    have : (N : ℝ) ≤ K := by exact_mod_cast hNK
    exact ⟨hy.1.trans this, hy.2.trans this⟩
  have hsup : ∀ x, ⨆ N, (E N).indicator F x = F x := by
    intro x
    refine le_antisymm (iSup_le fun N => indicator_le_self _ _ x) ?_
    obtain ⟨N, hN⟩ := exists_nat_ge (max ‖x‖ ‖h' x‖)
    refine le_iSup_of_le N ?_
    rw [indicator_of_mem (show x ∈ E N from ⟨(le_max_left _ _).trans hN, (le_max_right _ _).trans hN⟩)]
  have hlint : ∫⁻ x, ‖h x‖ₑ ^ p ≤ M ^ p := by
    calc ∫⁻ x, ‖h x‖ₑ ^ p = ∫⁻ x, F x :=
          lintegral_congr_ae (hae.mono fun x hx => by simp only [hFdef, hx])
      _ = ∫⁻ x, ⨆ N, (E N).indicator F x := by simp only [hsup]
      _ = ⨆ N, ∫⁻ x, (E N).indicator F x :=
          lintegral_iSup (fun N => hFm.indicator (hE N)) hmono
      _ = ⨆ N, I N := iSup_congr fun N => by rw [lintegral_indicator (hE N)]
      _ ≤ M ^ p := iSup_le hIle
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp0) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp0.le]
  calc (∫⁻ x, ‖h x‖ₑ ^ p) ^ (1 / p) ≤ (M ^ p) ^ (1 / p) :=
        ENNReal.rpow_le_rpow hlint (by positivity)
    _ = M := by rw [← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one]

end DbarRegularity

open DbarRegularity

open MeasureTheory Set Metric
open scoped ENNReal

theorem solution {d : ℕ} {h : EuclideanSpace ℝ (Fin d) → ℂ}
    (hh : AEStronglyMeasurable h volume) {p q : ℝ} (hp : 1 < p) (hq : q = p / (p - 1))
    (M : ℝ≥0∞)
    (H : ∀ g : EuclideanSpace ℝ (Fin d) → ℂ, (∀ r : ℝ≥0∞, 1 ≤ r → MemLp g r volume) →
      ‖∫ x, h x * g x‖ₑ ≤ M * eLpNorm g (ENNReal.ofReal q) volume) :
    eLpNorm h (ENNReal.ofReal p) volume ≤ M :=
  eLpNorm_le_of_forall_enorm_integral_mul_le hh hp hq M H
