-- Prove2me | solution 1 for DbarRegularity.truncatedSingularIntegral_lp
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T18:21:15.124402+00:00
-- url     : https://prove2.me/submissions/d3fad28c-c980-4cfb-be2d-a090a2fe09e6

import Definitions.Def_DbarRegularity_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Theorems.Thm_DbarRegularity_truncatedSingularIntegral_uniform_bound
import Theorems.Thm_DbarRegularity_exists_contDiff_hasCompactSupport_eLpNorm_sub_le
import Theorems.Thm_DbarRegularity_eLpNorm_truncatedSingularIntegral_sub_le
import Theorems.Thm_DbarRegularity_exists_memLp_tendsto_eLpNorm_sub
import Theorems.Thm_DbarRegularity_setIntegral_mul_eq_integral_indicator
import Theorems.Thm_DbarRegularity_memLp_indicator_le_norm
import Theorems.Thm_DbarRegularity_aestronglyMeasurable_integral_mul_sub
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Data.Real.ConjExponents



namespace DbarRegularity

open MeasureTheory Metric Filter Topology Set
open scoped ENNReal NNReal ContDiff

theorem truncatedSingularIntegral_lp_aux {d : ℕ} (K : EuclideanSpace ℝ (Fin d) → ℂ) (B : ℝ)
    (hKm : AEStronglyMeasurable K volume)
    (hK1 : ∀ x, x ≠ 0 → ‖K x‖ ≤ B / ‖x‖ ^ d)
    (hK2 : ∀ y, y ≠ 0 → ∫⁻ x in {x | 2 * ‖y‖ ≤ ‖x‖}, ‖K (x - y) - K x‖ₑ ≤ ENNReal.ofReal B)
    (hK3 : ∀ R₁ R₂ : ℝ, 0 < R₁ → R₁ < R₂ → ∫ x in {x | R₁ < ‖x‖ ∧ ‖x‖ < R₂}, K x = 0)
    (p : ℝ) (hp : 1 < p) :
    ∃ A : ℝ≥0,
      (∀ ε : ℝ, 0 < ε → ∀ f : EuclideanSpace ℝ (Fin d) → ℂ, MemLp f (ENNReal.ofReal p) volume →
        eLpNorm (fun x => ∫ y in {y | ε ≤ ‖y‖}, f (x - y) * K y) (ENNReal.ofReal p) volume
          ≤ A * eLpNorm f (ENNReal.ofReal p) volume) ∧
      ∀ f : EuclideanSpace ℝ (Fin d) → ℂ, MemLp f (ENNReal.ofReal p) volume →
        ∃ g : EuclideanSpace ℝ (Fin d) → ℂ, MemLp g (ENNReal.ofReal p) volume ∧
          Tendsto (fun ε : ℝ => eLpNorm
              ((fun x => ∫ y in {y | ε ≤ ‖y‖}, f (x - y) * K y) - g) (ENNReal.ofReal p) volume)
            (𝓝[>] 0) (𝓝 0) ∧
          eLpNorm g (ENNReal.ofReal p) volume ≤ A * eLpNorm f (ENNReal.ofReal p) volume := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · -- `d = 0`: every truncated integral vanishes
    have hT : ∀ (f : EuclideanSpace ℝ (Fin 0) → ℂ) (ε : ℝ), 0 < ε →
        (fun x => ∫ y in {y : EuclideanSpace ℝ (Fin 0) | ε ≤ ‖y‖}, f (x - y) * K y) = 0 := by
      intro f ε hε
      have : {y : EuclideanSpace ℝ (Fin 0) | ε ≤ ‖y‖} = ∅ := by
        ext y
        rw [Subsingleton.elim y 0]
        simp only [norm_zero, mem_setOf_eq, mem_empty_iff_false, iff_false, not_le]
        exact hε
      funext x
      rw [this, Measure.restrict_empty, integral_zero_measure]
      rfl
    refine ⟨0, fun ε hε f _ => ?_, fun f _ => ⟨0, MemLp.zero, ?_, ?_⟩⟩
    · rw [hT f ε hε, eLpNorm_zero]; exact bot_le
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      rw [hT f ε hε, sub_zero, eLpNorm_zero]
    · rw [eLpNorm_zero]; exact bot_le
  -- `d > 0`
  set P : ℝ≥0∞ := ENNReal.ofReal p with hP
  have hP1 : 1 ≤ P := by rw [hP, ENNReal.one_le_ofReal]; exact hp.le
  haveI : Fact (1 ≤ P) := ⟨hP1⟩
  obtain ⟨A, hA⟩ := truncatedSingularIntegral_uniform_bound hd K B hKm hK1 hK2 hK3 p hp
  refine ⟨A, hA, fun f hf => ?_⟩
  set T : (EuclideanSpace ℝ (Fin d) → ℂ) → ℝ → EuclideanSpace ℝ (Fin d) → ℂ :=
    fun u ε x => ∫ y in {y | ε ≤ ‖y‖}, u (x - y) * K y with hTdef
  have hpq : p.HolderConjugate p.conjExponent := Real.HolderConjugate.conjExponent hp
  haveI : ENNReal.HolderTriple P (ENNReal.ofReal p.conjExponent) 1 := by
    simpa [hP] using hpq.ennrealOfReal
  have hmeas_le : ∀ r : ℝ, MeasurableSet {y : EuclideanSpace ℝ (Fin d) | r ≤ ‖y‖} := fun r =>
    measurableSet_le measurable_const measurable_norm
  -- integrability
  have hInt : ∀ u : EuclideanSpace ℝ (Fin d) → ℂ, MemLp u P volume → ∀ x (ε : ℝ), 0 < ε →
      IntegrableOn (fun y => u (x - y) * K y) {y | ε ≤ ‖y‖} volume := by
    intro u hu x ε hε
    have hKr : MemLp ({y | ε ≤ ‖y‖}.indicator K) (ENNReal.ofReal p.conjExponent) volume :=
      memLp_indicator_le_norm hd K hKm B hK1 ε hε _ hpq.symm.lt
    have hux : MemLp (fun y => u (x - y)) P volume :=
      hu.comp_measurePreserving (Measure.measurePreserving_sub_left volume x)
    have := hux.integrable_mul hKr
    rw [← integrable_indicator_iff (hmeas_le ε)]
    refine this.congr (Eventually.of_forall fun y => ?_)
    simp only [Pi.mul_apply, indicator]
    split_ifs <;> simp
  -- measurability
  have hmeasT : ∀ u : EuclideanSpace ℝ (Fin d) → ℂ, AEStronglyMeasurable u volume → ∀ ε : ℝ,
      AEStronglyMeasurable (T u ε) volume := by
    intro u hu ε
    have : T u ε = fun x => ∫ y, {y | ε ≤ ‖y‖}.indicator K (x - y) * u y := by
      funext x; exact setIntegral_mul_eq_integral_indicator K u ε x
    rw [this]
    exact aestronglyMeasurable_integral_mul_sub _ u (hKm.indicator (hmeas_le ε)) hu
  -- linearity
  have hlin : ∀ u w : EuclideanSpace ℝ (Fin d) → ℂ, MemLp u P volume → MemLp w P volume →
      ∀ ε : ℝ, 0 < ε → T (u - w) ε = T u ε - T w ε := by
    intro u w hu hw ε hε
    funext x
    simp only [hTdef, Pi.sub_apply, sub_mul]
    exact integral_sub (hInt u hu x ε hε) (hInt w hw x ε hε)
  have hTmem : ∀ ε : ℝ, 0 < ε → MemLp (T f ε) P volume := fun ε hε =>
    ⟨hmeasT f hf.1 ε, (hA ε hε f hf).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hf.2)⟩
  -- Cauchy property
  have hc : ∀ δ : ℝ, 0 < δ → ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ ε η : ℝ, 0 < ε → ε < η₀ → 0 < η → η < η₀ →
      eLpNorm (T f ε - T f η) P volume ≤ ENNReal.ofReal δ := by
    intro δ hδ
    set δ₁ : ℝ := δ / (2 * A + 2) with hδ₁
    have hδ₁0 : 0 < δ₁ := by positivity
    obtain ⟨h, hsm, hcs, hfh⟩ :=
      exists_contDiff_hasCompactSupport_eLpNorm_sub_le hP1 ENNReal.ofReal_ne_top f hf δ₁ hδ₁0
    have hh1 : ContDiff ℝ 1 h := hsm.of_le (by exact_mod_cast le_top)
    have hhP : MemLp h P volume := hh1.continuous.memLp_of_hasCompactSupport hcs
    obtain ⟨C, hC⟩ := eLpNorm_truncatedSingularIntegral_sub_le hd K B hKm hK1 hK3 p hp h hh1 hcs
    set η₀ : ℝ := min 1 (δ₁ / (|C| + 1)) with hη₀
    have hη₀0 : 0 < η₀ := lt_min one_pos (by positivity)
    refine ⟨η₀, hη₀0, fun ε η hε hεη hη hηη => ?_⟩
    have hsmall : ∀ t : ℝ, 0 < t → t < η₀ → ENNReal.ofReal (C * t) ≤ ENNReal.ofReal δ₁ := by
      intro t ht htη
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : t < δ₁ / (|C| + 1) := htη.trans_le (min_le_right _ _)
      rw [lt_div_iff₀ (by positivity)] at h1
      nlinarith [le_abs_self C, abs_nonneg C]
    have hhh : eLpNorm (T h ε - T h η) P volume ≤ ENNReal.ofReal δ₁ := by
      rcases le_total ε η with hle | hle
      · exact (hC ε η hε hle (hηη.le.trans (min_le_left _ _))).trans (hsmall η hη hηη)
      · rw [eLpNorm_sub_comm]
        exact (hC η ε hη hle (hεη.le.trans (min_le_left _ _))).trans (hsmall ε hε hεη)
    have hfhP : MemLp (f - h) P volume := hf.sub hhP
    have hdec : T f ε - T f η = T (f - h) ε + (T h ε - T h η) - T (f - h) η := by
      rw [hlin f h hf hhP ε hε, hlin f h hf hhP η hη]; abel
    have hm1 := hmeasT (f - h) hfhP.1 ε
    have hm2 := (hmeasT h hhP.1 ε).sub (hmeasT h hhP.1 η)
    have hm3 := hmeasT (f - h) hfhP.1 η
    have hA1 : eLpNorm (T (f - h) ε) P volume ≤ A * ENNReal.ofReal δ₁ :=
      (hA ε hε _ hfhP).trans (mul_le_mul' le_rfl hfh)
    have hA3 : eLpNorm (T (f - h) η) P volume ≤ A * ENNReal.ofReal δ₁ :=
      (hA η hη _ hfhP).trans (mul_le_mul' le_rfl hfh)
    calc eLpNorm (T f ε - T f η) P volume
        = eLpNorm (T (f - h) ε + (T h ε - T h η) - T (f - h) η) P volume := by rw [hdec]
      _ ≤ eLpNorm (T (f - h) ε + (T h ε - T h η)) P volume + eLpNorm (T (f - h) η) P volume :=
          eLpNorm_sub_le (hm1.add hm2) hm3 hP1
      _ ≤ (eLpNorm (T (f - h) ε) P volume + eLpNorm (T h ε - T h η) P volume) +
            eLpNorm (T (f - h) η) P volume :=
          add_le_add (eLpNorm_add_le hm1 hm2 hP1) le_rfl
      _ ≤ (A * ENNReal.ofReal δ₁ + ENNReal.ofReal δ₁) + A * ENNReal.ofReal δ₁ :=
          add_le_add (add_le_add hA1 hhh) hA3
      _ = ENNReal.ofReal ((2 * A + 1) * δ₁) := by
          rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) hδ₁0.le,
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; ring
      _ ≤ ENNReal.ofReal δ := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [hδ₁, mul_div_assoc']
          rw [div_le_iff₀ (by positivity)]
          nlinarith
  obtain ⟨g, hg, hlim⟩ := exists_memLp_tendsto_eLpNorm_sub (T f) hTmem hc
  refine ⟨g, hg, hlim, ?_⟩
  have h2 : Tendsto (fun ε : ℝ => A * eLpNorm f P volume + eLpNorm (T f ε - g) P volume)
      (𝓝[>] 0) (𝓝 (A * eLpNorm f P volume)) := by
    simpa using (tendsto_const_nhds (x := A * eLpNorm f P volume)).add hlim
  refine ge_of_tendsto h2 ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  calc eLpNorm g P volume = eLpNorm (T f ε - (T f ε - g)) P volume := by rw [sub_sub_cancel]
    _ ≤ eLpNorm (T f ε) P volume + eLpNorm (T f ε - g) P volume :=
        eLpNorm_sub_le (hTmem ε hε).1 ((hTmem ε hε).1.sub hg.1) hP1
    _ ≤ _ := add_le_add (hA ε hε f hf) le_rfl

end DbarRegularity

open DbarRegularity

open MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ContDiff

theorem solution {d : ℕ} (K : EuclideanSpace ℝ (Fin d) → ℂ) (B : ℝ)
    (hKm : AEStronglyMeasurable K volume)
    (hK1 : ∀ x, x ≠ 0 → ‖K x‖ ≤ B / ‖x‖ ^ d)
    (hK2 : ∀ y, y ≠ 0 → ∫⁻ x in {x | 2 * ‖y‖ ≤ ‖x‖}, ‖K (x - y) - K x‖ₑ ≤ ENNReal.ofReal B)
    (hK3 : ∀ R₁ R₂ : ℝ, 0 < R₁ → R₁ < R₂ → ∫ x in {x | R₁ < ‖x‖ ∧ ‖x‖ < R₂}, K x = 0)
    (p : ℝ) (hp : 1 < p) :
    ∃ A : ℝ≥0,
      (∀ ε : ℝ, 0 < ε → ∀ f : EuclideanSpace ℝ (Fin d) → ℂ, MemLp f (ENNReal.ofReal p) volume →
        eLpNorm (fun x => ∫ y in {y | ε ≤ ‖y‖}, f (x - y) * K y) (ENNReal.ofReal p) volume
          ≤ A * eLpNorm f (ENNReal.ofReal p) volume) ∧
      ∀ f : EuclideanSpace ℝ (Fin d) → ℂ, MemLp f (ENNReal.ofReal p) volume →
        ∃ g : EuclideanSpace ℝ (Fin d) → ℂ, MemLp g (ENNReal.ofReal p) volume ∧
          Tendsto (fun ε : ℝ => eLpNorm
              ((fun x => ∫ y in {y | ε ≤ ‖y‖}, f (x - y) * K y) - g) (ENNReal.ofReal p) volume)
            (𝓝[>] 0) (𝓝 0) ∧
          eLpNorm g (ENNReal.ofReal p) volume ≤ A * eLpNorm f (ENNReal.ofReal p) volume :=
  DbarRegularity.truncatedSingularIntegral_lp_aux K B hKm hK1 hK2 hK3 p hp
