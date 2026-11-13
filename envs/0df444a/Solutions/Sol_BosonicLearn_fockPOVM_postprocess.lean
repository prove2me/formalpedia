-- Prove2me | solution 1 for BosonicLearn.fockPOVM_postprocess
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T05:16:48.342499+00:00
-- url     : https://prove2.me/submissions/81b6c544-8082-4af5-99b1-c4ad3de9a29d

import Mathlib
import Definitions.Def_BosonicLearn_FockPOVM
import Theorems.Thm_BosonicLearn_effect_matrix_operator
import Theorems.Thm_BosonicLearn_effect_trace_pairing
import Theorems.Thm_BosonicLearn_fockPOVM_form_measure

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity IsTraceClass NuclearExpansion)
open QAlgorithms.RealRegisters (Hilbert)
open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix
open Filter Topology

open BosonicLearn

noncomputable section

/-! ### Finite truncations of vectors of `ℓ²` -/

private def finVec {I : Type} [DecidableEq I] (s : Finset I) (g : I → ℂ) : Hilbert I :=
  ∑ i ∈ s, lp.single 2 i (g i)

private lemma norm_finVec_le {I : Type} [DecidableEq I] (s : Finset I) (f : Hilbert I) :
    ‖finVec s f‖ ≤ ‖f‖ := by
  have h1 := lp.norm_sum_single (p := (2 : ℝ≥0∞)) (E := fun _ : I => ℂ) (by norm_num) f s
  have h2 := lp.sum_rpow_le_norm_rpow (p := (2 : ℝ≥0∞)) (by norm_num) f s
  have h3 : ‖finVec s f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    have e : ‖finVec s f‖ ^ 2 = ∑ i ∈ s, ‖f i‖ ^ 2 := by simpa [finVec] using h1
    rw [e]
    simpa using h2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h3

private lemma tendsto_finVec {I : Type} [DecidableEq I] (f : Hilbert I) :
    Tendsto (fun s : Finset I => finVec s f) atTop (𝓝 f) := by
  simpa [HasSum, finVec] using lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) f

/-- A sequence of finite sets along which the truncations of two given vectors converge. -/
private lemma exists_seq_trunc {I : Type} [DecidableEq I] (R L : Hilbert I) :
    ∃ s : ℕ → Finset I, Tendsto (fun n => finVec (s n) R) atTop (𝓝 R) ∧
      Tendsto (fun n => finVec (s n) L) atTop (𝓝 L) := by
  have ev : ∀ n : ℕ, ∃ s : Finset I, dist (finVec s R) R < 1 / ((n : ℝ) + 1) ∧
      dist (finVec s L) L < 1 / ((n : ℝ) + 1) := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact ((Metric.tendsto_nhds.mp (tendsto_finVec R) _ hpos).and
      (Metric.tendsto_nhds.mp (tendsto_finVec L) _ hpos)).exists
  choose s hs using ev
  exact ⟨s,
    tendsto_iff_dist_tendsto_zero.mpr (squeeze_zero (fun _ => dist_nonneg) (fun n => (hs n).1.le)
      tendsto_one_div_add_atTop_nhds_zero_nat),
    tendsto_iff_dist_tendsto_zero.mpr (squeeze_zero (fun _ => dist_nonneg) (fun n => (hs n).2.le)
      tendsto_one_div_add_atTop_nhds_zero_nat)⟩

/-- Matrix elements of a bounded operator between finitely supported vectors. -/
private lemma inner_finVec_op {I : Type} [DecidableEq I] (F : Hilbert I →L[ℂ] Hilbert I) (s : Finset I)
    (x y : I → ℂ) :
    inner ℂ (finVec s x) (F (finVec s y)) = ∑ i ∈ s, ∑ j ∈ s,
      star (x i) * inner ℂ (lp.single 2 i (1 : ℂ) : Hilbert I) (F (lp.single 2 j (1 : ℂ))) * y j := by
  have hs : ∀ g : I → ℂ, finVec s g = ∑ i ∈ s, g i • (lp.single 2 i (1 : ℂ) : Hilbert I) := by
    intro g
    unfold finVec
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← lp.single_smul]
    simp
  rw [hs x, hs y, map_sum, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, inner_smul_left, inner_smul_right]
  simp only [Complex.star_def]
  ring

/-! ### The operator of an effect matrix -/

/-- The hypothesis of `effect_matrix_operator`. -/
private abbrev EffB {I : Type} (E : Matrix I I ℂ) : Prop :=
  ∀ (s : Finset I) (z : I → ℂ),
    (∑ i ∈ s, ∑ j ∈ s, star (z i) * E i j * z j).im = 0 ∧
    0 ≤ (∑ i ∈ s, ∑ j ∈ s, star (z i) * E i j * z j).re ∧
    (∑ i ∈ s, ∑ j ∈ s, star (z i) * E i j * z j).re ≤ ∑ i ∈ s, ‖z i‖ ^ 2

private def opOf {I : Type} [DecidableEq I] {E : Matrix I I ℂ} (hE : EffB E) : Hilbert I →L[ℂ] Hilbert I :=
  Classical.choose (effect_matrix_operator E hE)

private lemma opOf_norm {I : Type} [DecidableEq I] {E : Matrix I I ℂ} (hE : EffB E) : ‖opOf hE‖ ≤ 1 :=
  (Classical.choose_spec (effect_matrix_operator E hE)).1

private lemma opOf_hasSum {I : Type} [DecidableEq I] {E : Matrix I I ℂ} (hE : EffB E) (z : Hilbert I)
    (i : I) : HasSum (fun j => E i j * z j) (opOf hE z i) :=
  (Classical.choose_spec (effect_matrix_operator E hE)).2.2.1 z i

private lemma opOf_entry {I : Type} [DecidableEq I] {E : Matrix I I ℂ} (hE : EffB E) (i j : I) :
    inner ℂ (lp.single 2 i (1 : ℂ) : Hilbert I) (opOf hE (lp.single 2 j (1 : ℂ))) = E i j :=
  (Classical.choose_spec (effect_matrix_operator E hE)).2.2.2 i j

private lemma norm_inner_opOf_le {I : Type} [DecidableEq I] {E : Matrix I I ℂ} (hE : EffB E)
    (R L : Hilbert I) : ‖inner ℂ R (opOf hE L)‖ ≤ ‖R‖ * ‖L‖ := by
  refine (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  calc ‖opOf hE L‖ ≤ ‖opOf hE‖ * ‖L‖ := (opOf hE).le_opNorm L
    _ ≤ 1 * ‖L‖ := mul_le_mul_of_nonneg_right (opOf_norm hE) (norm_nonneg _)
    _ = ‖L‖ := one_mul _

/-- The Born sum `∑ᵢ ∑ⱼ Eᵢⱼ ρⱼᵢ`. -/
private def bornSum {I : Type} (E ρ : Matrix I I ℂ) : ℂ := ∑' i, ∑' j, E i j * ρ j i

private lemma bornSum_eq {I : Type} [DecidableEq I] {E : Matrix I I ℂ} (hE : EffB E) {ρ : Matrix I I ℂ}
    (e : NuclearExpansion ρ) :
    bornSum E ρ = ∑' a, inner ℂ (e.right a) (opOf hE (e.left a)) :=
  (effect_trace_pairing E (opOf hE) (opOf_hasSum hE) ρ e).2.2.2

private lemma bornSum_summable {I : Type} [DecidableEq I] {E : Matrix I I ℂ} (hE : EffB E)
    {ρ : Matrix I I ℂ} (e : NuclearExpansion ρ) :
    (∀ i, Summable fun j => E i j * ρ j i) ∧ Summable (fun i => ∑' j, E i j * ρ j i) :=
  ⟨(effect_trace_pairing E (opOf hE) (opOf_hasSum hE) ρ e).1,
    (effect_trace_pairing E (opOf hE) (opOf_hasSum hE) ρ e).2.1⟩

/-! ### Additivity of the effects and positivity of Born sums -/

private lemma effect_add_compl {I Ω : Type} [DecidableEq I] [MeasurableSpace Ω] (P : FockPOVM I Ω)
    {B : Set Ω} (hB : MeasurableSet B) (i j : I) :
    P.effect B i j + P.effect Bᶜ i j = (1 : Matrix I I ℂ) i j := by
  obtain ⟨m, hm, hmE⟩ := (fockPOVM_form_measure P).2 i j
  have hadd : ∀ k, (m k B).toReal + (m k Bᶜ).toReal = (m k Set.univ).toReal := by
    intro k
    have := hm k
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), measure_add_measure_compl hB]
  rw [hmE B hB, hmE Bᶜ hB.compl, ← P.effect_univ, hmE Set.univ MeasurableSet.univ,
    ← hadd 0, ← hadd 1, ← hadd 2, ← hadd 3]
  push_cast
  ring

/-- For a density operator the Born sum of every effect has non-negative real part: the sums for `B` and
its complement add up to the trace `1`, and the two outcome probabilities add up to `1`. -/
private lemma bornSum_re_nonneg {I Ω : Type} [DecidableEq I] [MeasurableSpace Ω] (P : FockPOVM I Ω)
    {ρ : Matrix I I ℂ} (hρ : IsDensity ρ) {B : Set Ω} (hB : MeasurableSet B) :
    0 ≤ (bornSum (P.effect B) ρ).re := by
  obtain ⟨e⟩ := hρ.1
  have hEB : EffB (P.effect B) := P.effect_form B hB
  have hEC : EffB (P.effect Bᶜ) := P.effect_form Bᶜ hB.compl
  obtain ⟨h1B, h2B⟩ := bornSum_summable hEB e
  obtain ⟨h1C, h2C⟩ := bornSum_summable hEC e
  have hpt : ∀ i, ∑' j, P.effect B i j * ρ j i + ∑' j, P.effect Bᶜ i j * ρ j i = ρ i i := by
    intro i
    rw [← (h1B i).tsum_add (h1C i)]
    have h : ∀ j, P.effect B i j * ρ j i + P.effect Bᶜ i j * ρ j i = if j = i then ρ i i else 0 := by
      intro j
      rw [← add_mul, effect_add_compl P hB, Matrix.one_apply]
      by_cases hij : i = j
      · subst hij
        simp
      · have hji : ¬ j = i := fun h => hij h.symm
        simp [hij, hji]
    rw [tsum_congr h, tsum_ite_eq]
  have hsum : bornSum (P.effect B) ρ + bornSum (P.effect Bᶜ) ρ = ∑' i, ρ i i := by
    unfold bornSum
    rw [← h2B.tsum_add h2C]
    exact tsum_congr hpt
  have hdiag : Summable fun i => ρ i i := (h2B.add h2C).congr hpt
  have hre : (bornSum (P.effect B) ρ).re + (bornSum (P.effect Bᶜ) ρ).re = 1 := by
    rw [← Complex.add_re, hsum, Complex.re_tsum hdiag]
    exact hρ.2.2.2
  have hprob := P.law_prob ρ hρ
  have hlaw := prob_add_prob_compl (μ := P.law ρ) hB
  rw [P.law_born ρ hρ B hB, P.law_born ρ hρ Bᶜ hB.compl] at hlaw
  change ENNReal.ofReal (bornSum (P.effect B) ρ).re + ENNReal.ofReal (bornSum (P.effect Bᶜ) ρ).re = 1
    at hlaw
  by_contra hneg
  rw [not_le] at hneg
  rw [ENNReal.ofReal_of_nonpos hneg.le, zero_add, ENNReal.ofReal_eq_one] at hlaw
  linarith

/-! ### The post-processed effects, by the layer-cake formula -/

/-- Level sets of the probability that the post-processed outcome lies in `B'`. -/
private def lev {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] (κ : Kernel Ω Ω') (B' : Set Ω')
    (t : ℝ) : Set Ω := {x | t < (κ x B').toReal}

private lemma measurableSet_lev {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] (κ : Kernel Ω Ω')
    {B' : Set Ω'} (hB' : MeasurableSet B') (t : ℝ) : MeasurableSet (lev κ B' t) :=
  measurableSet_lt measurable_const (κ.measurable_coe hB').ennreal_toReal

private lemma lev_anti {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] (κ : Kernel Ω Ω')
    (B' : Set Ω') : Antitone (lev κ B') := fun _ _ h _ hx => lt_of_le_of_lt h hx

private lemma measurable_entry {I Ω Ω' : Type} [DecidableEq I] [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : FockPOVM I Ω) (κ : Kernel Ω Ω') {B' : Set Ω'} (hB' : MeasurableSet B') (i j : I) :
    Measurable fun t : ℝ => P.effect (lev κ B' t) i j := by
  obtain ⟨m, hm, hmE⟩ := (fockPOVM_form_measure P).2 i j
  have hmeas : ∀ k, Measurable fun t : ℝ => (m k (lev κ B' t)).toReal := by
    intro k
    have := hm k
    exact Antitone.measurable fun t t' h =>
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (lev_anti κ B' h))
  have e : (fun t : ℝ => P.effect (lev κ B' t) i j) = fun t => (1 / 4 : ℂ) *
      ((((m 0 (lev κ B' t)).toReal - (m 1 (lev κ B' t)).toReal : ℝ) : ℂ) -
        Complex.I * (((m 2 (lev κ B' t)).toReal - (m 3 (lev κ B' t)).toReal : ℝ) : ℂ)) := by
    funext t
    exact hmE _ (measurableSet_lev κ hB' t)
  rw [e]
  exact ((Complex.measurable_ofReal.comp ((hmeas 0).sub (hmeas 1))).sub
    ((Complex.measurable_ofReal.comp ((hmeas 2).sub (hmeas 3))).const_mul _)).const_mul _

private lemma norm_entry_le {I : Type} [DecidableEq I] {E : Matrix I I ℂ} (hE : EffB E) (i j : I) :
    ‖E i j‖ ≤ 1 := by
  have h := norm_inner_opOf_le hE (lp.single 2 i (1 : ℂ)) (lp.single 2 j (1 : ℂ))
  rw [opOf_entry hE i j, lp.norm_single (by norm_num), lp.norm_single (by norm_num)] at h
  simpa using h

private lemma integrable_entry {I Ω Ω' : Type} [DecidableEq I] [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : FockPOVM I Ω) (κ : Kernel Ω Ω') {B' : Set Ω'} (hB' : MeasurableSet B') (i j : I) :
    IntegrableOn (fun t : ℝ => P.effect (lev κ B' t) i j) (Set.Ioo 0 1) volume :=
  Integrable.of_bound (measurable_entry P κ hB' i j).aestronglyMeasurable 1
    (Eventually.of_forall fun t => norm_entry_le (P.effect_form _ (measurableSet_lev κ hB' t)) i j)

/-- The effect of the post-processed measurement: `E'(B') = ∫₀¹ E({x | t < κ(x, B')}) dt`. -/
private def postEffect {I Ω Ω' : Type} [DecidableEq I] [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : FockPOVM I Ω) (κ : Kernel Ω Ω') (B' : Set Ω') : Matrix I I ℂ :=
  fun i j => ∫ t in Set.Ioo (0 : ℝ) 1, P.effect (lev κ B' t) i j

private lemma integrable_form {I Ω Ω' : Type} [DecidableEq I] [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : FockPOVM I Ω) (κ : Kernel Ω Ω') {B' : Set Ω'} (hB' : MeasurableSet B') (s : Finset I)
    (x y : I → ℂ) :
    IntegrableOn (fun t : ℝ => ∑ i ∈ s, ∑ j ∈ s, star (x i) * P.effect (lev κ B' t) i j * y j)
      (Set.Ioo 0 1) volume :=
  integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    ((integrable_entry P κ hB' i j).const_mul _).mul_const _

private lemma postEffect_sesq {I Ω Ω' : Type} [DecidableEq I] [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : FockPOVM I Ω) (κ : Kernel Ω Ω') {B' : Set Ω'} (hB' : MeasurableSet B') (s : Finset I)
    (x y : I → ℂ) :
    ∑ i ∈ s, ∑ j ∈ s, star (x i) * postEffect P κ B' i j * y j =
      ∫ t in Set.Ioo (0 : ℝ) 1, ∑ i ∈ s, ∑ j ∈ s, star (x i) * P.effect (lev κ B' t) i j * y j := by
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    ((integrable_entry P κ hB' i j).const_mul _).mul_const _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => ((integrable_entry P κ hB' i j).const_mul _).mul_const _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_mul_const, integral_const_mul]
  rfl

private lemma postEffect_effB {I Ω Ω' : Type} [DecidableEq I] [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : FockPOVM I Ω) (κ : Kernel Ω Ω') {B' : Set Ω'} (hB' : MeasurableSet B') :
    EffB (postEffect P κ B') := by
  intro s z
  have hreal : ∑ i ∈ s, ∑ j ∈ s, star (z i) * postEffect P κ B' i j * z j =
      ((∫ t in Set.Ioo (0 : ℝ) 1,
        (∑ i ∈ s, ∑ j ∈ s, star (z i) * P.effect (lev κ B' t) i j * z j).re : ℝ) : ℂ) := by
    rw [postEffect_sesq P κ hB' s z z, ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioo fun t _ => ?_
    have hq := P.effect_form _ (measurableSet_lev κ hB' t) s z
    exact Complex.ext (Complex.ofReal_re _).symm (hq.1.trans (Complex.ofReal_im _).symm)
  rw [hreal]
  have hq0 : ∀ t, 0 ≤ (∑ i ∈ s, ∑ j ∈ s, star (z i) * P.effect (lev κ B' t) i j * z j).re :=
    fun t => (P.effect_form _ (measurableSet_lev κ hB' t) s z).2.1
  have hq1 : ∀ t, (∑ i ∈ s, ∑ j ∈ s, star (z i) * P.effect (lev κ B' t) i j * z j).re ≤
      ∑ i ∈ s, ‖z i‖ ^ 2 := fun t => (P.effect_form _ (measurableSet_lev κ hB' t) s z).2.2
  refine ⟨Complex.ofReal_im _, ?_, ?_⟩
  · rw [Complex.ofReal_re]
    exact integral_nonneg hq0
  · rw [Complex.ofReal_re]
    calc ∫ t in Set.Ioo (0 : ℝ) 1, (∑ i ∈ s, ∑ j ∈ s, star (z i) * P.effect (lev κ B' t) i j * z j).re
        ≤ ∫ _t in Set.Ioo (0 : ℝ) 1, (∑ i ∈ s, ‖z i‖ ^ 2) :=
          integral_mono (integrable_form P κ hB' s z z).re (integrable_const _) hq1
      _ = ∑ i ∈ s, ‖z i‖ ^ 2 := by simp

private lemma postEffect_univ {I Ω Ω' : Type} [DecidableEq I] [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : FockPOVM I Ω) (κ : Kernel Ω Ω') [IsMarkovKernel κ] : postEffect P κ Set.univ = 1 := by
  funext i j
  unfold postEffect
  have h : ∀ t ∈ Set.Ioo (0 : ℝ) 1, P.effect (lev κ Set.univ t) i j = (1 : Matrix I I ℂ) i j := by
    intro t ht
    have hl : lev κ Set.univ t = Set.univ := by
      ext x
      simp [lev, ht.2]
    rw [hl, P.effect_univ]
  rw [setIntegral_congr_fun measurableSet_Ioo h]
  simp

/-! ### The operators of the level-set effects, as a family in `t` -/

private def opT {I Ω Ω' : Type} [DecidableEq I] [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : FockPOVM I Ω) (κ : Kernel Ω Ω') {B' : Set Ω'} (hB' : MeasurableSet B') (t : ℝ) :
    Hilbert I →L[ℂ] Hilbert I :=
  opOf (E := P.effect (lev κ B' t)) (P.effect_form _ (measurableSet_lev κ hB' t))

private lemma inner_finVec_opT {I Ω Ω' : Type} [DecidableEq I] [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : FockPOVM I Ω) (κ : Kernel Ω Ω') {B' : Set Ω'} (hB' : MeasurableSet B') (t : ℝ) (s : Finset I)
    (x y : I → ℂ) :
    inner ℂ (finVec s x) (opT P κ hB' t (finVec s y)) =
      ∑ i ∈ s, ∑ j ∈ s, star (x i) * P.effect (lev κ B' t) i j * y j := by
  rw [inner_finVec_op]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  unfold opT
  rw [opOf_entry]

/-- `t ↦ ⟨R, F_t L⟩` is measurable: it is a pointwise limit of finite combinations of matrix entries. -/
private lemma measurable_inner_opT {I Ω Ω' : Type} [DecidableEq I] [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (P : FockPOVM I Ω) (κ : Kernel Ω Ω') {B' : Set Ω'} (hB' : MeasurableSet B')
    (R L : Hilbert I) : Measurable fun t : ℝ => inner ℂ R (opT P κ hB' t L) := by
  obtain ⟨s, hsR, hsL⟩ := exists_seq_trunc R L
  refine measurable_of_tendsto_metrizable
    (f := fun n t => inner ℂ (finVec (s n) R) (opT P κ hB' t (finVec (s n) L))) (fun n => ?_)
    (tendsto_pi_nhds.mpr fun t => hsR.inner (((opT P κ hB' t).continuous.tendsto L).comp hsL))
  have e : (fun t : ℝ => inner ℂ (finVec (s n) R) (opT P κ hB' t (finVec (s n) L))) =
      fun t => ∑ i ∈ s n, ∑ j ∈ s n, star (R i) * P.effect (lev κ B' t) i j * L j := by
    funext t
    exact inner_finVec_opT P κ hB' t (s n) R L
  rw [e]
  exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
    ((measurable_entry P κ hB' i j).const_mul _).mul_const _

/-- Weak integral formula: the operator of the post-processed effect is the integral over `t` of the
operators of the level-set effects. -/
private lemma inner_post_eq_integral {I Ω Ω' : Type} [DecidableEq I] [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (P : FockPOVM I Ω) (κ : Kernel Ω Ω') {B' : Set Ω'} (hB' : MeasurableSet B')
    (R L : Hilbert I) :
    inner ℂ R (opOf (postEffect_effB P κ hB') L) =
      ∫ t in Set.Ioo (0 : ℝ) 1, inner ℂ R (opT P κ hB' t L) := by
  obtain ⟨s, hsR, hsL⟩ := exists_seq_trunc R L
  have hfin : ∀ n, inner ℂ (finVec (s n) R) (opOf (postEffect_effB P κ hB') (finVec (s n) L)) =
      ∫ t in Set.Ioo (0 : ℝ) 1, inner ℂ (finVec (s n) R) (opT P κ hB' t (finVec (s n) L)) := by
    intro n
    rw [inner_finVec_op]
    have e1 : ∑ i ∈ s n, ∑ j ∈ s n, star (R i) * inner ℂ (lp.single 2 i (1 : ℂ) : Hilbert I)
        (opOf (postEffect_effB P κ hB') (lp.single 2 j (1 : ℂ))) * L j =
        ∑ i ∈ s n, ∑ j ∈ s n, star (R i) * postEffect P κ B' i j * L j :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [opOf_entry]
    rw [e1, postEffect_sesq P κ hB' (s n) R L]
    refine setIntegral_congr_fun measurableSet_Ioo fun t _ => ?_
    exact (inner_finVec_opT P κ hB' t (s n) R L).symm
  have hl : Tendsto (fun n => inner ℂ (finVec (s n) R) (opOf (postEffect_effB P κ hB') (finVec (s n) L)))
      atTop (𝓝 (inner ℂ R (opOf (postEffect_effB P κ hB') L))) :=
    hsR.inner (((opOf (postEffect_effB P κ hB')).continuous.tendsto L).comp hsL)
  have hr : Tendsto (fun n => ∫ t in Set.Ioo (0 : ℝ) 1,
      inner ℂ (finVec (s n) R) (opT P κ hB' t (finVec (s n) L))) atTop
      (𝓝 (∫ t in Set.Ioo (0 : ℝ) 1, inner ℂ R (opT P κ hB' t L))) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => ‖R‖ * ‖L‖)
      (fun n => (measurable_inner_opT P κ hB' _ _).aestronglyMeasurable) (integrable_const _)
      (fun n => Eventually.of_forall fun t => ?_)
      (Eventually.of_forall fun t => hsR.inner (((opT P κ hB' t).continuous.tendsto L).comp hsL))
    exact (norm_inner_opOf_le _ _ _).trans
      (mul_le_mul (norm_finVec_le _ R) (norm_finVec_le _ L) (norm_nonneg _) (norm_nonneg _))
  simp only [hfin] at hl
  exact tendsto_nhds_unique hl hr

/-! ### The Born rule of the post-processed measurement -/

private lemma bornSum_hasSum {I : Type} [DecidableEq I] {E : Matrix I I ℂ} (hE : EffB E)
    {ρ : Matrix I I ℂ} (e : NuclearExpansion ρ) :
    HasSum (fun a => inner ℂ (e.right a) (opOf hE (e.left a))) (bornSum E ρ) := by
  rw [bornSum_eq hE e]
  exact (effect_trace_pairing E (opOf hE) (opOf_hasSum hE) ρ e).2.2.1.hasSum

private lemma post_born {I Ω Ω' : Type} [DecidableEq I] [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : FockPOVM I Ω) (κ : Kernel Ω Ω') [IsMarkovKernel κ] {ρ : Matrix I I ℂ} (hρ : IsDensity ρ)
    {B' : Set Ω'} (hB' : MeasurableSet B') :
    (P.law ρ).bind κ B' = ENNReal.ofReal (bornSum (postEffect P κ B') ρ).re := by
  obtain ⟨e⟩ := hρ.1
  have hw : Summable fun a => ‖e.right a‖ * ‖e.left a‖ := by
    simpa [mul_comm] using e.summable
  set τ : ℝ → ℂ := fun t => bornSum (P.effect (lev κ B' t)) ρ with hτ
  have hlim : ∀ t, HasSum (fun a => inner ℂ (e.right a) (opT P κ hB' t (e.left a))) (τ t) :=
    fun t => bornSum_hasSum _ e
  -- the Born sum of the post-processed effect is the integral of `τ`
  have h1 : HasSum (fun a => ∫ t in Set.Ioo (0 : ℝ) 1, inner ℂ (e.right a) (opT P κ hB' t (e.left a)))
      (∫ t in Set.Ioo (0 : ℝ) 1, τ t) :=
    hasSum_integral_of_dominated_convergence (fun a _ => ‖e.right a‖ * ‖e.left a‖)
      (fun a => (measurable_inner_opT P κ hB' _ _).aestronglyMeasurable)
      (fun a => Eventually.of_forall fun t => norm_inner_opOf_le _ _ _)
      (Eventually.of_forall fun _ => hw) (integrable_const _)
      (Eventually.of_forall fun t => hlim t)
  have h2 : bornSum (postEffect P κ B') ρ = ∫ t in Set.Ioo (0 : ℝ) 1, τ t := by
    rw [bornSum_eq (postEffect_effB P κ hB') e, ← h1.tsum_eq]
    exact tsum_congr fun a => inner_post_eq_integral P κ hB' _ _
  -- `τ` is measurable and bounded
  have hτmeas : Measurable τ :=
    measurable_of_tendsto_metrizable
      (f := fun N t => ∑ a ∈ Finset.range N, inner ℂ (e.right a) (opT P κ hB' t (e.left a)))
      (fun N => Finset.measurable_sum _ fun a _ => measurable_inner_opT P κ hB' _ _)
      (tendsto_pi_nhds.mpr fun t => (hlim t).tendsto_sum_nat)
  have hτbound : ∀ t, ‖τ t‖ ≤ ∑' a, ‖e.right a‖ * ‖e.left a‖ := by
    intro t
    rw [← (hlim t).tsum_eq]
    exact tsum_of_norm_bounded hw.hasSum fun a => norm_inner_opOf_le _ _ _
  have hτint : IntegrableOn τ (Set.Ioo 0 1) volume :=
    Integrable.of_bound hτmeas.aestronglyMeasurable _ (Eventually.of_forall hτbound)
  -- the law side, by the layer-cake formula
  have hprob := P.law_prob ρ hρ
  have hg : Measurable fun x => (κ x B').toReal := (κ.measurable_coe hB').ennreal_toReal
  have hlaw : ∀ t, P.law ρ (lev κ B' t) = ENNReal.ofReal (τ t).re :=
    fun t => P.law_born ρ hρ _ (measurableSet_lev κ hB' t)
  have hzero : ∀ t ∈ Set.Ici (1 : ℝ), P.law ρ (lev κ B' t) = 0 := by
    intro t ht
    have hempty : lev κ B' t = ∅ := by
      ext x
      simp only [lev, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      exact (ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one).trans (by simpa using ht)
    rw [hempty, measure_empty]
  have hre : (∫ t in Set.Ioo (0 : ℝ) 1, τ t).re = ∫ t in Set.Ioo (0 : ℝ) 1, (τ t).re := by
    have h := integral_re hτint
    simpa using h.symm
  calc (P.law ρ).bind κ B' = ∫⁻ x, κ x B' ∂(P.law ρ) := Measure.bind_apply hB' κ.aemeasurable
    _ = ∫⁻ x, ENNReal.ofReal ((κ x B').toReal) ∂(P.law ρ) :=
        lintegral_congr fun x => (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ = ∫⁻ t in Set.Ioi (0 : ℝ), P.law ρ (lev κ B' t) :=
        lintegral_eq_lintegral_meas_lt (P.law ρ) (Eventually.of_forall fun x => ENNReal.toReal_nonneg)
          hg.aemeasurable
    _ = ∫⁻ t in Set.Ioo (0 : ℝ) 1, P.law ρ (lev κ B' t) := by
        rw [← Set.Ioo_union_Ici_eq_Ioi (zero_lt_one' ℝ),
          lintegral_union measurableSet_Ici
            (Set.disjoint_left.mpr fun t h1 h2 => not_le.mpr h1.2 h2),
          setLIntegral_congr_fun measurableSet_Ici hzero]
        simp
    _ = ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (τ t).re := by simp only [hlaw]
    _ = ENNReal.ofReal (∫ t in Set.Ioo (0 : ℝ) 1, (τ t).re) :=
        (ofReal_integral_eq_lintegral_ofReal hτint.re
          (Eventually.of_forall fun t => bornSum_re_nonneg P hρ (measurableSet_lev κ hB' t))).symm
    _ = ENNReal.ofReal (bornSum (postEffect P κ B') ρ).re := by rw [h2, hre]

/-! ### The statement -/

theorem solution {I Ω Ω' : Type} [DecidableEq I] [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : FockPOVM I Ω) (κ : Kernel Ω Ω') (hκ : IsMarkovKernel κ) :
    ∃ P' : FockPOVM I Ω', ∀ ρ : Matrix I I ℂ, P'.law ρ = (P.law ρ).bind κ := by
  refine ⟨{
    effect := postEffect P κ
    effect_form := fun B hB => postEffect_effB P κ hB
    effect_univ := postEffect_univ P κ
    law := fun ρ => (P.law ρ).bind κ
    law_prob := fun ρ hρ => ?_
    law_born := fun ρ hρ B hB => post_born P κ hρ hB }, fun ρ => rfl⟩
  have hprob := P.law_prob ρ hρ
  constructor
  rw [Measure.bind_apply MeasurableSet.univ κ.aemeasurable]
  simp
