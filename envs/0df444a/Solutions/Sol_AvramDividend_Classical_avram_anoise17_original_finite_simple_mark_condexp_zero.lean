-- Prove2me | solution 1 for AvramDividend.Classical.avram_anoise17_original_finite_simple_mark_condexp_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T00:56:25.77841+00:00
-- url     : https://prove2.me/submissions/29d40722-e5a4-45e9-baeb-48e409b3337d

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump11_source_finite_band_rightCont_condexp_zero
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_finite_nu_count_real_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_borel_marked_unconditional_levy_rate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*} [DecidableEq ι]
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (r : ℕ → ℝ≥0)
    (hsr : ∀ n, s < r n) (hrt : ∀ n, r n ≤ t)
    (hShort : Tendsto (fun n => r n - s) atTop (𝓝 0))
    (hLong : Tendsto (fun n => t - r n) atTop (𝓝 (t - s)))
    (S : Finset ι) (B : ι → Set ℝ)
    (hB : ∀ i ∈ S, MeasurableSet (B i))
    (hFinite : ∀ i ∈ S, X.ν (B i) ≠ ⊤)
    (J : ι → ℝ≥0 → ℝ≥0 → Ω → ℝ≥0∞)
    (hJsource : ∀ i ∈ S, ∀ a b ω,
      J i a b ω =
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc a b ×ˢ B i))
    (hJmeas : ∀ i ∈ S, Measurable (J i s t))
    (weights : ι → ℝ) :
    P[(fun ω => ∑ i ∈ S, weights i *
      ((J i s t ω).toReal -
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (B i)).toReal)) |
        𝓕.rightCont s] =ᵐ[P] (fun _ => (0 : ℝ)) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  have hst : s ≤ t := (hsr 0).le.trans (hrt 0)
  let C (i : ι) : Ω → ℝ := fun ω =>
    (J i s t ω).toReal -
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (B i)).toReal
  let F (i : ι) : Ω → ℝ := fun ω => weights i * C i ω
  have hCint (i : ι) (hi : i ∈ S) : Integrable (C i) P := by
    have hν : X.ν (B i) < ⊤ := lt_top_iff_ne_top.mpr (hFinite i hi)
    have hRate :
        (∫⁻ ω, J i s t ω ∂P) =
          ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (B i) := by
      simpa only [hJsource i hi] using
        (avram_wave7_01_original_intrinsic_borel_marked_unconditional_levy_rate
          X s t hst (B i) (hB i hi))
    have hRaw : Integrable (fun ω => (J i s t ω).toReal) P := by
      simpa only [hJsource i hi] using
        (avram_p2_e_compensator_finite_nu_count_real_integrable
          X s t hst (B i) (hB i hi) hν
          (by simpa only [hJsource i hi] using hRate))
    exact hRaw.sub (integrable_const _)
  have hFint (i : ι) (hi : i ∈ S) : Integrable (F i) P := by
    exact (hCint i hi).const_mul (weights i)
  have hCzero (i : ι) (hi : i ∈ S) :
      P[C i | 𝓕.rightCont s] =ᵐ[P] (fun _ => (0 : ℝ)) := by
    have hsource :=
      avram_ubv_jump11_source_finite_band_rightCont_condexp_zero
        X s t r hsr hrt (B i) (hB i hi) (J i)
        (hJsource i hi) hShort hLong (hFinite i hi) (hJmeas i hi)
    filter_upwards [hsource] with ω hω
    simpa only [C, Pi.zero_apply] using hω
  have hFzero (i : ι) (hi : i ∈ S) :
      P[F i | 𝓕.rightCont s] =ᵐ[P] (fun _ => (0 : ℝ)) := by
    have hmul := MeasureTheory.condExp_smul (μ := P)
      (weights i) (C i) (𝓕.rightCont s)
    filter_upwards [hmul, hCzero i hi] with ω hω hzero
    have hF : F i = weights i • C i := by
      funext ξ
      simp only [F, Pi.smul_apply, smul_eq_mul]
    have hpoint : P[F i | 𝓕.rightCont s] ω =
        weights i * P[C i | 𝓕.rightCont s] ω := by
      rw [hF]
      simpa only [Pi.smul_apply, smul_eq_mul] using hω
    simpa only [hzero, mul_zero] using hpoint
  have hfinite_zero :
      ∀ᵐ ω ∂P, ∀ i ∈ S, P[F i | 𝓕.rightCont s] ω = 0 := by
    have haux (S' : Finset ι) :
        (∀ i ∈ S', P[F i | 𝓕.rightCont s] =ᵐ[P] (fun _ => (0 : ℝ))) →
        ∀ᵐ ω ∂P, ∀ i ∈ S', P[F i | 𝓕.rightCont s] ω = 0 := by
      induction S' using Finset.induction_on with
      | empty =>
          intro _
          filter_upwards [] with ω
          simp
      | @insert i S' hnot ih =>
          intro H
          have hi := H i (Finset.mem_insert_self i S')
          have hrest := ih (by
            intro j hj
            exact H j (Finset.mem_insert_of_mem hj))
          filter_upwards [hi, hrest] with ω hiω hrestω
          intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hj
          · exact hiω
          · exact hrestω j hj
    exact haux S hFzero
  have hsum := MeasureTheory.condExp_finsetSum
    (μ := P) (s := S) (f := F) hFint (𝓕.rightCont s)
  filter_upwards [hsum, hfinite_zero] with ω hsumω hzeroω
  have hSzero : (∑ i ∈ S, P[F i | 𝓕.rightCont s] ω) = 0 :=
    Finset.sum_eq_zero (fun i hi => hzeroω i hi)
  have hSzero' : (∑ i ∈ S, P[F i | 𝓕.rightCont s]) ω = 0 := by
    simpa only [Finset.sum_apply] using hSzero
  have hFsumEq :
      (∑ i ∈ S, F i) = (fun ξ => ∑ i ∈ S, F i ξ) := by
    funext ξ
    simp only [Finset.sum_apply]
  rw [hFsumEq] at hsumω
  simpa only [F, C] using hsumω.trans hSzero'
