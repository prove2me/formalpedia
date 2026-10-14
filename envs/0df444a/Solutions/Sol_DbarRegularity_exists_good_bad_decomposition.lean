-- Prove2me | solution 1 for DbarRegularity.exists_good_bad_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T15:42:37.424172+00:00
-- url     : https://prove2.me/submissions/160dc669-9343-408a-84e5-b8141b4ffdc8

import Definitions.Def_DbarRegularity_Setting
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Theorems.Thm_DbarRegularity_calderonZygmund_decomposition
import Theorems.Thm_DbarRegularity_volume_closedCube
import Theorems.Thm_DbarRegularity_isClosed_closedCube
import Theorems.Thm_DbarRegularity_dist_le_of_mem_closedCube
import Theorems.Thm_DbarRegularity_volume_closedCube_diff_interior
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace



namespace DbarRegularity

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal

/-- Calderón–Zygmund good/bad splitting of an integrable `f : ℝ^d → ℂ` at height `α`:
`f = g + ∑ₖ bₖ` with `|g| ≤ 2^d α` a.e., `‖g‖₁ ≤ ‖f‖₁`, and mean-zero pieces `bₖ` with disjoint
supports in balls `B̄(cₖ, rₖ)` such that `∑ ‖bₖ‖₁ ≤ 2 ‖f‖₁` and `∑ |B(cₖ, 2rₖ)| ≤ (C / α) ‖f‖₁`. -/
theorem exists_good_bad_decomposition {d : ℕ} (hd : 0 < d) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (f : EuclideanSpace ℝ (Fin d) → ℂ), Integrable f volume →
      ∀ α : ℝ, 0 < α →
      ∃ (ι : Type) (_ : Countable ι) (c : ι → EuclideanSpace ℝ (Fin d)) (r : ι → ℝ)
        (b : ι → EuclideanSpace ℝ (Fin d) → ℂ),
        (∀ k, Integrable (b k) volume) ∧
        (∀ k, ∫ x, b k x = 0) ∧
        (∀ k x, b k x ≠ 0 → x ∈ closedBall (c k) (r k)) ∧
        (∀ x k l, b k x ≠ 0 → b l x ≠ 0 → k = l) ∧
        Integrable (fun x => ∑' k, b k x) volume ∧
        (∀ᵐ x, ‖f x - ∑' k, b k x‖ ≤ 2 ^ d * α) ∧
        eLpNorm (fun x => f x - ∑' k, b k x) 1 volume ≤ eLpNorm f 1 volume ∧
        ∑' k, eLpNorm (b k) 1 volume ≤ 2 * eLpNorm f 1 volume ∧
        ∑' k, volume (ball (c k) (2 * r k)) ≤ C / ENNReal.ofReal α * eLpNorm f 1 volume := by
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := finrank_euclideanSpace_fin
  refine ⟨ENNReal.ofReal ((2 * Real.sqrt d) ^ d) *
      volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1),
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne, ?_⟩
  intro f hf α hα
  obtain ⟨F, Ω, ι, hι, a, s, hFΩ, hdisjFΩ, hF, hΩ, hs, hpair, havg⟩ :=
    calderonZygmund_decomposition hd (fun x => ‖f x‖) (fun x => norm_nonneg _) hf.norm α hα
  set Q : ι → Set (EuclideanSpace ℝ (Fin d)) := fun k => closedCube (a k) (s k) with hQdef
  set O : ι → Set (EuclideanSpace ℝ (Fin d)) := fun k => interior (Q k) with hOdef
  have hOm : ∀ k, MeasurableSet (O k) := fun k => isOpen_interior.measurableSet
  have hQm : ∀ k, MeasurableSet (Q k) := fun k => (isClosed_closedCube _ _).measurableSet
  have hQO : ∀ k, Q k =ᵐ[volume] O k := by
    intro k
    refine ae_eq_set.2 ⟨volume_closedCube_diff_interior _ _, ?_⟩
    rw [diff_eq_empty.2 interior_subset, measure_empty]
  have hvolQ : ∀ k, volume (Q k) = ENNReal.ofReal (s k) ^ d := fun k => volume_closedCube _ _
  have hQne : ∀ k, volume (Q k) ≠ 0 := by
    intro k; rw [hvolQ]; exact pow_ne_zero _ (ENNReal.ofReal_pos.2 (hs k)).ne'
  have hQtop : ∀ k, volume (Q k) ≠ ⊤ := by
    intro k; rw [hvolQ]; exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hvO : ∀ k, volume (O k) = volume (Q k) := fun k => measure_congr (hQO k).symm
  set v : ι → ℝ := fun k => (volume (Q k)).toReal with hvdef
  have hv : ∀ k, 0 < v k := fun k => ENNReal.toReal_pos (hQne k) (hQtop k)
  have hvQ : ∀ k, volume (Q k) = ENNReal.ofReal (v k) := fun k =>
    (ENNReal.ofReal_toReal (hQtop k)).symm
  set m : ι → ℂ := fun k => (∫ x in Q k, f x) / (v k : ℂ) with hmdef
  set b : ι → EuclideanSpace ℝ (Fin d) → ℂ := fun k => (O k).indicator (fun x => f x - m k)
    with hbdef
  -- averages
  have hlow : ∀ k, α * v k < ∫ x in Q k, ‖f x‖ := by
    intro k; have := (havg k).1; rwa [lt_div_iff₀ (hv k)] at this
  have hup : ∀ k, (∫ x in Q k, ‖f x‖) ≤ 2 ^ d * α * v k := by
    intro k; have := (havg k).2; rwa [div_le_iff₀ (hv k)] at this
  have hnm : ∀ k, ‖m k‖ * v k ≤ ∫ x in Q k, ‖f x‖ := by
    intro k
    simp only [hmdef, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hv k)]
    rw [div_mul_cancel₀ _ (hv k).ne']
    exact norm_integral_le_integral_norm _
  have hlQ : ∀ k, ∫⁻ x in Q k, ‖f x‖ₑ = ENNReal.ofReal (∫ x in Q k, ‖f x‖) := fun k =>
    (ofReal_integral_norm_eq_lintegral_enorm hf.integrableOn).symm
  have hlO : ∀ k, ∫⁻ x in O k, ‖f x‖ₑ = ∫⁻ x in Q k, ‖f x‖ₑ := fun k =>
    setLIntegral_congr (hQO k).symm
  have hmQ : ∀ k, ‖m k‖ₑ * volume (O k) ≤ ∫⁻ x in O k, ‖f x‖ₑ := by
    intro k
    rw [hvO, hvQ, hlO, hlQ, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hnm k)
  -- the tsum
  have hBO : ∀ k x, x ∈ O k → ∑' l, b l x = f x - m k := by
    intro k x hx
    rw [tsum_eq_single k]
    · simp [hbdef, indicator_of_mem hx]
    · intro l hl
      have : x ∉ O l := fun hx' => Set.disjoint_left.1 (hpair hl.symm) hx hx'
      simp [hbdef, indicator_of_notMem this]
  have hBn : ∀ x, (∀ k, x ∉ O k) → ∑' l, b l x = 0 := by
    intro x hx
    simp [hbdef, indicator_of_notMem (hx _)]
  have hbint : ∀ k, Integrable (b k) volume := by
    intro k
    refine (integrable_indicator_iff (hOm k)).2 ?_
    refine hf.integrableOn.sub ?_
    exact integrableOn_const (by rw [hvO]; exact hQtop k)
  have hSum : ∀ x, Summable (fun k => b k x) := by
    intro x
    by_cases h : ∃ k, x ∈ O k
    · obtain ⟨k, hk⟩ := h
      refine (hasSum_single k fun l hl => ?_).summable
      have : x ∉ O l := fun hx' => Set.disjoint_left.1 (hpair hl.symm) hk hx'
      simp [hbdef, indicator_of_notMem this]
    · push_neg at h
      have : (fun k => b k x) = fun _ => 0 := by
        funext k; simp [hbdef, indicator_of_notMem (h k)]
      rw [this]; exact summable_zero
  -- L¹ bounds for the pieces
  have hbk : ∀ k, eLpNorm (b k) 1 volume ≤ 2 * ∫⁻ x in O k, ‖f x‖ₑ := by
    intro k
    rw [eLpNorm_one_eq_lintegral_enorm]
    simp only [hbdef, enorm_indicator_eq_indicator_enorm]
    rw [lintegral_indicator (hOm k)]
    calc ∫⁻ x in O k, ‖f x - m k‖ₑ ≤ ∫⁻ x in O k, (‖f x‖ₑ + ‖m k‖ₑ) :=
          lintegral_mono fun x => enorm_sub_le
      _ = (∫⁻ x in O k, ‖f x‖ₑ) + ‖m k‖ₑ * volume (O k) := by
          rw [lintegral_add_right _ measurable_const, setLIntegral_const]
      _ ≤ (∫⁻ x in O k, ‖f x‖ₑ) + ∫⁻ x in O k, ‖f x‖ₑ := by gcongr; exact hmQ k
      _ = 2 * ∫⁻ x in O k, ‖f x‖ₑ := by rw [two_mul]
  have hUnion : ∑' k, ∫⁻ x in O k, ‖f x‖ₑ = ∫⁻ x in ⋃ k, O k, ‖f x‖ₑ :=
    (lintegral_iUnion hOm hpair _).symm
  have hsumb : ∑' k, eLpNorm (b k) 1 volume ≤ 2 * eLpNorm f 1 volume := by
    calc ∑' k, eLpNorm (b k) 1 volume ≤ ∑' k, 2 * ∫⁻ x in O k, ‖f x‖ₑ :=
          ENNReal.tsum_le_tsum hbk
      _ = 2 * ∫⁻ x in ⋃ k, O k, ‖f x‖ₑ := by rw [ENNReal.tsum_mul_left, hUnion]
      _ ≤ 2 * eLpNorm f 1 volume := by
          rw [eLpNorm_one_eq_lintegral_enorm]; gcongr; exact Measure.restrict_le_self
  have hfL1 : eLpNorm f 1 volume < ⊤ := (memLp_one_iff_integrable.2 hf).2
  refine ⟨ι, hι, a, fun k => Real.sqrt d * s k, b, hbint, ?_, ?_, ?_, ?_, ?_, ?_, hsumb, ?_⟩
  · -- mean zero
    intro k
    simp only [hbdef]
    rw [integral_indicator (hOm k), integral_sub hf.integrableOn
      (integrableOn_const (by rw [hvO]; exact hQtop k)), setIntegral_const,
      setIntegral_congr_set (hQO k).symm]
    have hvr : volume.real (O k) = v k := by
      simp [measureReal_def, hvO, hvdef]
    rw [hvr, Complex.real_smul, hmdef]
    have : (v k : ℂ) ≠ 0 := by exact_mod_cast (hv k).ne'
    field_simp
    ring
  · -- support
    intro k x hx
    have hxO : x ∈ O k := by
      by_contra h; exact hx (by simp [hbdef, indicator_of_notMem h])
    have hxQ : x ∈ Q k := interior_subset hxO
    have haQ : a k ∈ Q k := fun i => ⟨le_rfl, by linarith [hs k]⟩
    rw [mem_closedBall]
    exact dist_le_of_mem_closedCube haQ hxQ
  · -- disjoint supports
    intro x k l hk hl
    by_contra hkl
    have hxk : x ∈ O k := by
      by_contra h; exact hk (by simp [hbdef, indicator_of_notMem h])
    have hxl : x ∈ O l := by
      by_contra h; exact hl (by simp [hbdef, indicator_of_notMem h])
    exact Set.disjoint_left.1 (hpair hkl) hxk hxl
  · -- integrability of the tsum
    refine ⟨?_, ?_⟩
    · refine aestronglyMeasurable_of_tendsto_ae (u := (atTop : Filter (Finset ι)))
        (f := fun (t : Finset ι) x => ∑ k ∈ t, b k x) (fun t => ?_)
        (ae_of_all _ fun x => (hSum x).hasSum)
      exact Finset.aestronglyMeasurable_fun_sum t (fun k _ => (hbint k).1)
    · rw [hasFiniteIntegral_iff_enorm]
      calc ∫⁻ x, ‖∑' k, b k x‖ₑ ≤ ∫⁻ x, ∑' k, ‖b k x‖ₑ :=
            lintegral_mono fun x => enorm_tsum_le_tsum_enorm
        _ = ∑' k, ∫⁻ x, ‖b k x‖ₑ := lintegral_tsum fun k => (hbint k).1.enorm
        _ = ∑' k, eLpNorm (b k) 1 volume := by simp [eLpNorm_one_eq_lintegral_enorm]
        _ < ⊤ := lt_of_le_of_lt hsumb (ENNReal.mul_lt_top (by norm_num) hfL1)
  · -- the good part is bounded
    have hnull : volume (⋃ k, (Q k \ O k)) = 0 :=
      measure_iUnion_null fun k => volume_closedCube_diff_interior _ _
    have hnull' : ∀ᵐ x, x ∉ ⋃ k, (Q k \ O k) := by
      exact ae_iff.2 (by simp only [not_not, setOf_mem_eq]; exact hnull)
    filter_upwards [hF, hnull'] with x hxF hxN
    by_cases h : ∃ k, x ∈ O k
    · obtain ⟨k, hk⟩ := h
      rw [hBO k x hk, sub_sub_cancel]
      have h1 : ‖m k‖ * v k ≤ 2 ^ d * α * v k := (hnm k).trans (hup k)
      exact le_of_mul_le_mul_right h1 (hv k)
    · push_neg at h
      rw [hBn x h, sub_zero]
      have hxF' : x ∈ F := by
        rcases (Set.ext_iff.1 hFΩ x).2 trivial with hx | hx
        · exact hx
        · exfalso
          rw [hΩ] at hx
          obtain ⟨k, hk⟩ := mem_iUnion.1 hx
          exact hxN (mem_iUnion.2 ⟨k, hk, h k⟩)
      have := hxF hxF'
      have h2 : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
      nlinarith
  · -- L¹ norm of the good part
    rw [eLpNorm_one_eq_lintegral_enorm, eLpNorm_one_eq_lintegral_enorm]
    have hpt : ∀ x, ‖f x - ∑' k, b k x‖ₑ ≤ (⋃ k, O k)ᶜ.indicator (fun x => ‖f x‖ₑ) x +
        ∑' k, (O k).indicator (fun _ => ‖m k‖ₑ) x := by
      intro x
      by_cases h : ∃ k, x ∈ O k
      · obtain ⟨k, hk⟩ := h
        rw [hBO k x hk, sub_sub_cancel]
        have : x ∉ (⋃ k, O k)ᶜ := fun h' => h' (mem_iUnion.2 ⟨k, hk⟩)
        rw [indicator_of_notMem this, zero_add, tsum_eq_single k, indicator_of_mem hk]
        intro l hl
        have : x ∉ O l := fun hx' => Set.disjoint_left.1 (hpair hl.symm) hk hx'
        rw [indicator_of_notMem this]
      · push_neg at h
        rw [hBn x h, sub_zero]
        have : x ∈ (⋃ k, O k)ᶜ := fun h' => by
          obtain ⟨k, hk⟩ := mem_iUnion.1 h'; exact h k hk
        rw [indicator_of_mem this]
        simp [indicator_of_notMem (h _)]
    calc ∫⁻ x, ‖f x - ∑' k, b k x‖ₑ
        ≤ ∫⁻ x, ((⋃ k, O k)ᶜ.indicator (fun x => ‖f x‖ₑ) x +
            ∑' k, (O k).indicator (fun _ => ‖m k‖ₑ) x) := lintegral_mono hpt
      _ = (∫⁻ x in (⋃ k, O k)ᶜ, ‖f x‖ₑ) + ∑' k, ‖m k‖ₑ * volume (O k) := by
          rw [lintegral_add_right' _ (AEMeasurable.ennreal_tsum fun k =>
              (aemeasurable_const.indicator (hOm k))),
            lintegral_indicator (MeasurableSet.iUnion hOm).compl,
            lintegral_tsum fun k => aemeasurable_const.indicator (hOm k)]
          simp only [lintegral_indicator_const (hOm _)]
      _ ≤ (∫⁻ x in (⋃ k, O k)ᶜ, ‖f x‖ₑ) + ∑' k, ∫⁻ x in O k, ‖f x‖ₑ := by
          gcongr with k; exact hmQ k
      _ = ∫⁻ x, ‖f x‖ₑ := by
          rw [hUnion, add_comm, lintegral_add_compl _ (MeasurableSet.iUnion hOm)]
  · -- total measure of the doubled balls
    have hball : ∀ k, volume (ball (a k) (2 * (Real.sqrt d * s k))) =
        ENNReal.ofReal ((2 * Real.sqrt d) ^ d) *
          volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1) * volume (Q k) := by
      intro k
      have hpos : 0 < 2 * (Real.sqrt d * s k) := by
        have : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
        have := hs k; positivity
      rw [Measure.addHaar_ball_of_pos _ _ hpos, hfin, hvolQ, ← ENNReal.ofReal_pow (hs k).le,
        show 2 * (Real.sqrt d * s k) = (2 * Real.sqrt d) * s k by ring, mul_pow,
        ENNReal.ofReal_mul (by positivity)]
      ring
    have hQle : ∀ k, volume (Q k) ≤ (∫⁻ x in O k, ‖f x‖ₑ) / ENNReal.ofReal α := by
      intro k
      rw [hvQ, hlO, hlQ, ← ENNReal.ofReal_div_of_pos hα]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [le_div_iff₀ hα]; linarith [hlow k]
    calc ∑' k, volume (ball (a k) (2 * (Real.sqrt d * s k)))
        = ∑' k, ENNReal.ofReal ((2 * Real.sqrt d) ^ d) *
            volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1) * volume (Q k) := tsum_congr hball
      _ ≤ ∑' k, ENNReal.ofReal ((2 * Real.sqrt d) ^ d) *
            volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1) *
              ((∫⁻ x in O k, ‖f x‖ₑ) / ENNReal.ofReal α) := by
          gcongr with k; exact hQle k
      _ = ENNReal.ofReal ((2 * Real.sqrt d) ^ d) *
            volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1) / ENNReal.ofReal α *
              ∑' k, ∫⁻ x in O k, ‖f x‖ₑ := by
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun k => ?_
          simp only [div_eq_mul_inv]; ring
      _ ≤ _ := by
          rw [hUnion, eLpNorm_one_eq_lintegral_enorm]
          gcongr
          exact Measure.restrict_le_self

end DbarRegularity

open DbarRegularity

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal

theorem solution {d : ℕ} (hd : 0 < d) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (f : EuclideanSpace ℝ (Fin d) → ℂ), Integrable f volume →
      ∀ α : ℝ, 0 < α →
      ∃ (ι : Type) (_ : Countable ι) (c : ι → EuclideanSpace ℝ (Fin d)) (r : ι → ℝ)
        (b : ι → EuclideanSpace ℝ (Fin d) → ℂ),
        (∀ k, Integrable (b k) volume) ∧
        (∀ k, ∫ x, b k x = 0) ∧
        (∀ k x, b k x ≠ 0 → x ∈ closedBall (c k) (r k)) ∧
        (∀ x k l, b k x ≠ 0 → b l x ≠ 0 → k = l) ∧
        Integrable (fun x => ∑' k, b k x) volume ∧
        (∀ᵐ x, ‖f x - ∑' k, b k x‖ ≤ 2 ^ d * α) ∧
        eLpNorm (fun x => f x - ∑' k, b k x) 1 volume ≤ eLpNorm f 1 volume ∧
        ∑' k, eLpNorm (b k) 1 volume ≤ 2 * eLpNorm f 1 volume ∧
        ∑' k, volume (ball (c k) (2 * r k)) ≤ C / ENNReal.ofReal α * eLpNorm f 1 volume :=
  exists_good_bad_decomposition hd
