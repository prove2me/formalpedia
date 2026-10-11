-- Prove2me | solution 1 for BookProof.NsFieldMomentumInverse.momDomain_dense
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:44:50.711487+00:00
-- url     : https://prove2.me/submissions/324d33f1-7ed4-4d31-a4b0-f93999e908f3

-- Generated from ChapterNsFieldMomentumInverse.lean — solution of BookProof.NsFieldMomentumInverse.momDomain_dense
import Mathlib
import Definitions.Def_ChapterNsFieldMomentumInverse
import Theorems.Thm_BookProof_NsFieldMomentumInverse_momSymbol_ne_zero_ae
import Theorems.Thm_BookProof_NsFieldMomentumInverse_coeFn_cut
import Theorems.Thm_BookProof_NsFieldMomentumInverse_cut_mem_momDomain
import Definitions.Def_ChapterNsSpatialMomentumMultiplier
import Definitions.Def_ChapterFourierMultiplierEsa
import Definitions.Def_ChapterStrichartzWave
open BookProof.NsFieldMomentumInverse




open MeasureTheory SchwartzMap FourierTransform
open BookProof.NsSpatialMultiplier BookProof.FourierMultiplierEsa BookProof.StrichartzWave

noncomputable section

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

set_option maxHeartbeats 1000000 in
theorem solution {m : W} (hm : m ≠ 0) :
    Dense ((momDomain m : Set (Lp ℂ 2 (volume : Measure W)))) := by

  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff]
  refine Submodule.eq_bot_iff _ |>.2 fun h hh => ?_
  -- `h` is orthogonal to every cut-off state, hence vanishes on every cut set
  have hzero : ∀ n : ℕ, ∀ᵐ ξ ∂(volume : Measure W), ξ ∈ cutSet m n → (h : W → ℂ) ξ = 0 := by
    intro n
    have hmem : cut m n h ∈ momDomain m := cut_mem_momDomain hm n h
    have hinner : (inner ℂ (cut m n h) h : ℂ) = 0 := hh _ hmem
    have hint : (∫ ξ, (cutSet m n).indicator (fun ξ => (‖(h : W → ℂ) ξ‖ ^ 2 : ℝ)) ξ) = 0 := by
      have hcalc : (inner ℂ (cut m n h) h : ℂ)
          = ((∫ ξ, (cutSet m n).indicator (fun ξ => (‖(h : W → ℂ) ξ‖ ^ 2 : ℝ)) ξ : ℝ) : ℂ) := by
        rw [MeasureTheory.L2.inner_def]
        rw [← integral_complex_ofReal]
        refine integral_congr_ae ?_
        filter_upwards [coeFn_cut m n h] with ξ hξ
        rw [hξ]
        by_cases hmemξ : ξ ∈ cutSet m n
        · rw [Set.indicator_of_mem hmemξ, Set.indicator_of_mem hmemξ,
            inner_self_eq_norm_sq_to_K]
          norm_cast
        · rw [Set.indicator_of_notMem hmemξ, Set.indicator_of_notMem hmemξ]
          simp
      rw [hcalc] at hinner
      exact_mod_cast hinner
    have hnonneg : 0 ≤ᵐ[(volume : Measure W)]
        fun ξ => (cutSet m n).indicator (fun ξ => (‖(h : W → ℂ) ξ‖ ^ 2 : ℝ)) ξ :=
      Filter.Eventually.of_forall fun ξ => Set.indicator_nonneg (fun _ _ => by positivity) ξ
    have hintg : Integrable
        (fun ξ => (cutSet m n).indicator (fun ξ => (‖(h : W → ℂ) ξ‖ ^ 2 : ℝ)) ξ)
        (volume : Measure W) := by
      have : Integrable (fun ξ => (‖(h : W → ℂ) ξ‖ ^ 2 : ℝ)) (volume : Measure W) := by
        simpa [Real.rpow_natCast] using
          (MeasureTheory.Lp.memLp h).integrable_norm_rpow (by norm_num) (by norm_num)
      exact this.indicator (measurableSet_cutSet m n)
    have hae := (integral_eq_zero_iff_of_nonneg_ae hnonneg hintg).1 hint
    filter_upwards [hae] with ξ hξ hmemξ
    rw [Set.indicator_of_mem hmemξ] at hξ
    have : ‖(h : W → ℂ) ξ‖ = 0 := by
      have := hξ
      simpa [pow_eq_zero_iff] using this
    simpa using this
  have hall : ∀ᵐ ξ ∂(volume : Measure W), ∀ n : ℕ, ξ ∈ cutSet m n → (h : W → ℂ) ξ = 0 :=
    (MeasureTheory.ae_all_iff).2 hzero
  refine (Submodule.mem_bot ℂ).2 ?_
  refine (MeasureTheory.Lp.eq_zero_iff_ae_eq_zero).2 ?_
  filter_upwards [hall, momSymbol_ne_zero_ae hm] with ξ hξ hσ
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0:ℝ) < |momSymbol m ξ| from abs_pos.2 hσ)
  exact hξ n (le_of_lt hn)
