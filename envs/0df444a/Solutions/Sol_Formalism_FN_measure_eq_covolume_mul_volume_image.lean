-- Prove2me | solution 1 for Formalism.FN.measure_eq_covolume_mul_volume_image
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:09.738821+00:00
-- url     : https://prove2.me/submissions/2e52dbc3-36d5-4acd-9cb6-ee994c27a38d

import Definitions.Def_Formalism_SuccessiveMinima_DefsMink
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_MeasureEqCovolumeMulVolumeImage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module Metric Set
open scoped Pointwise ENNReal
noncomputable section
open Formalism Formalism.FN
namespace Formalism.FN
theorem _root_.solution {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {ι : Type} [Fintype ι] (b : Basis ι ℤ L) (S : Set E) :
    μ S = ENNReal.ofReal (ZLattice.covolume L μ) *
      volume ((b.ofZLatticeBasis ℝ L).equivFun '' S) := by
  set B := b.ofZLatticeBasis ℝ L with hB
  let f : E ≃ᵐ (ι → ℝ) := B.equivFunL.toHomeomorph.toMeasurableEquiv
  have hf : (f : E → ι → ℝ) = B.equivFun := rfl
  have : (μ.map f).IsAddHaarMeasure := B.equivFunL.isAddHaarMeasure_map μ
  have huniq := MeasureTheory.Measure.isAddLeftInvariant_eq_smul (μ.map f) volume
  obtain ⟨c, hc⟩ : ∃ c, c = MeasureTheory.Measure.addHaarScalarFactor (μ.map f) volume := ⟨_, rfl⟩
  rw [← hc] at huniq
  have himg : ∀ T : Set E, μ T = c * volume (B.equivFun '' T) := by
    intro T
    have h1 : μ T = μ.map f (f '' T) := by
      rw [MeasurableEquiv.map_apply, Set.preimage_image_eq T f.injective]
    rw [h1, huniq, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, hf]
  have hD : (B.equivFun : E → ι → ℝ) '' ZSpan.fundamentalDomain B =
      Set.univ.pi fun _ : ι => Set.Ico (0 : ℝ) 1 := by
    have h : ZSpan.fundamentalDomain B =
        (B.equivFun : E → ι → ℝ) ⁻¹' (Set.univ.pi fun _ : ι => Set.Ico (0 : ℝ) 1) := by
      ext x
      simp [ZSpan.mem_fundamentalDomain, Set.mem_pi]
    rw [h, Set.image_preimage_eq _ B.equivFun.surjective]
  have hvol : volume (Set.univ.pi fun _ : ι => Set.Ico (0 : ℝ) 1) = 1 := by
    rw [volume_pi_pi]
    simp
  have hcov : c = ENNReal.ofReal (ZLattice.covolume L μ) := by
    have h := himg (ZSpan.fundamentalDomain B)
    rw [hD, hvol, mul_one] at h
    rw [← h, ZLattice.covolume_eq_measure_fundamentalDomain L μ (ZLattice.isAddFundamentalDomain b μ),
      measureReal_def, ENNReal.ofReal_toReal]
    exact (Bornology.IsBounded.measure_lt_top (ZSpan.fundamentalDomain_isBounded B)).ne
  rw [himg S, hcov]
end Formalism.FN
