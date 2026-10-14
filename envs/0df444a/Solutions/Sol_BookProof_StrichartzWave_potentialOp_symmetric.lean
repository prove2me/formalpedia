-- Prove2me | solution 1 for BookProof.StrichartzWave.potentialOp_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-12T06:53:55.210977+00:00
-- url     : https://prove2.me/submissions/218bbe07-6f33-49bf-ba2f-265ac8ab4497

-- Generated from ChapterWaveUnboundedPotential.lean — solution of BookProof.StrichartzWave.potentialOp_symmetric
import Mathlib
import Definitions.Def_ChapterWaveUnboundedPotential
import Theorems.Thm_BookProof_StrichartzWave_inner_toLp_left
import Theorems.Thm_BookProof_StrichartzWave_opL2_apply
import Theorems.Thm_BookProof_StrichartzWave_schwartzEquiv_coe
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave




open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace ENNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! `potentialOp_apply` and its helper exist in the source chapter
(`BookProof/ChapterWaveUnboundedPotential.lean`) but no `Theorems/Thm_…` stub was
generated for them, so no solution may import them.  Both are one-line
unfolding lemmas over declarations the platform DOES serve (`potentialOp` in the
published bundle, `SchwartzMap.smulLeftCLM_apply_apply` from Mathlib), so they are
stated locally as `private` and the file stays standalone — the same repair that
made the `TensorCore` solutions acceptable.
-/

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
private theorem hasTemperateGrowth_ofReal' {W : V → ℝ}
    (hW : Function.HasTemperateGrowth W) :
    Function.HasTemperateGrowth (fun x => (W x : ℂ)) := by
  exact Function.HasTemperateGrowth.comp Complex.ofRealCLM.hasTemperateGrowth hW

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
private theorem potentialOp_apply' {W : V → ℝ} (hW : Function.HasTemperateGrowth W)
    (f : 𝓢(V, ℂ)) (x : V) : potentialOp W f x = (W x : ℂ) * f x := by
  simp [potentialOp, SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_ofReal' hW)]

set_option maxHeartbeats 1000000 in
theorem solution (W : V → ℝ) (hW : Function.HasTemperateGrowth W) :
    BookProof.FarisLavine.SymmetricOn (schwartzDomain V) (opL2 (potentialOp W)) := by

  intro x y
  obtain ⟨f, rfl⟩ := (schwartzEquiv V).surjective x
  obtain ⟨g, rfl⟩ := (schwartzEquiv V).surjective y
  rw [opL2_apply, opL2_apply, schwartzEquiv_coe, schwartzEquiv_coe, inner_toLp_left,
    inner_toLp_left]
  refine integral_congr_ae ?_
  filter_upwards [g.coeFn_toLp 2 (volume : Measure V),
    (potentialOp W g).coeFn_toLp 2 (volume : Measure V)] with x hx hy
  rw [hx, hy]
  simp only [potentialOp_apply' hW, map_mul, Complex.conj_ofReal]
  ring
