-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LatSum.map_equivFun
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:29.330065+00:00
-- url     : https://prove2.me/submissions/b093a1b3-95a4-452c-ac6a-205015233a3d

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoTsumDivPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module MeasureTheory Filter Topology Bornology Pointwise ZLattice
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LatSum
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
variable {ι : Type*} [Fintype ι]
namespace Formalism.HermitianLattices.Ext.L3.LatSum
theorem _root_.solution (μ : Measure E) [μ.IsAddHaarMeasure] (b : Basis ι ℤ L) :
    μ.map (b.ofZLatticeBasis ℝ L).equivFunL = ENNReal.ofReal (covolume L μ) • volume := by
  classical
  set e := (b.ofZLatticeBasis ℝ L).equivFunL with he
  have h := Measure.addHaarMeasure_unique (μ.map e) (TopologicalSpace.PositiveCompacts.piIcc01 ι)
  rw [addHaarMeasure_eq_volume_pi] at h
  have hF := ZLattice.isAddFundamentalDomain b μ
  have hc : (μ.map e) (TopologicalSpace.PositiveCompacts.piIcc01 ι) = ENNReal.ofReal (covolume L μ) := by
    have h1 : (μ.map e) (Set.univ.pi fun _ : ι => Set.Ico (0 : ℝ) 1) =
        (μ.map e) (TopologicalSpace.PositiveCompacts.piIcc01 ι) := by
      conv_lhs => rw [h]
      rw [Measure.smul_apply, Real.volume_pi_Ico]
      simp
    rw [← h1, Measure.map_apply e.continuous.measurable
      (MeasurableSet.univ_pi fun _ => measurableSet_Ico),
      covolume_eq_measure_fundamentalDomain L μ hF, measureReal_def,
      ENNReal.ofReal_toReal (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne]
    congr 1
    ext x
    simp [ZSpan.mem_fundamentalDomain, Set.mem_pi, he]
  rw [h, hc]
end Formalism.HermitianLattices.Ext.L3.LatSum
