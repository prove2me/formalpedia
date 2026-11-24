-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BallA.tendsto_card_div_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:32:27.511356+00:00
-- url     : https://prove2.me/submissions/bdef7593-c39c-4009-9781-6b5d6a6014be

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_DiscreteTopologyOfZsmul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallA_volume_image_equivFun

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module ZSpan Filter Topology Pointwise Bornology
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BallA
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (μ : Measure E) [μ.IsAddHaarMeasure]
namespace Formalism.HermitianLattices.Ext.L3.BallA
theorem _root_.solution {s : Set E} (hs₁ : IsBounded s) (hs₂ : MeasurableSet s)
    (hs₃ : μ (frontier s) = 0) :
    Tendsto (fun n : ℕ ↦ (Nat.card (s ∩ (n : ℝ)⁻¹ • L : Set E) : ℝ) / n ^ finrank ℝ E)
      atTop (𝓝 (μ.real s / ZLattice.covolume L μ)) := by
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) = finrank ℝ E := by
    rw [← finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ L]
  have hfr : frontier (((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L).equivFun '' s) =
      ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L).equivFun '' frontier s :=
    (((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L).equivFunL.toHomeomorph.image_frontier
      s).symm
  have hlim : volume.real (((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L).equivFun '' s) =
      μ.real s / ZLattice.covolume L μ := by
    rw [measureReal_def, volume_image_equivFun L μ, ENNReal.toReal_div,
      ENNReal.toReal_ofReal (ZLattice.covolume_pos L μ).le, measureReal_def]
  have key := ZLattice.covolume.tendsto_card_div_pow'' (Module.Free.chooseBasis ℤ L) hs₁ hs₂
    (by rw [hfr, volume_image_equivFun L μ, hs₃, ENNReal.zero_div])
  rw [hlim, hcard] at key
  exact key
end Formalism.HermitianLattices.Ext.L3.BallA
