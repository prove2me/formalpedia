-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x5.covolume_scal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:34:20.438199+00:00
-- url     : https://prove2.me/submissions/9a1e0c5f-e27f-4e8a-876d-181c23b44102

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S6x5
open Module MeasureTheory
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
namespace Formalism.FourierDecayAlt.P.S6x5
theorem _root_.solution (μ : Measure V) [μ.IsAddHaarMeasure] (L : Submodule ℤ V)
    [DiscreteTopology L] [IsZLattice ℝ L] (c : ℝ) (hc : c ≠ 0) :
    ZLattice.covolume (ZLattice.comap ℝ L (scalInv V c hc).toLinearMap) μ =
      |c| ^ finrank ℝ V * ZLattice.covolume L μ := by
  classical
  have : Module.Free ℤ L := ZLattice.module_free ℝ L
  have : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  let b := Free.chooseBasis ℤ L
  rw [ZLattice.covolume_eq_det_mul_measureReal _ μ
      (b.ofZLatticeComap ℝ L (scalInv V c hc).toLinearEquiv) (b.ofZLatticeBasis ℝ),
    ZLattice.covolume_eq_det_mul_measureReal L μ b (b.ofZLatticeBasis ℝ), ← mul_assoc]
  congr 1
  have h1 : ((↑) ∘ (b.ofZLatticeComap ℝ L (scalInv V c hc).toLinearEquiv) : _ → V)
      = fun i => c • ((↑) ∘ b : _ → V) i := by
    ext i
    rw [Function.comp_apply, Basis.ofZLatticeComap_apply]
    rfl
  have h2 := (b.ofZLatticeBasis ℝ).det.toMultilinearMap.map_smul_univ (fun _ => c)
    ((↑) ∘ b : _ → V)
  rw [h1]
  erw [h2]
  simp only [Finset.prod_const, Finset.card_univ, smul_eq_mul, abs_mul, abs_pow]
  rw [← finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ]
  rfl
end Formalism.FourierDecayAlt.P.S6x5
