-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxG.adj_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:07:35.573856+00:00
-- url     : https://prove2.me/submissions/ec29b4d4-e127-4b9d-9024-cf0e4bc84b9b

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositiveOrbitOpen
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellOrbitSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RadialAdjointOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveOrbitOpen_rw_local


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxG
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.JFxG
theorem _root_.solution (Θ : DiffOp k r Wp Wq) {f₁ f₂ : Mat k r → (Wq →L[ℂ] Wp)} {V : Set (Mat k r)} (hV : IsOpen V)
    (h : ∀ x ∈ V, x ∈ GV k r → f₁ x = f₂ x) : ∀ x ∈ V, x ∈ GV k r → opAdj Θ f₁ x = opAdj Θ f₂ x := by
  intro x hx hxG
  unfold opAdj
  congr 1
  refine List.map_congr_left fun T _ => ?_
  rw [PositiveOrbitOpen.rw_local (f₁ := fun y => T.coefAdj y (f₁ y)) (f₂ := fun y => T.coefAdj y (f₂ y)) hV
    (fun y hy hyG => by simp only [h y hy hyG]) T.word.reverse
    (fun X hX => T.word_lie X (List.mem_reverse.1 hX)) x hx hxG]
end Formalism.FourierDecayAlt.P.JFxG
