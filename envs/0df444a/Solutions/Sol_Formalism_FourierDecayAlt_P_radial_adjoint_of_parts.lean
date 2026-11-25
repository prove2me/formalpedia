-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.radial_adjoint_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:51:19.01555+00:00
-- url     : https://prove2.me/submissions/092778dd-f06c-4018-9d75-6de34f3d0787

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositiveOrbitOpen
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellOrbitSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RadialAdjointOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxG_adj_local
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxG_betaBig_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveOrbitOpen_omPlus_open
import Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveOrbitOpen_op_local


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.P.JFxG.RadAdjOfParts := by
  intro hE hJ hB k r Wp Wq _ _ _ _ _ _ D Θ f f' K hI hS hC hf hf' hEf hEf' hK hKQ hvan
  obtain ⟨F, hF, hFc, hFf⟩ := hE k r Wp Wq D f K hf hEf hK hKQ fun q hq hqK => (hvan q hq hqK).1
  obtain ⟨F', hF', hF'c, hF'f⟩ := hE k r Wp Wq D f' K hf' hEf' hK hKQ fun q hq hqK => (hvan q hq hqK).2
  have hB' := hB k r Wp Wq D Θ F F' hI hS hC hF hF' hFc hF'c
  have hO := PositiveOrbitOpen.omPlus_open (k := k) (r := r) D.z D.z'
  have p1 : ∀ g ∈ Om k r D.z D.z', hsVec (opApply Θ f g) = hsVec (JF D (opApply Θ F) g) := by
    intro g hg
    rw [(hJ k r Wp Wq D Θ F hS hC hF hFc g hg).1,
      PositiveOrbitOpen.op_local Θ hO (fun x hx hxG => (hFf x ⟨hxG, hx⟩).symm) g hg.2 hg.1]
  have p2 : ∀ g ∈ Om k r D.z D.z', hsVec (opAdj Θ f' g) = hsVec (JF D (opAdj Θ F') g) := by
    intro g hg
    rw [(hJ k r Wp Wq D Θ F' hS hC hF' hF'c g hg).2,
      JFxG.adj_local Θ hO (fun x hx hxG => (hF'f x ⟨hxG, hx⟩).symm) g hg.2 hg.1]
  have p3 : ∀ g ∈ Om k r D.z D.z', hsVec (f g) = hsVec (JF D F g) := fun g hg => by rw [hFf g hg]
  have p4 : ∀ g ∈ Om k r D.z D.z', hsVec (f' g) = hsVec (JF D F' g) := fun g hg => by rw [hF'f g hg]
  rw [JFxG.betaBig_congr D p1 p4, JFxG.betaBig_congr D p3 p2]
  exact hB'
end Formalism.FourierDecayAlt.P
