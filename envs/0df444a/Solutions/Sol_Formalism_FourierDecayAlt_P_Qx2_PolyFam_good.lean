-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx2.PolyFam.good
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:40:54.752065+00:00
-- url     : https://prove2.me/submissions/3d903fc6-59c4-41f4-bcce-93c98850638b

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_map_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.Qx2
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
namespace Formalism.FourierDecayAlt.P.Qx2
namespace PolyFam
theorem _root_.solution {N : ℕ} {h : ℂ → Mx k r → E} (H : PolyFam k r i D N h)
    {T : (Mx k r → E) → Mx k r → E} (hT : Good k r i D T) : PolyFam k r i D N (fun Y => T (h Y)) := by
  obtain ⟨c, hc, he⟩ := H
  refine ⟨fun j => T (c j), fun j => hT.sm _ (hc j), fun Y x hx => ?_⟩
  try dsimp only
  rw [hT.loc (h Y) (fun y => ∑ j ∈ Finset.range N, Y ^ j • c j y) (fun y hy => he Y y hy) x hx]
  exact hT.map_sum (fun j => Y ^ j) hc hx N
end PolyFam
end Formalism.FourierDecayAlt.P.Qx2
