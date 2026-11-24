-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx2.PolyFam.smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:35:06.57934+00:00
-- url     : https://prove2.me/submissions/45662974-c419-4f16-856c-bd5d181e58eb

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_smooth_smul

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
theorem _root_.solution {N : ℕ} {h : ℂ → Mx k r → E} (H : PolyFam k r i D N h) (s : ℂ) :
    PolyFam k r i D N (fun Y x => s • h Y x) := by
  obtain ⟨c, hc, he⟩ := H
  refine ⟨fun j x => s • c j x, fun j => smooth_smul (hc j) s, fun Y x hx => ?_⟩
  try dsimp only
  rw [he Y x hx, Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _
end PolyFam
end Formalism.FourierDecayAlt.P.Qx2
