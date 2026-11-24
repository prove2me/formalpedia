-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx2.PolyFam.add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:39:35.72034+00:00
-- url     : https://prove2.me/submissions/f326de31-4903-4188-a5c9-5a965997dbe2

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_smooth_add

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
theorem _root_.solution {N : ℕ} {h h' : ℂ → Mx k r → E} (H : PolyFam k r i D N h) (H' : PolyFam k r i D N h') :
    PolyFam k r i D N (fun Y x => h Y x + h' Y x) := by
  obtain ⟨c, hc, he⟩ := H
  obtain ⟨c', hc', he'⟩ := H'
  refine ⟨fun j x => c j x + c' j x, fun j => smooth_add (hc j) (hc' j), fun Y x hx => ?_⟩
  try dsimp only
  rw [he Y x hx, he' Y x hx, ← Finset.sum_add_distrib]
  simp only [smul_add]
end PolyFam
end Formalism.FourierDecayAlt.P.Qx2
