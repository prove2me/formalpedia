-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx2.polyFam_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:24:56.010711+00:00
-- url     : https://prove2.me/submissions/8f9215fa-54b4-4a8b-9e23-9341bf79e671

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_smooth_zero

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
theorem _root_.solution {f : Mx k r → E} (hf : SmoothLev k r i D f) (N : ℕ) :
    PolyFam k r i D (N + 1) (fun Y x => Y ^ N • f x) := by
  refine ⟨fun j x => if j = N then f x else 0, fun j => ?_, fun Y x hx => ?_⟩
  · by_cases hj : j = N
    · simp only [if_pos hj]
      exact hf
    · simp only [if_neg hj]
      exact smooth_zero
  · simp [smul_ite, Finset.sum_ite_eq', Finset.sum_ite_eq]
end Formalism.FourierDecayAlt.P.Qx2
