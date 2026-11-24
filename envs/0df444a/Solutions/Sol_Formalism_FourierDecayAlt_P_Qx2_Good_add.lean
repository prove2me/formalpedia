-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx2.Good.add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:39:35.076875+00:00
-- url     : https://prove2.me/submissions/7abd93f0-86c6-44d9-964b-90dd311db8db

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
namespace Good
theorem _root_.solution {T S : (Mx k r → E) → Mx k r → E} (hT : Good k r i D T) (hS : Good k r i D S) :
    Good k r i D (fun f x => T f x + S f x) := by
  refine ⟨fun f hf => smooth_add (hT.sm f hf) (hS.sm f hf), fun f f₂ h x hx => ?_,
    fun f f₂ s hf hf₂ x hx => ?_⟩
  · try dsimp only
    rw [hT.loc f f₂ h x hx, hS.loc f f₂ h x hx]
  · try dsimp only
    rw [hT.lin f f₂ s hf hf₂ x hx, hS.lin f f₂ s hf hf₂ x hx, smul_add]
    abel
end Good
end Formalism.FourierDecayAlt.P.Qx2
