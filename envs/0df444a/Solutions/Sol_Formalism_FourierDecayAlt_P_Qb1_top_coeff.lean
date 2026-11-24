-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qb1.top_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:29:14.972726+00:00
-- url     : https://prove2.me/submissions/a58771dd-2cef-4623-8518-3418b1ee3447

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CasimirEigenvalueCoefficients
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qb1_rdV_coeff
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qb1_lie1
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qb1_lie2

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
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.Qb1
variable {k r : ℕ} {Vs : Type} [NormedAddCommGroup Vs] [NormedSpace ℂ Vs]
variable {σ : Mx k r → (Vs →L[ℂ] Vs)}
namespace Formalism.FourierDecayAlt.P.Qb1
theorem _root_.solution (hrep : IsCRepOn (UH (Hpk k r)) σ) {w : Vs} (hw : SV σ w) (ℓ : Vs →L[ℂ] ℂ) (c : ℂ)
    (a b : Fin (2 * r + k + 1)) {g : Mx k r} (hg : g ∈ GV k r) :
    QuantumDeterminants.Top (EH k r) c a b (fun x => ℓ (σ x w)) g = ℓ (σ g (stepV σ c a b w)) := by
  unfold QuantumDeterminants.Top stepV EcRep
  simp only [EH, EabH]
  rw [rdV_coeff hrep hw (lie1 _) ℓ hg, rdV_coeff hrep hw (lie2 _) ℓ hg]
  split_ifs <;> simp [map_add, map_smul]
end Formalism.FourierDecayAlt.P.Qb1
