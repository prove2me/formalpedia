-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.casimir_eigenvalue_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:04:59.101812+00:00
-- url     : https://prove2.me/submissions/fa31cf49-10ac-42cb-ae20-69e84b7f63f1

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CasimirEigenvalueCoefficients
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qb1_qminor_coeff
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qb1_qmF_reindex
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr


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
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Q.EigenCoeff := by
  intro Vs _ _ k r σ v lam hrep hsm hC ℓ Y g hg
  have hw : Qb1.SV σ v := by
    intro g₀ hg₀
    have hmem : ∀ x ∈ GV k r, x ∈ Glev k r 0 := fun x hx =>
      ⟨hx, fun a ha => absurd ha (by simp)⟩
    obtain ⟨U, F, a, b, c, d⟩ := hsm g₀ ⟨hmem g₀ hg₀, trivial⟩
    exact ⟨U, F, a, b, c, fun x hx hxG => d x hx (hmem x hxG)⟩
  unfold CV capL
  rw [Qb1.qminor_coeff hrep ℓ _ _ _ hw hg,
    Qb1.qmF_reindex _ _ _ (mdim k r 0) (by simp [mdim]) (posL k r 0) (fun j => by simp [posL]), hC,
    map_smul, map_smul]
  congr 1
  refine Finset.prod_congr rfl fun s _ => ?_
  simp only [uC, mdim, Fin.val_zero, Nat.sub_zero]
  push_cast
  ring
end Formalism.FourierDecayAlt.P
