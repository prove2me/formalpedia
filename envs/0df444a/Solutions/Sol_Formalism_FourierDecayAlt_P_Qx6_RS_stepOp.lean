-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.RS_stepOp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:25:58.230842+00:00
-- url     : https://prove2.me/submissions/6e3eda72-0a56-4e69-9844-f0d0f066872f

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_preserves_transfer_letter
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_preserves_transfer_letter_star
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_preserves_operator_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_RS_lin
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_RS_op
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_RS_QL
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
namespace Formalism.FourierDecayAlt.P.Qx6
theorem _root_.solution (hFO : FamOps) (hTP : TPreservesFF) (hLL : TLinLoc) (hz : inWb k r z) (hz' : inWb k r z')
    (l : Fin r) {Dc Dc₀ : (Fin r → ℂ) → Set (Mx k r)} {S : Set (Fin r → ℂ)} (hS : SData z z' l.succ Dc Dc₀ S)
    (hSl : ∀ c ∈ S, ∀ᶠ s in 𝓝 (c l), Function.update c l s ∈ S) (Y : ℂ) (a b : Fin 2) :
    Pres2 (RS z z' π π' l.succ Dc Dc₀ S) (stepOp z z' l Y a b) (stepOp z z' l Y a b) := by
  have hl : LinRel (RS z z' π π' l.succ Dc Dc₀ S) := RS_lin
  have h1 : ∀ a b, Pres2 (RS z z' π π' l.succ Dc Dc₀ S) (TLs k l Y a b) (TLs k l Y a b) :=
    preserves_transfer_letter_star hl l (RS_op hFO hz hz' hS l hSl) Y
  have h2 : ∀ a b, Pres2 (RS z z' π π' l.succ Dc Dc₀ S) (TL k l Y a b) (TL k l Y a b) :=
    preserves_transfer_letter hl l (RS_op hFO hz hz' hS l hSl) Y
  have h3 : ∀ a b, Pres2 (RS z z' π π' l.succ Dc Dc₀ S) (QL k r z z' l.succ Y a b) (QL k r z z' l.succ Y a b) :=
    RS_QL hTP hLL hz hz' hS Y
  have h4 : ∀ a b, Pres2 (RS z z' π π' l.succ Dc Dc₀ S) (oMul (QL k r z z' l.succ Y) (TL k l Y) a b)
      (oMul (QL k r z z' l.succ Y) (TL k l Y) a b) :=
    preserves_operator_mul (M := QL k r z z' l.succ Y) (M' := QL k r z z' l.succ Y) (N := TL k l Y) (N' := TL k l Y) hl h3 h2
  exact preserves_operator_mul (M := TLs k l Y) (M' := TLs k l Y) (N := oMul (QL k r z z' l.succ Y) (TL k l Y))
    (N' := oMul (QL k r z z' l.succ Y) (TL k l Y)) hl h1 h4 a b
end Formalism.FourierDecayAlt.P.Qx6
