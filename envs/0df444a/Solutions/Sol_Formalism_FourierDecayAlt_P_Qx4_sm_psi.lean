-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx4.sm_psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:51:42.588128+00:00
-- url     : https://prove2.me/submissions/ab74bac2-a222-4fa6-8381-b3fa8f4a1221

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_smV_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_smV_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
local notation "⟪" u ", " v "⟫" => herm (Hpk k r) u v
variable {l : Fin r}
local notation "𝐞" => bvec (eI k r l)
local notation "𝐬" => bvec (esI k r l)
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
namespace Formalism.FourierDecayAlt.P.Qx4
theorem _root_.solution (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) {f : X → Mx k r} {s : Set X} (hf : SmM f s) :
    ContDiffOn ℝ ∞ (fun x => psi k r z c (f x)) s := by
  have h1 : ContDiffOn ℝ ∞ (fun x => ell k r z (f x)) s := by
    unfold ell
    apply ContDiffOn.sum
    intro a _
    split_ifs
    · exact hf _ _
    · exact smV_mulVec hf (smV_const _ s) _
  have h2 : ContDiffOn ℝ ∞ (fun x => c * ell k r z (f x)) s := contDiffOn_const.mul h1
  have h3 : ContDiffOn ℝ ∞ (fun x => (c * ell k r z (f x)).re) s := Complex.reCLM.contDiff.comp_contDiffOn h2
  have h4 : ContDiffOn ℝ ∞ (fun x => (((c * ell k r z (f x)).re : ℝ) : ℂ)) s :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn h3
  unfold psi
  exact (contDiffOn_const.mul h4).cexp
end Formalism.FourierDecayAlt.P.Qx4
