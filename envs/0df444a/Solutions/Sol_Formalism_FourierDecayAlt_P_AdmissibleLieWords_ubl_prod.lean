-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdmissibleLieWords.ubl_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:19:56.068853+00:00
-- url     : https://prove2.me/submissions/c915ffed-5977-43b0-b0b3-23ad68979f70

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleWordLengthLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ZinvBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_ubl_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_ubl_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Set
open scoped ComplexConjugate ContDiff Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.AdmissibleLieWords
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords
theorem _root_.solution {ι : Type*} [DecidableEq ι] {S : Set (Mat k r)} (hSG : S ⊆ GV k r) {n γ : ℕ} (s : Finset ι)
    (f : ι → Mat k r → ℂ) (h : ∀ i ∈ s, UBL (f i) S n 0 γ) : UBL (fun g => ∏ i ∈ s, f i g) S n 0 γ := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact ubl_const 1 hSG n γ
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    have h1 := ubl_mul hSG (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    simpa using h1
end Formalism.FourierDecayAlt.P.AdmissibleLieWords
