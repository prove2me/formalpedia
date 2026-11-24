-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdmissibleLieWords.ubl_epart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:58:27.292171+00:00
-- url     : https://prove2.me/submissions/9f3fbac4-1b07-4ef8-bac3-8375415ba8e9

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DminStarPd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutoffIteratedFDerivBounded
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_ubl_app
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_ubl_clm
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_ubl_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_ubl_fib


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
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords
theorem _root_.solution (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, C6.FibBound D (fib j)) {ε : ℝ} (hε : 0 < ε) {S : Set (Mat k r)}
    (hS : ∀ g ∈ S, g ∈ GV k r ∧ ε ≤ Gf k r D.z D.z' g) (n : ℕ) :
    ∀ es : List (Fin nf × List (Mat k r)), (∀ e ∈ es, ∀ X ∈ e.2, inLie k r X) →
      UBL (C6.Epart fib es) S n (3 * (r + 1) * (es.map fun e => e.2.length).sum) (3 * (r + 1)) := by
  have hSG : S ⊆ GV k r := fun g hg => (hS g hg).1
  intro es
  induction es with
  | nil =>
    intro _
    have e0 : C6.Epart fib ([] : List (Fin nf × List (Mat k r))) = fun _ => 1 := by
      funext g
      simp [C6.Epart]
    rw [e0]
    simpa using ubl_const (1 : C6.EndH Wp Wq) hSG n (3 * (r + 1))
  | cons e es ih =>
    intro hes
    have hA := ubl_fib D (fib e.1) (hfib e.1) hε hS e.2 (hes e (by simp)) n
    have hB := ih (fun e' he' => hes e' (List.mem_cons_of_mem _ he'))
    have hL := ubl_clm ((ContinuousLinearMap.mul ℂ (C6.EndH Wp Wq)).restrictScalars ℝ) hSG hA
    have hAB := ubl_app hSG hL hB
    have e1 : C6.Epart fib (e :: es) =
        fun g => ((ContinuousLinearMap.mul ℂ (C6.EndH Wp Wq)).restrictScalars ℝ
          (Rw e.2 (fib e.1) g)) (C6.Epart fib es g) := by
      funext g
      simp [C6.Epart]
    rw [e1]
    convert hAB using 2
    simp only [List.map_cons, List.sum_cons]
    ring
end Formalism.FourierDecayAlt.P.AdmissibleLieWords
