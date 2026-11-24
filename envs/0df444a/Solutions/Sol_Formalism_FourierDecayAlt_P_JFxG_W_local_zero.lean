-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxG.W_local_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:24:46.508699+00:00
-- url     : https://prove2.me/submissions/3cc766e5-6562-45f8-b870-2a8bca884db6

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaConjOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactSupportFiniteClass
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_W_cons
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_cv_hasDerivAt
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_cv_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_cv_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxG
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.JFxG
theorem _root_.solution {F : Mat k r → E} {V : Set (Mat k r)} (hV : IsOpen V) (h : ∀ x ∈ V, x ∈ GV k r → F x = 0) :
    ∀ (w : List (Bool × Mat k r)), AllLie w → ∀ x ∈ V, x ∈ GV k r → W w F x = 0 := by
  intro w
  induction w with
  | nil => intro _ x hx hxG; exact h x hx hxG
  | cons a w ih =>
    intro hw x hx hxG
    rw [W_cons]
    have hw' : AllLie w := fun y hy => hw y (List.mem_cons_of_mem _ hy)
    have hc := (cv_hasDerivAt a.1 a.2 x).continuousAt
    have hmem : ∀ᶠ t : ℝ in 𝓝 0, cv a.1 a.2 t x ∈ V :=
      hc.preimage_mem_nhds (by rw [cv_zero]; exact hV.mem_nhds hx)
    have he : (fun t : ℝ => W w F (cv a.1 a.2 t x)) =ᶠ[𝓝 0] fun _ => (0 : E) := by
      filter_upwards [hmem] with t ht
      exact ih hw' _ ht (cv_mem (hw a List.mem_cons_self) hxG t)
    show deriv (fun t : ℝ => W w F (cv a.1 a.2 t x)) 0 = 0
    rw [he.deriv_eq, deriv_const]
end Formalism.FourierDecayAlt.P.JFxG
