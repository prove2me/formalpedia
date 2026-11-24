-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux10.meas_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:53:59.803904+00:00
-- url     : https://prove2.me/submissions/0489b0de-b2fa-4c52-830b-a69cffad02ea

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyTransformPreservesForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_aesm_deriv
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_ckOn_diff
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_ckOn_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_cv_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_smooth_on_of_word_derivatives


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
open MeasureTheory Filter Topology
open Matrix Filter Topology
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux10
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.Ux10
theorem _root_.solution {h : α → Mat k r → E} {mm : ℕ} (hh : ∀ ξ, CkOn ((mm : ℕ) : ℕ∞) (GV k r) (h ξ))
    (hm : ∀ g ∈ GV k r, AEStronglyMeasurable (fun ξ => h ξ g) μ) :
    ∀ w : List (Bool × Mat k r), AllLie w → w.length ≤ mm → ∀ g ∈ GV k r,
      AEStronglyMeasurable (fun ξ => W w (h ξ) g) μ := by
  intro w
  induction w with
  | nil => intro _ _ g hg; exact hm g hg
  | cons x w ih =>
    intro hw hl g hg
    have hw' : AllLie w := fun y hy => hw y (List.mem_cons_of_mem _ hy)
    have hx : inLie k r x.2 := hw x List.mem_cons_self
    have hl' : w.length + 1 ≤ mm := by simpa using hl
    have hC : ∀ ξ, CkOn ((1 : ℕ) : ℕ∞) (GV k r) (W w (h ξ)) := fun ξ =>
      smooth_on_of_word_derivatives w hw' 1 (ckOn_mono (by omega) (hh ξ))
    refine aesm_deriv (G := fun ξ t => W w (h ξ) (cv x.1 x.2 t g)) (fun ξ => ?_)
      (Eventually.of_forall fun t => ih hw' (by omega) _ (cv_mem hx hg t))
    exact (ckOn_diff 0 x.1 (hC ξ) hx hg).hasDerivAt
end Formalism.FourierDecayAlt.P.Ux10
