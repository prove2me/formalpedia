-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MinorPolynomials.ckOn_Rw_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:31:20.44215+00:00
-- url     : https://prove2.me/submissions/58d32403-086f-4b2b-9cab-da71371d8002

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasDerivAtCvs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasDerivAtEpart
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_MinorPolynomials_Rw_cons__735539f794a9
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CkOn_Dx


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial
open scoped ComplexConjugate ContDiff Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MinorPolynomials
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.MinorPolynomials
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {UU : Set (Mat k r)} {f : Mat k r → E}
    (hf : CkOn ⊤ UU f) {w : List (Mat k r)} (hw : ∀ X ∈ w, inLie k r X) : CkOn ⊤ UU (Rw w f) := by
  induction w with
  | nil => exact hf
  | cons X w ih =>
    rw [Rw_cons']
    have h := ih (fun Y hY => hw Y (List.mem_cons_of_mem _ hY))
    exact CkOn_Dx (x := (false, X)) (hw X (by simp)) (by simpa using h)
end Formalism.FourierDecayAlt.P.MinorPolynomials
