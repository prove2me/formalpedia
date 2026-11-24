-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.Rw_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:25:54.904975+00:00
-- url     : https://prove2.me/submissions/c9c1b446-cb63-42a4-b80f-159becfff794

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Dx_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_nrm_back
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Dx_scale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BetaSesquilinearity
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
open scoped ContDiff
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
variable {O UU : Set (Mat k r)} {a : Mat k r → (E →L[ℂ] E')} {Φ : Mat k r → E}
namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity
theorem _root_.solution (v : List (Mat k r)) (f : Mat k r → E) :
    Rw v f = fun g => (((v.map nz).prod : ℝ) : ℂ) • Rw (v.map nrm) f g := by
  induction v with
  | nil => funext g; simp [Rw]
  | cons X v ih =>
    funext g
    have h1 : RdV X (Rw v f) = Dx (false, ((nz X : ℝ) : ℂ) • nrm X) (Rw v f) := by
      rw [nrm_back]; rfl
    show RdV X (Rw v f) g = _
    rw [h1, Dx_scale, ih, Dx_smul]
    show ((nz X : ℝ) : ℂ) • ((((v.map nz).prod : ℝ) : ℂ) • Dx (false, nrm X) (Rw (v.map nrm) f) g) = _
    rw [smul_smul, ← Complex.ofReal_mul]
    simp only [List.map_cons, List.prod_cons]
    rfl
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
