-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.Dx_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:53:42.934037+00:00
-- url     : https://prove2.me/submissions/10d393de-232a-4a8a-97fe-6feccc4c854b

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity

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
theorem _root_.solution (s : ℝ) (b : Bool) (X : Mat k r) (f : Mat k r → E) :
    Dx (b, (s : ℂ) • X) f = fun g => (s : ℂ) • Dx (b, X) f g := by
  funext g
  rcases b with _ | _
  · show deriv (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • (s : ℂ) • X))) 0 =
      (s : ℂ) • deriv (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) 0
    have h := deriv_comp_mul_left s (fun u : ℝ => f (g * NormedSpace.exp ((u : ℂ) • X))) 0
    simp only [mul_zero] at h
    rw [← Complex.coe_smul] at h
    rw [← h]
    congr 1
    funext t
    simp only [smul_smul, Complex.ofReal_mul, mul_comm (t : ℂ)]
  · show deriv (fun t : ℝ => f (NormedSpace.exp (-((t : ℂ) • (s : ℂ) • X)) * g)) 0 =
      (s : ℂ) • deriv (fun t : ℝ => f (NormedSpace.exp (-((t : ℂ) • X)) * g)) 0
    have h := deriv_comp_mul_left s (fun u : ℝ => f (NormedSpace.exp (-((u : ℂ) • X)) * g)) 0
    simp only [mul_zero] at h
    rw [← Complex.coe_smul] at h
    rw [← h]
    congr 1
    funext t
    simp only [smul_smul, Complex.ofReal_mul, mul_comm (t : ℂ)]
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
