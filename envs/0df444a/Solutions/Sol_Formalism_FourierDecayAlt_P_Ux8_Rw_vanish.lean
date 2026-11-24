-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux8.Rw_vanish
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:32:30.65113+00:00
-- url     : https://prove2.me/submissions/7a60d4b4-3941-4805-9c91-5b7edc14bbe0

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SeminormCompletion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
namespace Formalism.FourierDecayAlt.P.Ux8
section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (p : Seminorm ℂ V)
end
section supp
open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
section pi
variable {k r : ℕ} {ι E : Type} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℂ E]
end pi
private theorem continuous_exp_real_smul_matrix {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    Continuous fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) := by
  letI : SeminormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpSemiNormedRing
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  have hcs : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℂ _
  exact (@NormedSpace.exp_continuous _ _ _ hcs).comp (Complex.continuous_ofReal.smul continuous_const)
end supp
end Formalism.FourierDecayAlt.P.Ux8
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P
end
end

set_option autoImplicit false
open Matrix MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux8
open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P.Ux8
theorem _root_.solution {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {O : Set (B.Mat k r)} (hO : IsOpen O)
    {f : B.Mat k r → E} (h : ∀ g ∈ O, f g = 0) (w : List (B.Mat k r)) : ∀ g ∈ O, B.Rw w f g = 0 := by
  induction w with
  | nil => exact h
  | cons X w ih =>
    intro g hg
    have hc : ContinuousAt (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) 0 :=
      (continuous_const.mul (continuous_exp_real_smul_matrix X)).continuousAt
    have hmem : (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) ⁻¹' O ∈ nhds (0 : ℝ) :=
      hc.preimage_mem_nhds (by simpa using hO.mem_nhds hg)
    have hev : (fun t : ℝ => B.Rw w f (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[nhds 0] fun _ => 0 := by
      filter_upwards [hmem] with t ht
      exact ih _ ht
    show deriv (fun t : ℝ => B.Rw w f (g * NormedSpace.exp ((t : ℂ) • X))) 0 = 0
    rw [hev.deriv_eq]
    simp
end Formalism.FourierDecayAlt.P.Ux8
