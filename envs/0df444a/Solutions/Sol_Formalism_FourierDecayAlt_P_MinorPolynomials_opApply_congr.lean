-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MinorPolynomials.opApply_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:23:21.765813+00:00
-- url     : https://prove2.me/submissions/470ac282-2779-4a13-94c6-046ca5cf2729

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ListMapSumApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ComposeDifferentialOperators
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_crv_ev
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_crv_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix MvPolynomial Set
open scoped ComplexConjugate ContDiff Topology
noncomputable section
namespace Formalism.FourierDecayAlt.P.MinorPolynomials
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
private lemma rw_congr_on_domL {O : Set (Mat k r)} (hO : IsOpen O) {H H' : Mat k r → (Wq →L[ℂ] Wp)}
    (h : ∀ g ∈ GV k r, g ∈ O → H g = H' g) :
    ∀ w : List (Mat k r), (∀ X ∈ w, inLie k r X) → ∀ g ∈ GV k r, g ∈ O → Rw w H g = Rw w H' g := by
  intro w
  induction w with
  | nil => intro _ g hg hgO; exact h g hg hgO
  | cons X w ih =>
    intro hw g hg hgO
    have hX : inLie k r X := hw X (by simp)
    have ih' := ih (fun Y hY => hw Y (by simp [hY]))
    show RdV X (Rw w H) g = RdV X (Rw w H') g
    show deriv (fun t : ℝ => Rw w H (g * NormedSpace.exp ((t : ℂ) • X))) 0 =
      deriv (fun t : ℝ => Rw w H' (g * NormedSpace.exp ((t : ℂ) • X))) 0
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [crv_ev (x := (false, X)) hO hgO] with t ht
    have hm := crv_mem (x := (false, X)) hX hg t
    simp only [crv, Bool.false_eq_true, if_false] at ht hm
    exact ih' _ hm ht
end Formalism.FourierDecayAlt.P.MinorPolynomials
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.P.MinorPolynomials
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end Formalism.FourierDecayAlt.P
end
end

set_option autoImplicit false
open Matrix MvPolynomial Set
open scoped ComplexConjugate ContDiff Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MinorPolynomials
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.MinorPolynomials
theorem _root_.solution (Θ : DiffOp k r Wp Wq) {O : Set (Mat k r)} (hO : IsOpen O) {H H' : Mat k r → (Wq →L[ℂ] Wp)}
    (h : ∀ g ∈ GV k r, g ∈ O → H g = H' g) {g : Mat k r} (hg : g ∈ GV k r) (hgO : g ∈ O) :
    opApply Θ H g = opApply Θ H' g := by
  unfold opApply
  congr 1
  refine List.map_congr_left (fun T _ => ?_)
  rw [rw_congr_on_domL hO h T.word T.word_lie g hg hgO]
end Formalism.FourierDecayAlt.P.MinorPolynomials
