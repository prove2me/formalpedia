-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MinorPolynomials.mem_steps_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:23:20.98281+00:00
-- url     : https://prove2.me/submissions/938491c8-2ced-4dfc-9af6-297db1a3db13

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ListMapSumApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ComposeDifferentialOperators
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_mem_steps_full
import Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_steps_append


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution (D : RealPlaceData k r Wp Wq) {nf : ℕ} {e : CT k r nf × List (Mat k r)} {Lf : FS k r nf}
    (he : e ∈ Lf) : ∀ w : List (Mat k r), (e.1, w ++ e.2) ∈ steps D w Lf := by
  intro w
  obtain ⟨s, t, rfl⟩ := List.append_of_mem he
  rw [steps_append, List.mem_append]
  right
  rw [show e :: t = [e] ++ t from rfl, steps_append, List.mem_append]
  exact Or.inl (mem_steps_full D e w)
end Formalism.FourierDecayAlt.P.MinorPolynomials
