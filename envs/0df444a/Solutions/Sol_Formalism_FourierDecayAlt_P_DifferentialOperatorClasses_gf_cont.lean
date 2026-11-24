-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DifferentialOperatorClasses.gf_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:43:53.195617+00:00
-- url     : https://prove2.me/submissions/92766a4b-db2e-49c0-8562-474270b58b70

import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HomogeneityNaturalDegree
import Mathlib.Topology.Algebra.MvPolynomial
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellVanishingOfCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_gram_function_polynomial


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Filter Topology
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DifferentialOperatorClasses
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.DifferentialOperatorClasses
theorem _root_.solution (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Continuous fun g : B.Mat k r => Gf k r z z' g := by
  obtain ⟨q, _, hq⟩ := P.gram_function_polynomial k r z z'
  have h1 : Continuous fun g : B.Mat k r => ((Gf k r z z' g : ℝ) : ℂ) := by
    have e : (fun g : B.Mat k r => ((Gf k r z z' g : ℝ) : ℂ)) =
        fun g => MvPolynomial.eval (Sum.elim (fun x => g x.1 x.2) (fun x => star (g x.1 x.2))) q := funext hq
    rw [e]
    refine (MvPolynomial.continuous_eval q).comp ?_
    refine continuous_pi fun i => ?_
    rcases i with ⟨a, b⟩ | ⟨a, b⟩
    · simp only [Sum.elim_inl]; exact continuous_id.matrix_elem a b
    · simp only [Sum.elim_inr]; exact continuous_star.comp (continuous_id.matrix_elem a b)
  have := Complex.continuous_re.comp h1
  refine this.congr fun g => ?_
  simp
end Formalism.FourierDecayAlt.P.DifferentialOperatorClasses
