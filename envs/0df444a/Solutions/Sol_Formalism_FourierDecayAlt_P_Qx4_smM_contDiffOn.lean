-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx4.smM_contDiffOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:45:22.351031+00:00
-- url     : https://prove2.me/submissions/535be9f4-4569-41ff-b812-199c79cdd2f7

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenAdelicUnipotentTimesIntegralOutsideSet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
local notation "⟪" u ", " v "⟫" => herm (Hpk k r) u v
variable {l : Fin r}
local notation "𝐞" => bvec (eI k r l)
local notation "𝐬" => bvec (esI k r l)
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {m : ℕ}
namespace Formalism.FourierDecayAlt.P.Qx4
theorem _root_.solution {f : X → Matrix (Fin m) (Fin m) ℂ} {s : Set X} (hf : SmM f s) : ContDiffOn ℝ ∞ f s := by
  have h : ContDiffOn ℝ ∞ (fun x => (f x : Fin m → Fin m → ℂ)) s :=
    contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => hf i j
  exact h
end Formalism.FourierDecayAlt.P.Qx4
