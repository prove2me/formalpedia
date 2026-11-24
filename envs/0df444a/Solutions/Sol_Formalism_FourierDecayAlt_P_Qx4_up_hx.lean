-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx4.up_hx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:04:10.327447+00:00
-- url     : https://prove2.me/submissions/0f26cdde-5a08-4127-9394-a21254a4d970

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_hx_up
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_hx_es
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_isX_of_glev
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_up_unique

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
namespace Formalism.FourierDecayAlt.P.Qx4
theorem _root_.solution {u : Mx k r} (hu : u ∈ UP k r l) : hx k r l (u *ᵥ 𝐬) = u :=
  up_unique (hx_up (isX_of_glev hu.1 hu.2.1)) hu (hx_es (isX_of_glev hu.1 hu.2.1))
end Formalism.FourierDecayAlt.P.Qx4
