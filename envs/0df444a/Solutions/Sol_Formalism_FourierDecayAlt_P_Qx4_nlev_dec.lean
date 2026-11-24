-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx4.nlev_dec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:18:16.5845+00:00
-- url     : https://prove2.me/submissions/e3d56dc2-40d2-4cfc-8cb2-5e9e5d3cd07c

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_uh_inv_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_up_nset
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_stab_dec
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_nlev_e
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_mem_n_inv
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_mem_n_mul


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
theorem _root_.solution {n : Mx k r} (hn : n ∈ Nlev k r l.castSucc) :
    ∃ u ∈ UP k r l, ∃ n₁ ∈ Nlev k r l.succ, n = u * n₁ := by
  obtain ⟨u, hu, g₁, hg₁, h⟩ := stab_dec hn.2 (nlev_e hn)
  refine ⟨u, hu, g₁, ⟨?_, hg₁⟩, h⟩
  have : g₁ = u⁻¹ * n := by rw [h, ← Matrix.mul_assoc, uh_inv_mul hu.1.1, Matrix.one_mul]
  rw [this]
  exact WeylGroupFacts.mem_n_mul (WeylGroupFacts.mem_n_inv (up_nset hu)) hn.1
end Formalism.FourierDecayAlt.P.Qx4
