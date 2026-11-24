-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx4.mem_cell_domain_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:14:43.171624+00:00
-- url     : https://prove2.me/submissions/9666bc9b-0c37-4928-a194-704bae678602

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_Dec_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_dec_exists
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_Dec_rho_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_Dec_cell_decomposition_mem

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
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
namespace Formalism.FourierDecayAlt.P.Qx4
theorem _root_.solution {D₁ : Set (Mx k r)} {g : Mx k r} :
    g ∈ Glev k r l.castSucc ∩ D0 k r l D₁ ↔ ∃ c u g₁ u', Dec k r l g c u g₁ u' ∧ g₁ ∈ D₁ := by
  constructor
  · rintro ⟨hg, hC, hρ⟩
    obtain ⟨u, g₁, u', h⟩ := dec_exists hg hC.1
    refine ⟨_, u, g₁, u', h, ?_⟩
    rw [← h.rho_eq]; exact hρ
  · rintro ⟨c, u, g₁, u', h, hg₁⟩
    refine ⟨h.mem, h.cell_decomposition_mem, ?_⟩
    show rho k r l g ∈ D₁
    rw [h.rho_eq]; exact hg₁
end Formalism.FourierDecayAlt.P.Qx4
