-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.EabGlW.flow_of_lieL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:09:29.751967+00:00
-- url     : https://prove2.me/submissions/1f60b0d1-aca9-4483-98ce-06561bba23f7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeneralLinearLevel_ExpMulVecFix
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalIO
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeneralLinearLevel_HpartUnique
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_exp_uh
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_lieL_rsmul
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_exp_mulVec_fix


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.EabGlW
open Formalism.REAL Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.EabGlW
theorem _root_.solution {i : Fin (r + 1)} {X : Mx k r} (hX : X ∈ LieL k r i) : Flow (Glev k r i) X := by
  intro g hg t
  have hY : (t : ℂ) • X ∈ LieL k r i := lieL_rsmul hX t
  obtain ⟨hgU, hgv⟩ := hg
  have hgU' : gᴴ * Hpk k r * g = Hpk k r := hgU
  have hE' : (NormedSpace.exp ((t : ℂ) • X))ᴴ * Hpk k r * NormedSpace.exp ((t : ℂ) • X) = Hpk k r :=
    exp_uh hY.1
  refine ⟨?_, fun a ha => ?_⟩
  · show (g * NormedSpace.exp ((t : ℂ) • X))ᴴ * Hpk k r * (g * NormedSpace.exp ((t : ℂ) • X)) = Hpk k r
    rw [Matrix.conjTranspose_mul]
    calc _ = (NormedSpace.exp ((t : ℂ) • X))ᴴ * (gᴴ * Hpk k r * g) * NormedSpace.exp ((t : ℂ) • X) := by
          simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [hgU', hE']
  · obtain ⟨e1, e2⟩ := hY.2 a ha
    obtain ⟨g1, g2⟩ := hgv a ha
    exact ⟨by rw [← Matrix.mulVec_mulVec, exp_mulVec_fix _ _ e1, g1],
      by rw [← Matrix.mulVec_mulVec, exp_mulVec_fix _ _ e2, g2]⟩
end Formalism.FourierDecayAlt.Q.EabGlW
