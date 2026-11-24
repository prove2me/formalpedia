-- Prove2me | solution 1 for Formalism.QuantumDeterminants.io_gl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:42:25.423559+00:00
-- url     : https://prove2.me/submissions/eb4dbc34-5aaf-459f-a9c5-ff7667d1b8a1

import Definitions.Def_Formalism_FormalDegreeBessel_StatementIO
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOCentral
import Theorems.Thm_Formalism_QuantumDeterminants_io_mem_smooth
import Theorems.Thm_Formalism_QuantumDeterminants_ioE_rep
import Theorems.Thm_Formalism_QuantumDeterminants_io_rep_ext
import Theorems.Thm_Formalism_REAL_eabGlV


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ContDiff
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (ε E)
namespace Formalism.QuantumDeterminants
theorem _root_.solution : GlRel (ioE ε E) := by
  intro a b c d
  refine LinearMap.ext fun x => Subtype.ext (funext fun p => ?_)
  obtain ⟨g, hg⟩ := p
  have hF := io_rep_ext x
  have key := eabGlV n ε E (ioExt ε x.1) a b c d g (io_mem_smooth x) hg
  have r1 := ioE_rep (ioE_rep hF c d) a b g hg
  have r2 := ioE_rep (ioE_rep hF a b) c d g hg
  have r3 := ioE_rep hF a d g hg
  have r4 := ioE_rep hF c b g hg
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, Pi.sub_apply]
  rw [← r1, ← r2, key]
  split_ifs <;> simp [r3, r4]
end Formalism.QuantumDeterminants
