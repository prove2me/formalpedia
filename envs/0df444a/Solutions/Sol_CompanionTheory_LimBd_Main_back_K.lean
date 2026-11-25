-- Prove2me | solution 1 for CompanionTheory.LimBd.Main.back_K
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:56:47.933895+00:00
-- url     : https://prove2.me/submissions/06a6b976-4e77-4d28-aa59-5882ef117c82

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_ZuckDualTOfZuckDual
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurH
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_Letter
import Theorems.Thm_CompanionTheory_LimBd_Main_inv_unitary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.LimBd CompanionTheory.LimBd.Main
open Formalism.FourierDecayAlt PI.UpqRep Matrix CompanionTheory.LimBd.SchurHpk
open scoped InnerProductSpace
variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : B.Mat k r}
namespace CompanionTheory.LimBd.Main
theorem _root_.solution (hP : IsCayleyU k r ε P) {g : B.Mat k r} (hg : g ∈ Kset ε) :
    P⁻¹ * g * P ∈ UH (Hpk k r) ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _) := by
  refine ⟨back_mem hP.1 ?_, Submonoid.mul_mem _ (Submonoid.mul_mem _ (inv_unitary hP) hg.1) hP.2⟩
  show gᴴ * Jm ε * g = Jm ε
  have h1 : gᴴ * g = 1 := Matrix.mem_unitaryGroup_iff'.1 hg.1
  rw [Matrix.mul_assoc, ← hg.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]
end CompanionTheory.LimBd.Main
