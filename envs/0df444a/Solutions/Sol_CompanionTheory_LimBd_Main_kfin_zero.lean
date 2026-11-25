-- Prove2me | solution 1 for CompanionTheory.LimBd.Main.kfin_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:14:25.347956+00:00
-- url     : https://prove2.me/submissions/c2cc4bfa-a928-4730-a256-684f53304031

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_ZuckDualTOfZuckDual
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurH
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_Letter

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
theorem _root_.solution {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : B.Mat k r → (H →L[ℂ] H)) :
    IsKFinHpk (k := k) (r := r) σ 0 :=
  ⟨⊥, inferInstance, Submodule.zero_mem _, fun g _ x hx => by
    rw [Submodule.mem_bot] at hx ⊢; rw [hx, map_zero]⟩
end CompanionTheory.LimBd.Main
