-- Prove2me | solution 1 for Formalism.L2.Th1.A.WpSh.coeff_shift_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:20:15.317974+00:00
-- url     : https://prove2.me/submissions/756f26ab-deed-4aa0-a6af-893aeac7654b

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_Laurent
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_WpShape

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.WpSh
variable {K : Type u} [Field K]
namespace Formalism.L2.Th1.A.WpSh
theorem _root_.solution {f : K⟦X⟧} (A : K⟦X⟧) {n m : ℕ} (hf : ∀ k < n, coeff k f = 0)
    (hm : 0 < m) : coeff n (X ^ m * (f * A)) = 0 := by
  rw [coeff_X_pow_mul']
  split_ifs with h
  · rw [coeff_mul]
    apply Finset.sum_eq_zero
    intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    rw [hf p.1 (by omega), zero_mul]
  · rfl
end Formalism.L2.Th1.A.WpSh
