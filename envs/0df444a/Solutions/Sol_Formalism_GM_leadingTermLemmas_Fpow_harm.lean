-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.Fpow_harm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:12.113831+00:00
-- url     : https://prove2.me/submissions/f75c1cb3-4538-4605-a7c5-51eb8ec71af8

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.leadingTermLemmas
open MvPolynomial Finset Formalism.GM
variable {K σ : Type} [Field K] [CharZero K] [Fintype σ] [DecidableEq σ] {r : ℕ} {w e : Fin r → σ}
  (hw : Function.Injective w) (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d)
include hw he hwe
namespace Formalism.GM.leadingTermLemmas
theorem _root_.solution {u : MvPolynomial σ K} (hF : tieF w e u = 0) {t : ℕ} (ht : 1 ≤ t) :
    (tieF w e ^ t) u = 0 := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ht
  rw [add_comm, pow_succ, Module.End.mul_apply, hF, map_zero]
end Formalism.GM.leadingTermLemmas
