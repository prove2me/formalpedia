-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.circle_pow_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:52:49.323363+00:00
-- url     : https://prove2.me/submissions/9decaefd-7e32-4726-b469-bde5380c23fc

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_PrimitiveRootFifteenSubOneUnit
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZCircleCharExtends

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.Z
namespace Formalism.IrreducibleCountingLemmas.Z
theorem _root_.solution {n : ℤ} (hn : n ≠ 0) :
    Function.Surjective (fun a : Circle => a ^ n) := by
  intro z
  obtain ⟨θ, rfl⟩ := Circle.exp_surjective z
  refine ⟨Circle.exp (θ / n), ?_⟩
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  show Circle.exp (θ / n) ^ n = Circle.exp θ
  rw [← Circle.exp_zsmul, zsmul_eq_mul, mul_div_cancel₀ _ hn']
end Formalism.IrreducibleCountingLemmas.Z
