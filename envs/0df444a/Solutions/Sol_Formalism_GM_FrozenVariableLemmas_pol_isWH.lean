-- Prove2me | solution 1 for Formalism.GM.FrozenVariableLemmas.pol_isWH
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:19:37.597499+00:00
-- url     : https://prove2.me/submissions/7767621f-d784-4aa2-8afa-61cfce85f060

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Theorems.Thm_Formalism_GM_FrozenVariableLemmas_weight_fst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FrozenVariableLemmas
open MvPolynomial Finset
namespace Formalism.GM.FrozenVariableLemmas
theorem _root_.solution (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : M.Letters N) (G : Fin N → ℕ)
    {f : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hf : f ∈ M.Pol p r LL) :
    IsWeightedHomogeneous (fun x : Fin N × Fin r => G x.1) f (∑ b, G b * LL.deg b) := by
  intro m hm
  have hf' : (↑f.support : Set (Fin N × Fin r →₀ ℕ)) ⊆ {m | M.MultiDeg LL m} := hf
  have hms : M.MultiDeg LL m := hf' (mem_support_iff.mpr hm)
  rw [weight_fst]
  exact Finset.sum_congr rfl (fun b _ => by rw [hms b])
end Formalism.GM.FrozenVariableLemmas
