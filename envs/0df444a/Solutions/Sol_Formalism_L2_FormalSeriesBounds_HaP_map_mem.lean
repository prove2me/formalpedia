-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.HaP.map_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:58:23.211792+00:00
-- url     : https://prove2.me/submissions/d2344673-f7d9-4478-92b8-bd02eb9e84ed

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHaDefs
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePDescSpanSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHaSpan
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_HaP_lap_map
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_HaP_rowShift_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.HaP
open MvPolynomial Formalism.L2.Pj
variable {Ty : Type} {r : Ty → ℕ} {n : ℕ} {cc : Ty → Ty} {isX : Ty → Prop} {a : Ty → ℕ → ℕ}
namespace Formalism.L2.FormalSeriesBounds.HaP
theorem _root_.solution (hR : RowInvUpSt) (K : Type) [Field K] [CharZero K] (p : MvPolynomial (Letter Ty r n) ℚ)
    (hp : p ∈ HHa r n ℚ cc isX a) : map (algebraMap ℚ K) p ∈ HHa r n K cc isX a := by
  obtain ⟨h1, h2, h3⟩ := hp
  refine ⟨?_, hR Ty r n K _ fun σ i i' hii q => ?_, fun m hm => h3 m (support_map_subset _ _ hm)⟩
  · simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker] at h1 ⊢
    intro τ hτ a0 a1
    rw [lap_map, h1 τ hτ a0 a1, map_zero]
  · have e : ((q : ℚ) : K) = algebraMap ℚ K q := (eq_ratCast (algebraMap ℚ K) q).symm
    rw [e, rowShift_map, h2 σ i i' hii q]
end Formalism.L2.FormalSeriesBounds.HaP
