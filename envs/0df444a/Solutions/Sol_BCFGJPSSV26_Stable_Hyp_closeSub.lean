-- Prove2me | solution 1 for BCFGJPSSV26.Stable.Hyp.closeSub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:01:25.979089+00:00
-- url     : https://prove2.me/submissions/eb0158dd-7be0-452a-9443-5bd20b4b0bc6

module

public import Definitions.Def_BCFGJPSSV26_Stable_Stability_Defs
public import Definitions.Def_BCFGJPSSV26_Stable_Stability_SyncSub
import all Definitions.Def_BCFGJPSSV26_Stable_Stability_SyncSub

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

namespace Hyp

variable {X : Ctx} (H : Hyp X)
include H

/-- **Substitutes for close clusters** ([BCFGJPSSV26b, Proposition 4.4]). -/
theorem closeSub {c : Fin X.I.m} (hc : c ∈ X.Ocl) :
    ∑ j ∈ X.C c, X.dist j (X.σcl c) ≤ (1 + eta) * X.costO c + 2 * X.ε * X.costS (X.C c) := by
  classical
  have hv := H.valid
  obtain ⟨hcO, -, hclose⟩ := mem_filter.1 hc
  have hcard : (0 : ℝ) < (X.C c).card := by exact_mod_cast (H.cluster_nonempty hcO).card_pos
  have h1 : ∀ j ∈ X.C c, X.dist j (X.σcl c) ≤ X.dist j c + X.dOS c := by
    intro j _
    have := Instance.dd_triangle hv (.inl j) (.inr c) (.inr (X.σcl c))
    have h2 := H.dF_σcl c
    unfold Ctx.dist
    unfold Ctx.dF at h2
    linarith
  calc ∑ j ∈ X.C c, X.dist j (X.σcl c) ≤ ∑ j ∈ X.C c, (X.dist j c + X.dOS c) := sum_le_sum h1
    _ = X.costO c + (X.C c).card * X.dOS c := by
        rw [sum_add_distrib, sum_const, nsmul_eq_mul]
        rfl
    _ ≤ X.costO c + (X.C c).card * (eta * X.avgO c + 2 * X.ε * X.avgS c) := by gcongr
    _ = _ := by
        unfold Ctx.avgO Ctx.avgS
        field_simp
        ring

end Hyp

end BCFGJPSSV26.Stable

end

public section

theorem solution : type_of% @BCFGJPSSV26.Stable.Hyp.closeSub := @BCFGJPSSV26.Stable.Hyp.closeSub
