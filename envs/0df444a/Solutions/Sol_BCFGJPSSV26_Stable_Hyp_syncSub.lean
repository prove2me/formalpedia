-- Prove2me | solution 1 for BCFGJPSSV26.Stable.Hyp.syncSub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:01:25.110194+00:00
-- url     : https://prove2.me/submissions/d8032458-ee1a-4317-9d78-398917dc7045

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

/-- **Substitutes for synced clusters** ([BCFGJPSSV26b, Proposition 4.3]). -/
theorem syncSub :
    ∑ c ∈ X.Osync, ∑ j ∈ X.C c, X.dist j (X.σsync c) ≤
      (1 + 4 * X.ε) * ∑ c ∈ X.Osync, X.costO c + 5 * X.ε * X.I.costF X.S := by
  classical
  have hv := H.valid
  have hε := H.eps_pos
  have hcostS := Instance.costF_nonneg hv X.S
  have hO : 0 ≤ ∑ c ∈ X.Osync, X.costO c :=
    sum_nonneg fun c _ ↦ sum_nonneg fun j _ ↦ Instance.dd_nonneg hv _ _
  have hS := H.sum_costS_C_le X.Osync
  have hcard : ((X.Osync.card : ℝ)) ≤ X.I.k := by
    have : X.Osync.card ≤ X.O.card := card_filter_le _ _
    rw [H.isOpt.card] at this
    exact_mod_cast this
  have hk : (0 : ℝ) < X.I.k := by
    have := H.two_le_k
    have : (2 : ℝ) ≤ X.I.k := by exact_mod_cast this
    linarith
  have hN := X.P.N_pos'
  have herr : (X.Osync.card : ℝ) * (X.I.costF X.S / (X.P.N * X.I.k)) ≤ X.ε * X.I.costF X.S := by
    have he : X.ε = 1 / X.P.N := rfl
    rw [he, mul_div_assoc', div_le_iff₀ (by positivity)]
    have : (X.Osync.card : ℝ) * X.I.costF X.S ≤ X.I.k * X.I.costF X.S :=
      mul_le_mul_of_nonneg_right hcard hcostS
    calc (X.Osync.card : ℝ) * X.I.costF X.S ≤ X.I.k * X.I.costF X.S := this
      _ = 1 / X.P.N * X.I.costF X.S * (X.P.N * X.I.k) := by field_simp
  calc ∑ c ∈ X.Osync, ∑ j ∈ X.C c, X.dist j (X.σsync c)
      ≤ ∑ c ∈ X.Osync, ((1 + 2 * X.ε) * X.costO c + 2 * X.ε * X.costS (X.C c) +
          X.I.costF X.S / (X.P.N * X.I.k)) := sum_le_sum fun c hc ↦ H.syncSub_one hc
    _ = (1 + 2 * X.ε) * ∑ c ∈ X.Osync, X.costO c + 2 * X.ε * ∑ c ∈ X.Osync, X.costS (X.C c) +
          X.Osync.card * (X.I.costF X.S / (X.P.N * X.I.k)) := by
        rw [sum_add_distrib, sum_add_distrib, sum_const, nsmul_eq_mul, mul_sum, mul_sum]
    _ ≤ _ := by nlinarith

end Hyp

end BCFGJPSSV26.Stable

end

public section

theorem solution : type_of% @BCFGJPSSV26.Stable.Hyp.syncSub := @BCFGJPSSV26.Stable.Hyp.syncSub
