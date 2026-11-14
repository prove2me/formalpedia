-- Prove2me | solution 1 for BCFGJPSSV26.Stable.Hyp.costMix_intermediate_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:05:56.748057+00:00
-- url     : https://prove2.me/submissions/4dfeeb5a-d257-4429-a690-d8f8434f176a

module

public import Definitions.Def_BCFGJPSSV26_Stable_Structure_ClientWitness
public import Definitions.Def_BCFGJPSSV26_Stable_Stability_FewNotInSync
public import Definitions.Def_BCFGJPSSV26_Stable_Stability_SyncSub
public import Definitions.Def_BCFGJPSSV26_Stable_Structure_ClusterWitness
import all Definitions.Def_BCFGJPSSV26_Stable_Structure_ClusterWitness
public import Theorems.Thm_BCFGJPSSV26_Stable_Hyp_closeSub
public import Theorems.Thm_BCFGJPSSV26_Stable_Hyp_syncSub
public import Theorems.Thm_BCFGJPSSV26_Stable_costF_le_four_opt

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

namespace Ctx

variable (X : Ctx)

end Ctx

namespace Hyp

variable {X : Ctx} (H : Hyp X)
include H

/-- **The clusters outside `O₂`** cost at most `5 cost_OPT + 37 ε opt` in `(LS_X, Λ₁)`. -/
theorem cost_exceptional_le {Λ₁ : List (Dummy X.I)} (w₁ : ClientWitness X Λ₁) :
    ∑ c ∈ X.O \ X.O2 w₁.OL, costMixOn X.I (X.LSX w₁.OL) Λ₁ (X.C c) ≤
      5 * ∑ c ∈ X.O \ X.O2 w₁.OL, X.costO c + 37 * X.ε * X.opt := by
  classical
  have hv := H.valid
  have he := H.eps_pos
  have he' := H.eps_lt
  have hOS0 : ∀ c, c ∈ X.O2 w₁.OL → c ∉ X.OS0 := fun c hc ↦
    (mem_sdiff.1 (w₁.O2_subset hc)).2
  have hOL1 : ∀ c ∈ w₁.OL, c ∈ X.O1 := fun c hc ↦ w₁.OL_sub hc
  have hOS11 : ∀ c ∈ X.OS1 w₁.OL, c ∈ X.O1 ∧ c ∉ w₁.OL := fun c hc ↦
    mem_sdiff.1 (mem_filter.1 hc).1
  have hA : X.O \ X.O2 w₁.OL = X.Osync ∪ X.Ocl ∪ X.OS1 w₁.OL ∪ w₁.OL := by
    ext c
    simp only [mem_sdiff, mem_union]
    constructor
    · rintro ⟨hcO, hc2⟩
      by_cases h0 : c ∈ X.OS0
      · rcases mem_union.1 h0 with h | h
        · exact Or.inl (Or.inl (Or.inl h))
        · exact Or.inl (Or.inl (Or.inr h))
      have h1 : c ∈ X.O1 := mem_sdiff.2 ⟨hcO, h0⟩
      by_cases hL : c ∈ w₁.OL
      · exact Or.inr hL
      by_cases hS1 : c ∈ X.OS1 w₁.OL
      · exact Or.inl (Or.inr hS1)
      exact absurd (mem_sdiff.2 ⟨mem_sdiff.2 ⟨h1, hL⟩, hS1⟩) hc2
    · rintro (((h | h) | h) | h)
      · exact ⟨(mem_filter.1 h).1, fun h2 ↦ hOS0 c h2 (mem_union_left _ h)⟩
      · exact ⟨(mem_filter.1 h).1, fun h2 ↦ hOS0 c h2 (mem_union_right _ h)⟩
      · exact ⟨(mem_sdiff.1 (hOS11 c h).1).1, fun h2 ↦ (mem_sdiff.1 h2).2 h⟩
      · exact ⟨(mem_sdiff.1 (hOL1 c h)).1, fun h2 ↦ (mem_sdiff.1 (mem_sdiff.1 h2).1).2 h⟩
  have d1 : Disjoint X.Osync X.Ocl :=
    disjoint_left.2 fun c h1 h2 ↦ (mem_filter.1 h2).2.1 (mem_filter.1 h1).2
  have d2 : Disjoint (X.Osync ∪ X.Ocl) (X.OS1 w₁.OL) :=
    disjoint_right.2 fun c h1 h2 ↦ (mem_sdiff.1 (hOS11 c h1).1).2 h2
  have d3 : Disjoint (X.Osync ∪ X.Ocl ∪ X.OS1 w₁.OL) w₁.OL := by
    refine disjoint_right.2 fun c h1 h2 ↦ ?_
    rcases mem_union.1 h2 with h2 | h2
    · exact (mem_sdiff.1 (hOL1 c h1)).2 h2
    · exact (hOS11 c h2).2 h1
  rw [hA]
  simp only [sum_union d3, sum_union d2, sum_union d1]
  -- the four parts
  have hsync : ∑ c ∈ X.Osync, costMixOn X.I (X.LSX w₁.OL) Λ₁ (X.C c) ≤
      (1 + 4 * X.ε) * ∑ c ∈ X.Osync, X.costO c + 5 * X.ε * X.I.costF X.S := by
    refine le_trans (sum_le_sum fun c hc ↦ costMixOn_le_of_mem ?_ _) H.syncSub
    refine mem_union_left _ (mem_image.2 ⟨c, mem_union_left _ hc, ?_⟩)
    unfold Ctx.σ₀
    exact if_pos (mem_filter.1 hc).2
  have hcl : ∑ c ∈ X.Ocl, costMixOn X.I (X.LSX w₁.OL) Λ₁ (X.C c) ≤
      (1 + eta) * ∑ c ∈ X.Ocl, X.costO c + 2 * X.ε * ∑ c ∈ X.Ocl, X.costS (X.C c) := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_le_sum fun c hc ↦ le_trans (costMixOn_le_of_mem ?_ _) (H.closeSub hc)
    refine mem_union_left _ (mem_image.2 ⟨c, mem_union_right _ hc, ?_⟩)
    unfold Ctx.σ₀
    exact if_neg (mem_filter.1 hc).2.1
  have hos1 : ∑ c ∈ X.OS1 w₁.OL, costMixOn X.I (X.LSX w₁.OL) Λ₁ (X.C c) ≤ X.ε * X.opt :=
    le_trans (sum_le_sum fun c hc ↦ costMixOn_le_of_mem
      (mem_union_right _ (mem_image_of_mem _ hc)) _) (w₁.sum_OS1_le H)
  have hol : ∑ c ∈ w₁.OL, costMixOn X.I (X.LSX w₁.OL) Λ₁ (X.C c) ≤
      4 * ∑ c ∈ w₁.OL, X.costO c + 2 * X.ε * ∑ c ∈ w₁.OL, X.costS (X.C c) := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    exact sum_le_sum fun c hc ↦ H.costMixOn_OL_le w₁ hc _
  -- the errors
  have hS4 : X.I.costF X.S ≤ 4 * X.opt := costF_le_four_opt hv H.k_le_m X.P.hN H.alo
  have hcl' : ∑ c ∈ X.Ocl, X.costS (X.C c) ≤ X.I.costF X.S := H.sum_costS_le (filter_subset _ _)
  have hol' : ∑ c ∈ w₁.OL, X.costS (X.C c) ≤ X.I.costF X.S :=
    H.sum_costS_le fun c hc ↦ (mem_sdiff.1 (hOL1 c hc)).1
  have e1 : X.ε * ∑ c ∈ X.Ocl, X.costS (X.C c) ≤ X.ε * X.I.costF X.S :=
    mul_le_mul_of_nonneg_left hcl' he.le
  have e2 : X.ε * ∑ c ∈ w₁.OL, X.costS (X.C c) ≤ X.ε * X.I.costF X.S :=
    mul_le_mul_of_nonneg_left hol' he.le
  have e3 : X.ε * X.I.costF X.S ≤ X.ε * (4 * X.opt) := mul_le_mul_of_nonneg_left hS4 he.le
  have p1 : 0 ≤ ∑ c ∈ X.Osync, X.costO c :=
    sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ Instance.dd_nonneg hv _ _
  have p2 : 0 ≤ ∑ c ∈ X.Ocl, X.costO c :=
    sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ Instance.dd_nonneg hv _ _
  have p3 : 0 ≤ ∑ c ∈ X.OS1 w₁.OL, X.costO c :=
    sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ Instance.dd_nonneg hv _ _
  have p4 : 0 ≤ ∑ c ∈ w₁.OL, X.costO c :=
    sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ Instance.dd_nonneg hv _ _
  have q1 : X.ε * ∑ c ∈ X.Osync, X.costO c ≤ 1 / 200 * ∑ c ∈ X.Osync, X.costO c :=
    mul_le_mul_of_nonneg_right he'.le p1
  unfold eta at hcl
  nlinarith

/-- **An intermediate mixed set** of the cluster sampling costs less than `6 opt`: `LS'`
between `LS_X` and `S` containing the satellites of the unmatched clusters of `O₂ \ O_X`, and
dummies `Λ₂` matching the clusters of `M` with the radius bounds. -/
theorem costMix_intermediate_lt {Λ₁ : List (Dummy X.I)} (w₁ : ClientWitness X Λ₁)
    {LS' : Finset (Fin X.I.m)} {Λ₂ : List (Dummy X.I)} {M : Finset (Fin X.I.m)}
    {φ : Fin X.I.m → Dummy X.I} (hX : X.LSX w₁.OL ⊆ LS') (hS : LS' ⊆ X.S)
    (hM : M ⊆ X.O2 w₁.OL \ X.OX w₁.OL) (hΓ : X.GamOf (X.OB w₁.OL M) ⊆ LS')
    (hφ : ∀ c ∈ M, φ c ∈ Λ₂ ∧ X.I.dd (.inr c) (φ c).leader ≤ (φ c).radius ∧
      (φ c).radius ≤ (1 + X.kap c + 6 * X.ε) * X.per c) :
    costMix X.I LS' (Λ₁ ++ Λ₂) < 6 * X.opt := by
  -- (`LS' ⊆ S` and `M ⊆ O₂ \ O_X` are not needed for the bound)
  have _ := hS
  have _ := hM
  have hv := H.valid
  have he := H.eps_pos
  have he' := H.eps_lt
  have hO2 : X.O2 w₁.OL ⊆ X.O := fun c hc ↦ (mem_sdiff.1 (w₁.O2_subset hc)).1
  -- the clusters of `O₂`
  have hcl : ∀ c ∈ X.O2 w₁.OL, ∑ j ∈ X.C c, dMix X.I (.inl j) LS' (Λ₁ ++ Λ₂) ≤
      5 * X.costO c := by
    intro c hc
    have hO0 : 0 ≤ X.costO c := sum_nonneg fun _ _ ↦ Instance.dd_nonneg hv _ _
    have hκ : 12 / 65 ≤ X.kap c ∧ X.kap c ≤ 23 / 65 := kappa_mem _
    have h1 : (1 + X.kap c + 6 * X.ε) * ((X.C c).card * X.per c) ≤
        (1 + X.kap c + 6 * X.ε) * ((1 + 2 * X.ε) * X.costO c) :=
      mul_le_mul_of_nonneg_left (H.card_mul_per_le c) (by linarith)
    have h2 : (1 + X.kap c + 6 * X.ε) * (1 + 2 * X.ε) ≤ 3 / 2 := by nlinarith
    have h3 : (1 + X.kap c + 6 * X.ε) * (1 + 2 * X.ε) * X.costO c ≤ 3 / 2 * X.costO c :=
      mul_le_mul_of_nonneg_right h2 hO0
    calc ∑ j ∈ X.C c, dMix X.I (.inl j) LS' (Λ₁ ++ Λ₂)
        ≤ ∑ j ∈ X.C c,
            (X.I.dd (.inl j) (.inr c) + 2 * ((1 + X.kap c + 6 * X.ε) * X.per c)) :=
          sum_le_sum fun j _ ↦ H.dMix_O2_le w₁ hX hΓ hφ hc j
      _ = X.costO c + 2 * ((1 + X.kap c + 6 * X.ε) * ((X.C c).card * X.per c)) := by
          rw [sum_add_distrib, sum_const, nsmul_eq_mul]
          unfold Ctx.costO costAt
          ring
      _ ≤ 5 * X.costO c := by nlinarith
  -- the other clusters, by `cost_exceptional_le`
  have hex : ∑ c ∈ X.O \ X.O2 w₁.OL, ∑ j ∈ X.C c, dMix X.I (.inl j) LS' (Λ₁ ++ Λ₂) ≤
      5 * ∑ c ∈ X.O \ X.O2 w₁.OL, X.costO c + 37 * X.ε * X.opt :=
    le_trans (sum_le_sum fun c _ ↦ sum_le_sum fun j _ ↦ dMix_mono hv hX _ _ _)
      (H.cost_exceptional_le w₁)
  have hsum : costMix X.I LS' (Λ₁ ++ Λ₂) =
      ∑ c ∈ X.O, ∑ j ∈ X.C c, dMix X.I (.inl j) LS' (Λ₁ ++ Λ₂) :=
    Instance.sum_clusters H.O_nonempty _
  have hopt : 0 < X.opt := H.opt_pos
  have hoe : X.ε * X.opt ≤ 1 / 200 * X.opt := mul_le_mul_of_nonneg_right he'.le hopt.le
  rw [hsum, ← sum_sdiff hO2]
  have h2 := sum_le_sum hcl
  rw [← mul_sum] at h2
  have h3 := H.opt_eq_sum
  rw [← sum_sdiff hO2] at h3
  linarith

end Hyp

end BCFGJPSSV26.Stable

end

public section

theorem solution : type_of% @BCFGJPSSV26.Stable.Hyp.costMix_intermediate_lt := @BCFGJPSSV26.Stable.Hyp.costMix_intermediate_lt
