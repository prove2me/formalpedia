-- Prove2me | solution 1 for BCFGJPSSV26.Stable.Hyp.exists_partition
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:09:01.322934+00:00
-- url     : https://prove2.me/submissions/b342ec01-481b-469d-a002-5d48c9292aac

module

public import Definitions.Def_BCFGJPSSV26_Stable_Structure_ClusterWitness
public import Definitions.Def_BCFGJPSSV26_Stable_Structure_Partition
import all Definitions.Def_BCFGJPSSV26_Stable_Structure_Partition
public import Theorems.Thm_BCFGJPSSV26_Stable_Hyp_card_O1_le
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

variable {X : Ctx}

/-- **(d-i)** The clusters of `O_S`, sent to their substitutes `σ₀`, cost at most
`(1 + η) cost_OPT + 30 ε opt`: synced ones by `BCFGJPSSV26.Stable.Hyp.syncSub`, close ones by
`BCFGJPSSV26.Stable.Hyp.closeSub`, those of `O_S1` by
`BCFGJPSSV26.Stable.ClientWitness.sum_OS1_le`, with `cost(S) ≤ 4 opt`. -/
theorem Hyp.pt_cost_OSall (H : Hyp X) {Λ₁ : List (Dummy X.I)} (w₁ : ClientWitness X Λ₁) :
    ∑ c ∈ X.OSall w₁.OL, ∑ j ∈ X.C c, X.dist j (X.σ₀ c) ≤
      (1 + eta) * ∑ c ∈ X.OSall w₁.OL, X.costO c + 30 * X.ε * X.opt := by
  classical
  have hd1 : Disjoint X.Osync X.Ocl := by
    rw [disjoint_left]
    intro c h1 h2
    exact (mem_filter.1 h2).2.1 (mem_filter.1 h1).2
  have hd2 : Disjoint X.OS0 (X.OS1 w₁.OL) := by
    rw [disjoint_left]
    intro c h1 h2
    exact (mem_sdiff.1 (mem_sdiff.1 (mem_filter.1 h2).1).1).2 h1
  have hsplit : ∀ F : Fin X.I.m → ℝ, ∑ c ∈ X.OSall w₁.OL, F c =
      ∑ c ∈ X.Osync, F c + ∑ c ∈ X.Ocl, F c + ∑ c ∈ X.OS1 w₁.OL, F c := by
    intro F
    rw [Ctx.OSall, sum_union hd2, Ctx.OS0, sum_union hd1]
  rw [hsplit, hsplit]
  have hs : ∑ c ∈ X.Osync, ∑ j ∈ X.C c, X.dist j (X.σ₀ c) =
      ∑ c ∈ X.Osync, ∑ j ∈ X.C c, X.dist j (X.σsync c) := by
    refine sum_congr rfl fun c hc ↦ ?_
    simp only [Ctx.σ₀]
    rw [if_pos (mem_filter.1 hc).2]
  have hcl : ∑ c ∈ X.Ocl, ∑ j ∈ X.C c, X.dist j (X.σ₀ c) ≤
      (1 + eta) * ∑ c ∈ X.Ocl, X.costO c + 2 * X.ε * X.I.costF X.S := by
    calc ∑ c ∈ X.Ocl, ∑ j ∈ X.C c, X.dist j (X.σ₀ c)
        ≤ ∑ c ∈ X.Ocl, ((1 + eta) * X.costO c + 2 * X.ε * X.costS (X.C c)) := by
          refine sum_le_sum fun c hc ↦ ?_
          simp only [Ctx.σ₀]
          rw [if_neg (mem_filter.1 hc).2.1]
          exact H.closeSub hc
      _ = (1 + eta) * ∑ c ∈ X.Ocl, X.costO c + 2 * X.ε * ∑ c ∈ X.Ocl, X.costS (X.C c) := by
          rw [sum_add_distrib, mul_sum, mul_sum]
      _ ≤ (1 + eta) * ∑ c ∈ X.Ocl, X.costO c + 2 * X.ε * X.I.costF X.S := by
          have := H.pt_sum_costS_C_le (A := X.Ocl) (filter_subset _ _)
          have := H.eps_pos
          nlinarith
  have h1 : ∑ c ∈ X.OS1 w₁.OL, ∑ j ∈ X.C c, X.dist j (X.σ₀ c) ≤ X.ε * X.opt := by
    refine le_of_eq_of_le (sum_congr rfl fun c hc ↦ ?_) (w₁.sum_OS1_le H)
    simp only [Ctx.σ₀]
    rw [if_neg (X.pt_not_isSynced_of_mem_OS1 hc)]
  have hsync := H.syncSub
  have h4 : X.I.costF X.S ≤ 4 * X.opt :=
    costF_le_four_opt H.valid H.k_le_m X.P.hN H.alo
  have hS0 : 0 ≤ X.I.costF X.S := Instance.costF_nonneg H.valid _
  have hA : 0 ≤ ∑ c ∈ X.Osync, X.costO c := sum_nonneg fun c _ ↦ X.pt_costO_nonneg H.valid c
  have hB : 0 ≤ ∑ c ∈ X.OS1 w₁.OL, X.costO c := sum_nonneg fun c _ ↦ X.pt_costO_nonneg H.valid c
  have hε := H.eps_pos
  have hε' := H.eps_lt
  have hη : 4 * X.ε ≤ eta := by unfold eta; linarith
  rw [hs]
  have hopt : 0 ≤ X.opt := H.opt_pos.le
  have e1 : (1 + 4 * X.ε) * ∑ c ∈ X.Osync, X.costO c ≤ (1 + eta) * ∑ c ∈ X.Osync, X.costO c :=
    mul_le_mul_of_nonneg_right (by linarith) hA
  have e2 : 0 ≤ (1 + eta) * ∑ c ∈ X.OS1 w₁.OL, X.costO c := mul_nonneg (by unfold eta; norm_num) hB
  nlinarith

namespace Partition

variable {X : Ctx} {Λ₁ : List (Dummy X.I)} {w₁ : ClientWitness X Λ₁}
  {LS' : Finset (Fin X.I.m)} {Λ₂ : List (Dummy X.I)} {w₂ : ClusterWitness w₁ LS' Λ₂}
  (Q : Partition w₂)

end Partition

/-- **The structural theorem**: good outcomes of both samplings give a partition. -/
theorem Hyp.exists_partition {X : Ctx} (H : Hyp X) {Λ₁ : List (Dummy X.I)}
    (w₁ : ClientWitness X Λ₁) {LS' : Finset (Fin X.I.m)} {Λ₂ : List (Dummy X.I)}
    (w₂ : ClusterWitness w₁ LS' Λ₂) : Nonempty (Partition w₂) := by
  classical
  have hO2 : ∀ c ∈ X.O2 w₁.OL, c ∈ X.O1 ∧ c ∉ w₁.OL := fun c hc ↦
    mem_sdiff.1 (mem_sdiff.1 hc).1
  have hOBO2 : X.OB w₁.OL w₂.OL2 ⊆ X.O2 w₁.OL := fun c hc ↦ (mem_sdiff.1 (mem_sdiff.1 hc).1).1
  have hOBX : ∀ c ∈ X.OB w₁.OL w₂.OL2, c ∉ X.OX w₁.OL := fun c hc ↦
    (mem_sdiff.1 (mem_sdiff.1 hc).1).2
  have hOXO2 : X.OX w₁.OL ⊆ X.O2 w₁.OL := filter_subset _ _
  have hsat : ∀ c ∈ X.OB w₁.OL w₂.OL2,
      X.pt_sat c ∈ X.Gam c ∧ X.dF c (X.pt_sat c) ≤ (1 + X.ε) * X.per c := by
    intro c hc
    obtain ⟨c', hc', hd, -⟩ := (w₁.isFar H (hOBO2 hc)).near_sat
    exact Ctx.pt_sat_spec ⟨c', hc', hd⟩
  obtain ⟨OR, hORB, hinj, hnot, hrep⟩ :=
    pt_exists_reps (X.OB w₁.OL w₂.OL2) X.pt_sat (X.LSX w₁.OL)
  set OP := X.OX w₁.OL ∪ (X.OB w₁.OL w₂.OL2 \ OR) with hOP
  have hu : OP ∪ OR = X.OX w₁.OL ∪ X.OB w₁.OL w₂.OL2 := by
    ext c
    simp only [hOP, mem_union, mem_sdiff]
    constructor
    · rintro ((h | ⟨h, -⟩) | h)
      exacts [Or.inl h, Or.inr h, Or.inr (hORB h)]
    · rintro (h | h)
      · exact Or.inl (Or.inl h)
      · by_cases h' : c ∈ OR
        · exact Or.inr h'
        · exact Or.inl (Or.inr ⟨h, h'⟩)
  have hd : Disjoint OP OR := by
    rw [disjoint_left]
    intro c hc hcR
    rcases mem_union.1 hc with h | h
    · exact hOBX c (hORB hcR) h
    · exact (mem_sdiff.1 h).2 hcR
  have hOP2 : OP ⊆ X.O2 w₁.OL := union_subset hOXO2 (sdiff_subset.trans hOBO2)
  have hcount := Ctx.pt_card_cover_of w₁ w₂ hu hd H.isOpt.card
  have hLSX := Ctx.pt_LSX_eq_image (X := X) w₁.OL
  have hGamR : X.GamOf OR ⊆ X.GamOf (X.OB w₁.OL w₂.OL2) :=
    biUnion_subset_biUnion_of_subset_left _ hORB
  have hGam : X.GamOf OR ⊆ LS' := hGamR.trans w₂.Gam_sub
  have hσR : OR.image X.pt_sat ⊆ X.GamOf OR := by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := mem_image.1 hx
    exact mem_biUnion.2 ⟨c, hc, (hsat c (hORB hc)).1⟩
  have hσ₀ : (X.OSall w₁.OL).image X.σ₀ ⊆ LS' := hLSX ▸ w₂.LSX_sub
  have hLSσ : (X.OSall w₁.OL).image X.σ₀ ∪ OR.image X.pt_sat ⊆ LS' :=
    union_subset hσ₀ (hσR.trans hGam)
  have hZ : (LS'.card + (Λ₁.length + Λ₂.length + OP.card)) - X.I.k ≤
      (LS' \ ((X.OSall w₁.OL).image X.σ₀ ∪ OR.image X.pt_sat)).card := by
    rw [card_sdiff_of_subset hLSσ]
    have h1 := card_union_le ((X.OSall w₁.OL).image X.σ₀) (OR.image X.pt_sat)
    have h2 : ((X.OSall w₁.OL).image X.σ₀).card ≤ (X.OSall w₁.OL).card := card_image_le
    have h3 : (OR.image X.pt_sat).card ≤ OR.card := card_image_le
    rw [w₁.length_eq, w₂.length_eq]
    omega
  obtain ⟨Z, hZsub, hZcard⟩ := exists_subset_card_eq hZ
  have hcard : w₁.OL.card + w₂.OL2.card + OP.card + OR.card ≤ X.s := by
    have h1 : X.OS0.card ≤ (X.OSall w₁.OL).card := card_le_card subset_union_left
    have h2 : X.O1.card = X.O.card - X.OS0.card := card_sdiff_of_subset X.pt_OS0_subset
    have h3 := H.card_O1_le
    rw [H.isOpt.card] at h2
    omega
  refine ⟨{
    OP := OP
    OR := OR
    ψ := fun c ↦ if c ∈ X.OX w₁.OL then X.ψX w₁.OL c else X.pt_sat c
    σR := X.pt_sat
    Zstar := Z
    union_eq := hu
    OX_sub := subset_union_left
    disjoint := hd
    card_le := hcard
    ψ_mem := ?_
    ψ_dist := ?_
    σR_gam := fun c hc ↦ hsat c (hORB hc)
    σR_inj := hinj
    σR_disj := fun c hc ↦ hLSX ▸ hnot c hc
    σ₀_sub := hσ₀
    Gam_sub := hGam
    cost_OS := H.pt_cost_OSall w₁
    cost_mix := ?_
    hidden_PL := ?_
    hidden_R := ?_
    gam_cost := ?_
    far_R := fun c hc ↦ w₁.isFar H (hOBO2 (hORB hc))
    per_pos_P := fun c hc ↦ (w₁.isFar H (hOP2 hc)).per_pos
    Zstar_sub := hZsub
    Zstar_card := hZcard }⟩
  · intro c hc
    by_cases hX : c ∈ X.OX w₁.OL
    · simp only [if_pos hX]
      exact mem_union_left _ (hLSX ▸ (Ctx.pt_ψX_spec hX).1)
    · simp only [if_neg hX]
      have hcB : c ∈ X.OB w₁.OL w₂.OL2 \ OR := (mem_union.1 hc).resolve_left hX
      rcases hrep c (mem_sdiff.1 hcB).1 (mem_sdiff.1 hcB).2 with h | ⟨c', hc', heq⟩
      · exact mem_union_left _ (hLSX ▸ h)
      · exact mem_union_right _ (mem_image.2 ⟨c', hc', heq⟩)
  · intro c hc
    by_cases hX : c ∈ X.OX w₁.OL
    · simp only [if_pos hX]
      exact (Ctx.pt_ψX_spec hX).2
    · simp only [if_neg hX]
      have hcB : c ∈ X.OB w₁.OL w₂.OL2 \ OR := (mem_union.1 hc).resolve_left hX
      refine (hsat c (mem_sdiff.1 hcB).1).2.trans ?_
      have hp : 0 ≤ X.per c := per_nonneg H.valid _ _ _
      have hk := kappa_pos (X.xr c)
      have hε := H.eps_pos
      unfold Ctx.kap
      nlinarith
  · refine lt_of_le_of_lt (sum_le_sum_of_subset_of_nonneg ?_ ?_) w₂.cost₁
    · refine union_subset_union hGamR (sdiff_subset_sdiff (subset_refl _) ?_)
      rw [hLSX]
      exact subset_union_left
    · intro c _ _
      exact sum_nonneg fun j _ ↦ dMix_nonneg H.valid (H.pt_radius_nonneg_of_witness w₁ w₂) _ _
  · refine lt_of_le_of_lt (sum_le_sum_of_subset_of_nonneg ?_ ?_) w₁.hidden_early
    · intro c hc
      rcases mem_union.1 hc with h | h
      · obtain ⟨h1, h2⟩ := hO2 c (hOP2 h)
        exact mem_sdiff.2 ⟨h1, fun h' ↦ h2 (w₁.OLe_sub h')⟩
      · obtain ⟨h1, h2⟩ := mem_sdiff.1 h
        refine mem_sdiff.2 ⟨?_, h2⟩
        rcases mem_union.1 h1 with h1 | h1
        · exact w₁.OL_sub h1
        · exact (hO2 c (mem_sdiff.1 (w₂.OL2_sub h1)).1).1
    · intro c _ _
      exact Instance.costOn_nonneg H.valid _ _
  · refine lt_of_le_of_lt (sum_le_sum_of_subset_of_nonneg ?_ ?_) w₁.hidden_hit
    · intro c hc
      exact mem_sdiff.2 (hO2 c (hOBO2 (hORB hc)))
    · intro c _ _
      exact Instance.costOn_nonneg H.valid _ _
  · refine lt_of_le_of_lt (sum_le_sum_of_subset_of_nonneg hGamR ?_) w₂.cost₀
    intro c _ _
    exact Instance.costOn_nonneg H.valid _ _

end BCFGJPSSV26.Stable

end

public section

theorem solution : type_of% @BCFGJPSSV26.Stable.Hyp.exists_partition := @BCFGJPSSV26.Stable.Hyp.exists_partition
