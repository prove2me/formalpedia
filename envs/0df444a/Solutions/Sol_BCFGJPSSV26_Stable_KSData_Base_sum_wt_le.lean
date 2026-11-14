-- Prove2me | solution 1 for BCFGJPSSV26.Stable.KSData.Base.sum_wt_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:07:40.062205+00:00
-- url     : https://prove2.me/submissions/24af9c6b-9a1d-40d8-86c4-200a991dbded

module

public import Definitions.Def_BCFGJPSSV26_Stable_Alg_ClusterSamplingGhost
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_ClusterSamplingBridge
import all Definitions.Def_BCFGJPSSV26_Stable_Alg_ClusterSamplingBridge
public import Theorems.Thm_BCFGJPSSV26_Stable_Hyp_costMix_intermediate_lt
public import Theorems.Thm_BCFGJPSSV26_Stable_costF_le_four_opt

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

namespace KSData

variable (K : KSData)

section

variable {K}

end

section

variable {K}

/-- **The mixed set costs less than `6 opt`** (`BCFGJPSSV26.Stable.Hyp.costMix_intermediate_lt`). -/
theorem Base.costMix_lt {del : List ℕ} {D : List DumQ} (hb : K.Base del D)
    (hD : (toRaw K.X.I).ValidDums D) (hg : K.GamSub del D) :
    costMix K.X.I (K.LSp del) (K.mixL D) < 6 * K.X.opt :=
  K.H.costMix_intermediate_lt K.w₁ (Λ₂ := toDums K.X.I D) (M := K.matched D) (φ := K.phi D)
    hb.LSX_subset (K.LSp_subset del) (K.matched_subset D)
    (fun c hc ↦ by
      obtain ⟨c', -, hc'⟩ := mem_biUnion.1 hc
      exact K.mem_LSp.2 ⟨K.X.Gam_subset_S c' hc', hg c hc⟩)
    (fun c hc ↦ ⟨K.phi_mem hD hc, hb.rad c hc⟩)

/-- **The total weight** is at most `6 opt`. -/
theorem Base.sum_wt_le {del : List ℕ} {D : List DumQ} (hb : K.Base del D)
    (hD : (toRaw K.X.I).ValidDums D) (hg : K.GamSub del D) (ph : ℕ) :
    ∑ c ∈ K.LSp del, K.wt ph del D c ≤ 6 * K.X.opt := by
  classical
  have hv := K.H.valid
  have hopt : 0 < K.X.opt := K.H.opt_pos
  by_cases h0 : ph = 0
  · have h1 : ∑ c ∈ K.LSp del, K.wt ph del D c ≤ ∑ c ∈ K.X.S, K.wt ph del D c :=
      sum_le_sum_of_subset_of_nonneg (K.LSp_subset del) fun c _ _ ↦ K.wt_nonneg _ _ _ c
    have h2 : ∑ c ∈ K.X.S, K.wt ph del D c = K.X.I.costF K.X.S := by
      unfold wt
      simp only [h0, ↓reduceIte]
      rw [Instance.costF, Instance.sum_clusters K.H.S_nonempty]
      rfl
    have h3 := costF_le_four_opt hv K.H.k_le_m K.X.P.hN K.H.alo
    unfold Ctx.opt at hopt ⊢
    linarith
  · have h1 : ∑ c ∈ K.LSp del, K.wt ph del D c ≤ costMix K.X.I (K.LSp del) (K.mixL D) := by
      unfold wt costMix costMixOn
      simp only [h0, ↓reduceIte]
      rw [← sum_biUnion]
      · refine sum_le_sum_of_subset_of_nonneg (subset_univ _) fun j _ _ ↦ ?_
        exact dMix_nonneg hv (hb.radius_nonneg hD) _ _
      · intro c _ c' _ hcc'
        exact disjoint_of_subset_left (filter_subset _ _) (disjoint_of_subset_right
          (filter_subset _ _) (Instance.disjoint_cluster _ hcc'))
    linarith [hb.costMix_lt hD hg]

end

end KSData

end BCFGJPSSV26.Stable

end

public section

theorem solution : type_of% @BCFGJPSSV26.Stable.KSData.Base.sum_wt_le := @BCFGJPSSV26.Stable.KSData.Base.sum_wt_le
