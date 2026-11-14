-- Prove2me | solution 1 for BCFGJPSSV26.Stable.KSData.Base.GoodL_eq_empty
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:11:32.086312+00:00
-- url     : https://prove2.me/submissions/470150e3-104b-4df2-9bf4-566a5b211a19

module

public import Definitions.Def_BCFGJPSSV26_Stable_Alg_ClusterSamplingGhost
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_ClusterSamplingBridge
import all Definitions.Def_BCFGJPSSV26_Stable_Alg_ClusterSamplingBridge
public import Theorems.Thm_BCFGJPSSV26_Stable_Hyp_card_S_sdiff_LSX_le

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

namespace KSData

variable (K : KSData)

section

variable {K}

/-- If `s` centers are deleted, all of `S \ LS_X` is. -/
theorem Base.LSp_subset_LSX {del : List ℕ} {D : List DumQ} (hb : K.Base del D)
    (h : K.X.s ≤ del.length) : K.LSp del ⊆ K.X.LSX K.w₁.OL := by
  classical
  intro c hc
  by_contra hcX
  rw [K.mem_LSp] at hc
  have hinj : Set.InjOn K.fac ↑del.toFinset := fun i hi i' hi' he ↦ by
    rw [← K.fac_val (hb.del_sub i (List.mem_toFinset.1 hi)).1,
      ← K.fac_val (hb.del_sub i' (List.mem_toFinset.1 hi')).1, he]
  have h1 : (del.toFinset.image K.fac).card = del.length := by
    rw [card_image_of_injOn hinj, List.toFinset_card_of_nodup hb.del_nodup]
  have h2 : del.toFinset.image K.fac ⊆ K.X.S \ K.X.LSX K.w₁.OL := fun _ hc ↦ by
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hc
    exact (hb.del_sub i (List.mem_toFinset.1 hi)).2
  have h3 := eq_of_subset_of_card_le h2 (by
    rw [h1]
    exact (K.H.card_S_sdiff_LSX_le K.w₁).trans h)
  have : c ∈ del.toFinset.image K.fac := h3 ▸ mem_sdiff.2 ⟨hc.1, hcX⟩
  obtain ⟨i, hi, rfl⟩ := mem_image.1 this
  exact hc.2 (by rw [K.fac_val (hb.del_sub i (List.mem_toFinset.1 hi)).1];
                 exact List.mem_toFinset.1 hi)

end

/-- If `s` centers are deleted, there are no good centers left. -/
theorem Base.GoodL_eq_empty {K : KSData} {ph : ℕ} {del : List ℕ} {D : List DumQ}
    (hb : K.Base del D)
    (hg : K.GamSub del D) (h : K.X.s ≤ del.length) : K.GoodL ph del D = ∅ := by
  refine eq_empty_of_forall_notMem fun c hc ↦ ?_
  have hX := hb.LSp_subset_LSX h
  have hcL := K.GoodL_subset hg hc
  unfold GoodL at hc
  split_ifs at hc
  · exact K.not_mem_LSX_of_GamE (K.GamOf_OB_subset_GamE D hc) (hX hcL)
  · rcases mem_union.1 hc with hc | hc
    · exact K.not_mem_LSX_of_GamE (K.GamOf_OB_subset_GamE D hc) (hX hcL)
    · exact (mem_sdiff.1 hc).2 (hX hcL)

section

variable {K}

end

end KSData

end BCFGJPSSV26.Stable

end

public section

theorem solution : type_of% @BCFGJPSSV26.Stable.KSData.Base.GoodL_eq_empty := @BCFGJPSSV26.Stable.KSData.Base.GoodL_eq_empty
