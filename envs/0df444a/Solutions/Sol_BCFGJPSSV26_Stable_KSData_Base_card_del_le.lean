-- Prove2me | solution 1 for BCFGJPSSV26.Stable.KSData.Base.card_del_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:11:31.228968+00:00
-- url     : https://prove2.me/submissions/485c3307-b85b-4846-a3d7-7964497aaa4c

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

theorem Base.card_del_le {del : List ℕ} {D : List DumQ} (hb : K.Base del D) :
    del.length ≤ K.X.s := by
  classical
  have hinj : Set.InjOn K.fac {i | i ∈ del} := fun i hi i' hi' he ↦ by
    rw [← K.fac_val (hb.del_sub i hi).1, ← K.fac_val (hb.del_sub i' hi').1, he]
  have h1 : (del.toFinset.image K.fac).card = del.length := by
    rw [card_image_of_injOn (fun i hi i' hi' he ↦ hinj (List.mem_toFinset.1 hi)
      (List.mem_toFinset.1 hi') he), List.toFinset_card_of_nodup hb.del_nodup]
  have h2 : del.toFinset.image K.fac ⊆ K.X.S \ K.X.LSX K.w₁.OL := fun _ hc ↦ by
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hc
    exact (hb.del_sub i (List.mem_toFinset.1 hi)).2
  rw [← h1]
  exact (card_le_card h2).trans (K.H.card_S_sdiff_LSX_le K.w₁)

end

section

variable {K}

end

end KSData

end BCFGJPSSV26.Stable

end

public section

theorem solution : type_of% @BCFGJPSSV26.Stable.KSData.Base.card_del_le := @BCFGJPSSV26.Stable.KSData.Base.card_del_le
