-- Prove2me | solution 1 for Formalism.L2.Col.HXm_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:43:42.478108+00:00
-- url     : https://prove2.me/submissions/d3c326fa-d1dd-4937-9f52-b7317bc74a5b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DimensionMassJointBound
import Definitions.Def_Formalism_LocalToGlobal_Columns_LevGCount
import Theorems.Thm_Formalism_L2_Col_blkIdx_replicate_of_le
import Theorems.Thm_Formalism_L2_Col_blkIdx_replicate_lt
import Theorems.Thm_Formalism_L2_Col_exists_diagEmb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset IsDedekindDomain NumberField
open Formalism Formalism.L2 Formalism.L2.Col
variable {n : ℕ} {κ : Type} [CommRing κ] {K : Type} [Field K]
namespace Formalism.L2.Col
theorem _root_.solution (r t m : ℕ) :
    HXm κ (r + m * t + 1) r t m = (HJ κ (r + m * t) r t m).map (diagEmb κ (Nat.le_succ (r + m * t))) := by
  ext M
  constructor
  · intro hM
    obtain ⟨hJ, hF⟩ := hM
    have hlast : fine r (List.replicate m t) (r + m * t) = r + m := by
      unfold fine
      by_cases h0 : r + m * t < r
      · omega
      · rw [if_neg h0, Nat.add_sub_cancel_left, blkIdx_replicate_of_le t m (m * t) le_rfl]
    have hr : ∀ j : Fin (r + m * t + 1), j.val < r + m * t →
        (M : Matrix (Fin (r + m * t + 1)) (Fin (r + m * t + 1)) κ) (Fin.last (r + m * t)) j = 0 := by
      intro j hj
      apply hJ.1
      show fine r (List.replicate m t) j.val < fine r (List.replicate m t) (Fin.last (r + m * t)).val
      rw [Fin.val_last, hlast]
      unfold fine
      split_ifs with h0
      · omega
      · have := blkIdx_replicate_lt t m (j.val - r) (by omega)
        omega
    obtain ⟨g, hg, hge⟩ := exists_diagEmb M hF hr
    have hgm : g ∈ HJ κ (r + m * t) r t m := by
      show g ∈ btG (r + m * t) κ (fine r (List.replicate m t)) ∧
        ∀ i : Fin (r + m * t), i.val < r → (g : Matrix (Fin (r + m * t)) (Fin (r + m * t)) κ) i i = 1
      refine ⟨?_, fun i hi => ?_⟩
      · show (g : Matrix (Fin (r + m * t)) (Fin (r + m * t)) κ).BlockTriangular (fun i => fine r (List.replicate m t) i.val)
        intro i j hij
        rw [hge]
        exact hJ.1 (i := i.castSucc) (j := j.castSucc) hij
      · rw [hge]
        exact hJ.2 i.castSucc hi
    exact ⟨g, hgm, hg⟩
  · rintro ⟨g, hg, rfl⟩
    show diagEmb κ (Nat.le_succ (r + m * t)) g ∈ HJ κ (r + m * t + 1) r t m ⊓ fixCol (r + m * t + 1) κ (r + m * t)
    exact Subgroup.mem_inf.mpr ⟨diagEmb_mem_uniUT _ hg, diagEmb_mem_fixCol _ le_rfl g⟩
end Formalism.L2.Col
