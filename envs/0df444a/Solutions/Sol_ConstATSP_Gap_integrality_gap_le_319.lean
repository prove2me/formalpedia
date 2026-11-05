-- Prove2me | solution 1 for ConstATSP.Gap.integrality_gap_le_319
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T14:04:43.668949+00:00
-- url     : https://prove2.me/submissions/cb58feae-4929-439c-ad77-9b9d74812f67
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ConstATSP_Gap_Graph
import Definitions.Def_ConstATSP_Gap_Instance
import Theorems.Thm_ConstATSP_Gap_theorem_2_4
import Theorems.Thm_ConstATSP_Gap_theorem_8_3
import Theorems.Thm_ConstATSP_Gap_theorem_9_4
import Theorems.Thm_ConstATSP_Gap_singleton_tour_le_ten
import Theorems.Thm_ConstATSP_Gap_vertebrate_tour_bound

open ConstATSP.Gap

theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    (G : ConstATSP.Gap.Graph V E) (w : E → ℝ) (hV : 2 ≤ Fintype.card V) (hG : IsStronglyConnected G)
    (hw : ∀ e, 0 ≤ w e) (x : E → ℝ) (hx : IsHeldKarpFeasible G x) :
    ∃ F : E → ℕ, IsTour G F ∧ ∑ e, (F e : ℝ) * w e ≤ 319 * ∑ e, w e * x e := by
  refine theorem_2_4 319 ?_ G w hV hG hw x hx
  intro V' E' _ _ _ I' hI'
  -- δ = 39/50, α_S' = 10, κ = 2, η' = 21
  have h94 := fun {V'' E'' : Type} [Fintype V''] [DecidableEq V''] [Fintype E'']
      (I'' : Instance V'' E'') (hI'' : I''.IsValid) (hirr : I''.IsIrreducible (39/50)) =>
    theorem_9_4 (39/50) (by norm_num) (by norm_num) 2 21 10 (by norm_num) (by norm_num)
      (fun I hI hS => singleton_tour_le_ten I hI hS)
      (fun I hI B hB => vertebrate_tour_bound I hI B hB) I'' hI'' hirr
  obtain ⟨F, hF, hwt⟩ := theorem_8_3 (39/50) (by norm_num) (by norm_num)
    ((2 + 21 * (1 - 39/50) + 10 + 3) / (2 * (39/50) - 1)) h94 I' hI'
  refine ⟨F, hF, le_trans hwt ?_⟩
  have hval : 0 ≤ I'.value := by
    unfold Instance.value Instance.valueOf
    have := hI'.2.2.2.2.2.2
    have : 0 ≤ ∑ R ∈ I'.L.filter (fun R => R ⊂ Finset.univ), I'.y R :=
      Finset.sum_nonneg (fun R hR => this R (Finset.mem_filter.1 hR).1)
    linarith
  apply mul_le_mul_of_nonneg_right _ hval
  norm_num
