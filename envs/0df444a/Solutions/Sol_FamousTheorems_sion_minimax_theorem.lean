-- Prove2me | solution 1 for FamousTheorems.sion_minimax_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:20:15.446326+00:00
-- url     : https://prove2.me/submissions/e589d9f9-38ea-461c-87f2-fbcc834e7d4c

import Mathlib

theorem solution {E F β : Type*} [LinearOrder β] [DenselyOrdered β] [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] {X : Set E} {Y : Set F} {f : E → F → β}
    (hX_ne : X.Nonempty) (hX_cpt : IsCompact X) (hX : Convex ℝ X) (hY : Convex ℝ Y)
    (hfy_lsc : ∀ y ∈ Y, LowerSemicontinuousOn (fun x => f x y) X) (hfy_qcvx : ∀ y ∈ Y, QuasiconvexOn ℝ X fun x => f x y)
    (hfx_usc : ∀ x ∈ X, UpperSemicontinuousOn (fun y => f x y) Y) (hfx_qccv : ∀ x ∈ X, QuasiconcaveOn ℝ Y fun y => f x y)
    (sup_y : E → β) (h_sup_y : ∀ x ∈ X, IsLUB {b | ∃ y ∈ Y, f x y = b} (sup_y x))
    (inf_sup : β) (h_inf_sup : IsGLB {b | ∃ x ∈ X, sup_y x = b} inf_sup)
    (inf_x : F → β) (h_inf_x : ∀ y ∈ Y, IsGLB {b | ∃ x ∈ X, f x y = b} (inf_x y))
    (sup_inf : β) (h_sup_inf : IsLUB {b | ∃ y ∈ Y, inf_x y = b} sup_inf) : inf_sup = sup_inf :=
  Sion.minimax hX_ne hX_cpt hfy_lsc hfy_qcvx hY hfx_usc hfx_qccv hX sup_y h_sup_y inf_sup h_inf_sup inf_x h_inf_x sup_inf h_sup_inf
