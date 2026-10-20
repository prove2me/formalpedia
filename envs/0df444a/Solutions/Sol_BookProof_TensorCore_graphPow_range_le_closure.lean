-- Prove2me | solution 1 for BookProof.TensorCore.graphPow_range_le_closure
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:12:11.193156+00:00
-- url     : https://prove2.me/submissions/9759c366-94bf-41b8-8e79-ba638ef955ea

-- Generated from ChapterTensorGraphCore.lean — solution of BookProof.TensorCore.graphPow_range_le_closure
import Mathlib
import Definitions.Def_ChapterTensorGraphCore
import Theorems.Thm_BookProof_TensorCore_graphPow_tmul_mem_closure
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
open BookProof.TensorCore




open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier)
variable (A : D₂ →ₗ[ℂ] Hs.carrier)
variable (D : Submodule ℂ Hs.carrier)

set_option maxHeartbeats 1000000 in
theorem solution (hcore : IsGraphCore D A) (n : ℕ) :
    LinearMap.range (graphPow Hs D₂ A n)
      ≤ (Submodule.map (graphPow Hs D₂ A n) (corePow Hs D₂ D n)).topologicalClosure := by

  induction n with
  | zero =>
      have h0 : corePow Hs D₂ D 0 = ⊤ := rfl
      rw [h0, Submodule.map_top]
      exact Submodule.le_topologicalClosure _
  | succ n ih =>
      rintro y ⟨x, rfl⟩
      have hx : x ∈ Submodule.span ℂ
          {t : (D₂ ⊗[ℂ] ((domSpace Hs D₂).pow n).carrier) |
            ∃ (p : D₂) (q : ((domSpace Hs D₂).pow n)), p ⊗ₜ[ℂ] q = t} := by
        rw [TensorProduct.span_tmul_eq_top]; trivial
      induction hx using Submodule.span_induction with
      | mem t ht =>
          obtain ⟨p, q, rfl⟩ := ht
          exact graphPow_tmul_mem_closure Hs D₂ A D hcore n (fun c => ih ⟨c, rfl⟩) p q
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | add s t _ _ hs ht => rw [map_add]; exact Submodule.add_mem _ hs ht
      | smul c s _ hs => rw [map_smul]; exact Submodule.smul_mem _ c hs
