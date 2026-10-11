-- Prove2me | solution 1 for BookProof.TwoParticleSector.swapDom_mem_corePow
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:35:02.050654+00:00
-- url     : https://prove2.me/submissions/d33cdad7-af15-4875-ad3c-694015729b15

-- Generated from ChapterTwoParticleSectorEsa.lean — solution of BookProof.TwoParticleSector.swapDom_mem_corePow
import Mathlib
import Definitions.Def_ChapterTwoParticleSectorEsa
import Theorems.Thm_BookProof_TensorCore_tmul_mem_corePow
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterTensorGraphCore
open BookProof.TwoParticleSector




open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore

noncomputable section

variable (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X]
variable {X}
variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier)
variable (A : D₂ →ₗ[ℂ] Hs.carrier)
variable (D : Submodule ℂ Hs.carrier)

set_option maxHeartbeats 1000000 in
theorem solution {t : ((domSpace Hs D₂).pow 2).carrier}
    (ht : t ∈ corePow Hs D₂ D 2) : swapDom Hs D₂ t ∈ corePow Hs D₂ D 2 := by

  induction ht using Submodule.span_induction with
  | mem u hu =>
      obtain ⟨a, haD, b, hb, rfl⟩ := hu
      -- `b` lies in the one-particle core power, which is spanned by `b' ⊗ c`
      induction hb using Submodule.span_induction with
      | mem v hv =>
          obtain ⟨b', hb'D, c, -, rfl⟩ := hv
          rw [swapDom_tmul]
          exact tmul_mem_corePow Hs D₂ D hb'D
            (tmul_mem_corePow Hs D₂ D haD (by trivial))
      | zero => simp
      | add s s' _ _ hs hs' =>
          rw [TensorProduct.tmul_add, map_add]
          exact Submodule.add_mem _ hs hs'
      | smul r s _ hs =>
          rw [TensorProduct.tmul_smul, map_smul]
          exact Submodule.smul_mem _ r hs
  | zero => simp
  | add u v _ _ hu hv => rw [map_add]; exact Submodule.add_mem _ hu hv
  | smul r u _ hu => rw [map_smul]; exact Submodule.smul_mem _ r hu
