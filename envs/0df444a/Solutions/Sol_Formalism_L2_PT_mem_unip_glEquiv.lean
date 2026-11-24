-- Prove2me | solution 1 for Formalism.L2.PT.mem_unip_glEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:31:12.873814+00:00
-- url     : https://prove2.me/submissions/a79a6819-80df-4378-b708-5f8b0582b375

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisConjCentralIdempotent
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_TypesDefs
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoeffZeroNeOfMonicIrr
import Theorems.Thm_Formalism_L2_PT_coe_glEquiv
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_L2_Host_restr_apply
import Theorems.Thm_Formalism_L2_NT_IsTeich_injective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.L2.Host.restr_apply



set_option autoImplicit false
noncomputable section
open Polynomial Formalism.IrreducibleCountingLemmas.TYPES CategoryTheory
open Formalism Formalism.L2 Formalism.L2.PT
open Polynomial CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
namespace Formalism.L2.PT
theorem _root_.solution {s : ℕ} (b : κ → Fin s) (e : ι ≃ κ) {u : GL ι K} (hu : u ∈ unip K (b ∘ e)) :
    glEquiv K e u ∈ unip K b := by
  obtain ⟨hp, hu2⟩ := hu
  refine ⟨?_, ?_⟩
  · unfold parab at hp ⊢
    obtain ⟨h1, h2⟩ := hp
    have key : ∀ M : Matrix ι ι K, IsBlockUT K (b ∘ e) M → IsBlockUT K b (Matrix.reindex e e M) := by
      intro M hM
      unfold IsBlockUT at *
      intro i j hij
      rw [Matrix.reindex_apply, Matrix.submatrix_apply]
      exact hM _ _ (by simpa using hij)
    show _ ∧ _
    refine ⟨?_, ?_⟩
    · rw [coe_glEquiv]
      exact key _ h1
    · rw [← map_inv, coe_glEquiv]
      exact key _ h2
  · intro i j hij
    rw [coe_glEquiv, Matrix.reindex_apply, Matrix.submatrix_apply, hu2 (e.symm i) (e.symm j) (by simpa using hij)]
    simp [e.symm.injective.eq_iff]
end Formalism.L2.PT
