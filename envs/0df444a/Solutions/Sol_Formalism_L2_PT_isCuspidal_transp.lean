-- Prove2me | solution 1 for Formalism.L2.PT.isCuspidal_transp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:48:53.935066+00:00
-- url     : https://prove2.me/submissions/24843d30-b4b0-419e-98d5-e81457d7a23e

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisConjCentralIdempotent
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_TypesDefs
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoeffZeroNeOfMonicIrr
import Theorems.Thm_P2M_Formalism_L2_PT_transp___1b8910838bef
import Theorems.Thm_Formalism_L2_PT_mem_unip_glEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Formalism.IrreducibleCountingLemmas.TYPES CategoryTheory
open Formalism Formalism.L2 Formalism.L2.PT
open Polynomial CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
namespace Formalism.L2.PT
theorem _root_.solution (e : ι ≃ κ) {τ : FDRep ℂ (GL ι K)} (h : IsCuspidal K τ) :
    IsCuspidal K (transp e τ) := by
  intro s b hb hs v hv
  exact h s (b ∘ e) (hb.comp e.surjective) hs v (fun u hu => by
    have := hv _ (mem_unip_glEquiv b e hu)
    rwa [transp_ρ, MulEquiv.symm_apply_apply] at this)
end Formalism.L2.PT
