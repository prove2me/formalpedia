-- Prove2me | solution 1 for Formalism.L2.PT.hasCuspLabel_transp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:36:26.415226+00:00
-- url     : https://prove2.me/submissions/2d3b74d2-aa16-4cd7-8383-098ac9d8e167

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisConjCentralIdempotent
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_TypesDefs
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoeffZeroNeOfMonicIrr
import Theorems.Thm_Formalism_L2_PT_coe_glEquiv_symm
import Theorems.Thm_P2M_Formalism_L2_PT_transp___1b8910838bef
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_L2_Host_restr_apply
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
theorem _root_.solution (cv : LabelConv K) (e : ι ≃ κ) {τ : FDRep ℂ (GL ι K)} {P : K[X]}
    (h : HasCuspLabel cv τ P) : HasCuspLabel cv (transp e τ) P := by
  unfold HasCuspLabel at *
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hc : Fintype.card κ = Fintype.card ι := (Fintype.card_congr e).symm
  refine ⟨h1, h2, h3, by rw [h4, hc], ?_⟩
  intro x hx γ hγ z hz m hm
  have hcp : (((glEquiv K e).symm γ : GL ι K) : Matrix ι ι K).charpoly = (γ : Matrix κ κ K).charpoly := by
    first
      | rw [coe_glEquiv_symm, Matrix.charpoly_reindex]
      | simp [coe_glEquiv_symm, Matrix.charpoly_reindex]
  rw [hc] at hm ⊢
  have key := h5 x hx ((glEquiv K e).symm γ) (by rw [hcp]; exact hγ) z (by rw [hcp]; exact hz) m hm
  first
    | (rw [transp_ρ]; exact key)
    | exact key
    | simpa [transp_ρ] using key
end Formalism.L2.PT
