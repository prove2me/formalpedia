-- Prove2me | solution 1 for Formalism.L2.PT.simple_transp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:31:21.46489+00:00
-- url     : https://prove2.me/submissions/48f06cfa-929e-48d1-aa7b-edb9ebd69ae2

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisConjCentralIdempotent
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_TypesDefs
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoeffZeroNeOfMonicIrr
import Theorems.Thm_Formalism_L2_PT_character_transp
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
theorem _root_.solution (e : ι ≃ κ) {τ : FDRep ℂ (GL ι K)} (h : Simple τ) : Simple (transp e τ) := by
  rw [FDRep.simple_iff_char_is_norm_one] at h ⊢
  have hc : Fintype.card (GL κ K) = Fintype.card (GL ι K) := Fintype.card_congr (glEquiv K e).symm.toEquiv
  have hs : ∑ g : GL κ K, (transp e τ).character g * (transp e τ).character g⁻¹ =
      ∑ g : GL ι K, τ.character g * τ.character g⁻¹ := by
    simp only [character_transp]
    symm
    refine Fintype.sum_equiv (glEquiv K e).toEquiv _ _ (fun g => ?_)
    first
      | simp
      | simp [map_inv]
      | rfl
  rw [hs]
  first
    | (rw [hc]; exact h)
    | (simp only [hc]; exact h)
    | (simp only [invOf_eq_inv] at h ⊢; rw [hc]; exact h)
    | (convert h using 3; simp [hc])
    | (convert h using 2; simp [hc])
end Formalism.L2.PT
