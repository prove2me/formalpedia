-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.inert_euler_holomorphic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:07:31.383178+00:00
-- url     : https://prove2.me/submissions/6ba50378-cd41-4768-be2f-a120f9703607

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_FactorOverLocalSubalgebraMonic
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZReuse
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZCircleCharExtends
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_FactorOverLocalSubalgebra
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CharpolyFactorAnnihilator
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZGoodCuspidal
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbitt
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CardLtAddCardGtAddCardEq
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_inertFactor_sub_one_le
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_inertFactor_differentiableAt
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_Equi_trans
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_BN_Kills_mul_left
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_glue_castAdd
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_glue_natAdd
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_shuffle_castAdd
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_shuffle_natAdd
import Theorems.Thm_P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_zero
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_zero
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.glue_castAdd
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.glue_natAdd
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.shuffle_castAdd
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.shuffle_natAdd
attribute [local simp] P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8



set_option autoImplicit false
open Polynomial Filter Topology
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.Z
namespace Formalism.IrreducibleCountingLemmas.Z
theorem _root_.solution : InertEulerHolomorphic := by
  intro ι q ch hq hch hsum s hs
  have hs : 1 / 2 < s.re := hs
  obtain ⟨σ₀, h1, h2⟩ : ∃ σ₀ : ℝ, 1 / 2 < σ₀ ∧ σ₀ < s.re := exists_between hs
  let K : Set ℂ := {z | σ₀ < z.re}
  have hK : IsOpen K := isOpen_lt continuous_const Complex.continuous_re
  have hKd : ∀ v, DifferentiableOn ℂ (fun z => inertFactor (q v) (ch v) z) K := fun v z hz =>
    (inertFactor_differentiableAt (q v) (ch v) z (hq v) (hch v)
      (lt_trans h1 hz)).differentiableWithinAt
  have hprod := ((hsum σ₀ h1).mul_left 4).hasProdLocallyUniformlyOn_one_add
    (f := fun v z => inertFactor (q v) (ch v) z - 1) hK
    (.of_forall fun v z hz => by
      have hz' : σ₀ < z.re := hz
      refine (inertFactor_sub_one_le (q v) (ch v) z (hq v) (hch v) (lt_trans h1 hz')).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      exact Real.rpow_le_rpow_of_exponent_le (by linarith [hq v]) (by linarith))
    (fun v => ((hKd v).sub (differentiableOn_const _)).continuousOn)
  have hd : DifferentiableOn ℂ (fun z => ∏' v, (1 + (inertFactor (q v) (ch v) z - 1))) K :=
    hprod.differentiableOn (.of_forall fun _ => by
      simpa [Finset.prod_fn] using DifferentiableOn.finsetProd (fun v _ => hKd v)) hK
  have h3 := hd.differentiableAt (hK.mem_nhds h2)
  simp only [add_sub_cancel] at h3
  exact h3.differentiableWithinAt
end Formalism.IrreducibleCountingLemmas.Z
