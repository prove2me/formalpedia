-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.TW.hecke_determinant_factors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:00:54.631825+00:00
-- url     : https://prove2.me/submissions/bc3681c5-1d8a-4414-a581-ff865d6ee58a

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_CentralIdempotentIntegral
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_TWHeckeDetFactors
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_prod_one_sub_inv_mul_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.TW
namespace Formalism.IrreducibleCountingLemmas.TW
theorem _root_.solution : HeckeDetFactors := by
  intro k _ _ d r A hA
  classical
  set M : Matrix (Fin d) (Fin d) k[X] :=
    ∑ j : Fin (r + 1), (X : k[X]) ^ (j : ℕ) • (A j).map C with hM
  have hentry : ∀ a b, (M a b).natDegree ≤ r := by
    intro a b
    rw [hM, Matrix.sum_apply]
    refine natDegree_sum_le_of_forall_le _ _ (fun j _ => ?_)
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    refine (natDegree_mul_C_le _ _).trans ?_
    rw [natDegree_X_pow]
    omega
  have hdeg : M.det.natDegree ≤ r * d := by
    rw [Matrix.det_apply]
    refine natDegree_sum_le_of_forall_le _ _ (fun g _ => ?_)
    have h1 : natDegree (Equiv.Perm.sign g • ∏ i, M (g i) i) ≤ natDegree (∏ i, M (g i) i) := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign g) with sg | sg
      · rw [sg, one_smul]
      · rw [sg, Units.neg_smul, one_smul, natDegree_neg]
    refine h1.trans ((natDegree_prod_le _ _).trans ?_)
    refine (Finset.sum_le_card_nsmul _ _ r (fun i _ => hentry _ _)).trans ?_
    simp [mul_comm]
  have h0 : M.det.eval 0 = 1 := by
    have h1 : (evalRingHom (0 : k)) M.det = ((evalRingHom (0 : k)).mapMatrix M).det :=
      RingHom.map_det _ _
    have hm : (evalRingHom (0 : k)).mapMatrix M = 1 := by
      rw [← hA]
      ext a b
      simp [hM, Matrix.sum_apply, eval_finsetSum, Fin.sum_univ_succ]
    rw [hm, Matrix.det_one] at h1
    simpa using h1
  have hne : M.det ≠ 0 := by
    intro h; rw [h] at h0; simp at h0
  have hs := IsAlgClosed.splits M.det
  have hfac := hs.eq_prod_roots
  have hev := hs.eval_eq_prod_roots 0
  rw [h0] at hev
  have hnz : ∀ a ∈ M.det.roots, a ≠ 0 := by
    intro a ha h
    have := (mem_roots hne).1 ha
    rw [h, IsRoot.def, h0] at this
    exact one_ne_zero this
  have haux := prod_one_sub_inv_mul_X M.det.roots hnz
  have hfin : M.det = (M.det.roots.map (fun a => (1 : k[X]) - C a⁻¹ * X)).prod := by
    conv_lhs => rw [hfac]
    rw [← haux, mul_comm, mul_assoc, ← C_mul, mul_comm _ M.det.leadingCoeff, ← hev, C_1, mul_one]
  refine ⟨M.det.roots.toList.length, fun i => (M.det.roots.toList[i.1])⁻¹, ?_, ?_⟩
  · rw [Multiset.length_toList]
    exact (card_roots' _).trans hdeg
  · rw [Fin.prod_univ_fun_getElem M.det.roots.toList (fun a => (1 : k[X]) - C a⁻¹ * X),
      ← Multiset.prod_coe, ← Multiset.map_coe, Multiset.coe_toList]
    exact hfin
end Formalism.IrreducibleCountingLemmas.TW
