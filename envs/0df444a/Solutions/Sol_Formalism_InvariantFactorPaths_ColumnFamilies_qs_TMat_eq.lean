-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qs_TMat_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:23:35.631292+00:00
-- url     : https://prove2.me/submissions/ac0d905f-8ab0-47e8-b2bd-1fecfef93064

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsRemIffAdd
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsSymDMatEq
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHHigh
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_ext_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_minorC_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_mn_univ
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_mn_empty

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {mu : Fin n → ℤ} (hmu : Dominant mu) (lo hi : ℤ) (h1 : lo ≤ mu (lastIdx n)) (h2 : mu 0 ≤ hi)
    (J I : TIdx mu) : TMat mu J I = qs_TM lo (Finset.Ioc lo hi) (qs_ext mu J) (qs_ext mu I) := by
  have h0 : mu (lastIdx n) ≤ mu 0 := hmu (Fin.zero_le _)
  have hS : Finset.Ioc lo hi = Finset.Ioc lo (mu (lastIdx n)) ∪ (TCols mu ∪ Finset.Ioc (mu 0) hi) := by
    rw [TCols, Finset.Ioc_union_Ioc_eq_Ioc h0 h2, Finset.Ioc_union_Ioc_eq_Ioc h1 (h0.trans h2)]
  have hA : ∏ c ∈ Finset.Ioc lo (mu (lastIdx n)), qs_mn (qs_gC n) (qs_ext mu J c) (qs_ext mu I c) =
      ((detU n : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) ^ (mu (lastIdx n) - lo).toNat := by
    rw [← Int.card_Ioc, ← Finset.prod_const]
    refine Finset.prod_congr rfl fun c hc => ?_
    have hc2 : c ≤ mu (lastIdx n) := (Finset.mem_Ioc.1 hc).2
    have hc1 : c ∉ TCols mu := by simp only [TCols, mem_Ioc]; omega
    simp only [qs_ext, dif_neg hc1, if_pos hc2, qs_mn_univ]
  have hB : ∏ c ∈ TCols mu, qs_mn (qs_gC n) (qs_ext mu J c) (qs_ext mu I c) =
      ∏ c : ↥(TCols mu), minorC (J c).1 (I c).1 (J c).2 (I c).2 := by
    rw [← Finset.prod_coe_sort]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [qs_ext_mem, qs_ext_mem, qs_minorC_eq]
  have hC : ∏ c ∈ Finset.Ioc (mu 0) hi, qs_mn (qs_gC n) (qs_ext mu J c) (qs_ext mu I c) = 1 := by
    refine Finset.prod_eq_one fun c hc => ?_
    have hc2 : mu 0 < c := (Finset.mem_Ioc.1 hc).1
    have hc1 : c ∉ TCols mu := by simp only [TCols, mem_Ioc]; omega
    have hc3 : ¬ c ≤ mu (lastIdx n) := by omega
    simp only [qs_ext, dif_neg hc1, if_neg hc3, qs_mn_empty]
  have hU : detU n ^ mu (lastIdx n) = detU n ^ lo * detU n ^ (mu (lastIdx n) - lo).toNat := by
    rw [← zpow_natCast, ← zpow_add, Int.toNat_of_nonneg (by omega)]; congr 1; omega
  rw [qs_TM, hS, Finset.prod_union, Finset.prod_union, hA, hB, hC, TMat, hU, Units.val_mul, Units.val_pow_eq_pow_val]
  · ring
  · refine Finset.disjoint_left.2 fun x hx hx' => ?_
    simp only [TCols, mem_Ioc] at hx hx'; omega
  · refine Finset.disjoint_left.2 fun x hx hx' => ?_
    simp only [TCols, mem_Ioc, mem_union] at hx hx'; omega
end Formalism.InvariantFactorPaths.ColumnFamilies
