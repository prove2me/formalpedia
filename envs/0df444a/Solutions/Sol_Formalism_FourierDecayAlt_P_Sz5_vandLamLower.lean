-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz5.vandLamLower
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:49:33.55833+00:00
-- url     : https://prove2.me/submissions/36b66e7a-56c2-43b9-820d-053a070d69d9

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CriticalThresholdLowerBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_vand_split
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_v_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_vand_v_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_b_step
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_b_ge_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_one_le_prod_real
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_prodb_ge_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz5
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz5
theorem _root_.solution : VandLamLower := by
  intro c h
  have hk := h.hk
  have hkm : c.k + c.m - 1 = (c.k - 1) + c.m := by omega
  have vcongr : ∀ (p : ℕ) (x y : ℕ → ℝ), (∀ i, 1 ≤ i → i ≤ p → x i = y i) → Vand p x = Vand p y := by
    intro p x y hxy
    unfold Vand
    apply Finset.prod_congr rfl
    intro i hi
    apply Finset.prod_congr rfl
    intro j hj
    rw [Finset.mem_Icc] at hi
    rw [Finset.mem_Ioc] at hj
    rw [hxy i hi.1 hi.2, hxy j (by omega) hj.2]
  have hlam1 : ∀ i, i ≤ c.k - 1 → c.lam i = c.v i := by
    intro i hi
    have hi' : i < c.k := by omega
    simp only [Cfg.lam, if_pos hi']
  have hlam2 : ∀ j, 1 ≤ j → c.lam (j + (c.k - 1)) = -c.b j := by
    intro j hj
    have h1 : ¬ (j + (c.k - 1) < c.k) := by omega
    have h2 : j + (c.k - 1) + 1 - c.k = j := by omega
    simp only [Cfg.lam, if_neg h1, h2]
  have eqn : Vand (c.k + c.m - 1) c.lam = Vand (c.k - 1) c.v *
      (∏ i ∈ Icc 1 (c.k - 1), ∏ j ∈ Icc 1 c.m, (c.v i + c.b j)) * Vand c.m (fun j => -c.b j) := by
    rw [hkm, vand_split (c.k - 1) c.m c.lam]
    have e1 : Vand (c.k - 1) c.lam = Vand (c.k - 1) c.v :=
      vcongr _ _ _ (fun i _ hi2 => hlam1 i hi2)
    have e2 : Vand c.m (fun j => c.lam (j + (c.k - 1))) = Vand c.m (fun j => -c.b j) :=
      vcongr _ _ _ (fun j hj1 _ => hlam2 j hj1)
    have e3 : ∏ i ∈ Icc 1 (c.k - 1), ∏ j ∈ Icc 1 c.m, (c.lam i - c.lam (j + (c.k - 1)))
        = ∏ i ∈ Icc 1 (c.k - 1), ∏ j ∈ Icc 1 c.m, (c.v i + c.b j) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [Finset.mem_Icc] at hi
      apply Finset.prod_congr rfl
      intro j hj
      rw [Finset.mem_Icc] at hj
      rw [hlam1 i hi.2, hlam2 j hj.1]
      ring
    rw [e1, e2, e3]
  refine ⟨eqn, ?_⟩
  have hC : c.prodb ^ (c.k - 1) ≤ ∏ i ∈ Icc 1 (c.k - 1), ∏ j ∈ Icc 1 c.m, (c.v i + c.b j) := by
    calc c.prodb ^ (c.k - 1) = ∏ i ∈ Icc 1 (c.k - 1), ∏ j ∈ Icc 1 c.m, c.b j := by
          first
          | (rw [Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel]; done)
          | (rw [Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel]; rfl)
          | (unfold Cfg.prodb; rw [Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel])
      _ ≤ ∏ i ∈ Icc 1 (c.k - 1), ∏ j ∈ Icc 1 c.m, (c.v i + c.b j) := by
          apply Finset.prod_le_prod
          · intro i _
            apply Finset.prod_nonneg
            intro j hj
            rw [Finset.mem_Icc] at hj
            linarith [b_ge_one c h j hj.1 hj.2]
          · intro i hi
            rw [Finset.mem_Icc] at hi
            apply Finset.prod_le_prod
            · intro j hj
              rw [Finset.mem_Icc] at hj
              linarith [b_ge_one c h j hj.1 hj.2]
            · intro j _
              linarith [v_nonneg c h i (by omega)]
  have hV : 1 ≤ Vand c.m (fun j => -c.b j) := by
    unfold Vand
    apply one_le_prod_real
    intro i hi
    rw [Finset.mem_Icc] at hi
    apply one_le_prod_real
    intro j hj
    rw [Finset.mem_Ioc] at hj
    have hb := b_step c h i hi.1 j hj.1 hj.2
    show (1:ℝ) ≤ -c.b i - -c.b j
    linarith
  have hv := vand_v_pos c h (c.k - 1)
  have hpb := prodb_ge_one c h
  have hC0 : 0 ≤ ∏ i ∈ Icc 1 (c.k - 1), ∏ j ∈ Icc 1 c.m, (c.v i + c.b j) :=
    le_trans (pow_nonneg (by linarith) _) hC
  rw [eqn]
  calc Vand (c.k - 1) c.v * c.prodb ^ (c.k - 1)
      ≤ Vand (c.k - 1) c.v * ∏ i ∈ Icc 1 (c.k - 1), ∏ j ∈ Icc 1 c.m, (c.v i + c.b j) :=
        mul_le_mul_of_nonneg_left hC hv.le
    _ = Vand (c.k - 1) c.v * (∏ i ∈ Icc 1 (c.k - 1), ∏ j ∈ Icc 1 c.m, (c.v i + c.b j)) * 1 :=
        (mul_one _).symm
    _ ≤ Vand (c.k - 1) c.v * (∏ i ∈ Icc 1 (c.k - 1), ∏ j ∈ Icc 1 c.m, (c.v i + c.b j)) *
          Vand c.m (fun j => -c.b j) :=
        mul_le_mul_of_nonneg_left hV (mul_nonneg hv.le hC0)
end Formalism.FourierDecayAlt.P.Sz5
