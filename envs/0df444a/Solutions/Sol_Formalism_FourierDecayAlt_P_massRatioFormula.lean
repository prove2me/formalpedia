-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.massRatioFormula
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:38.068278+00:00
-- url     : https://prove2.me/submissions/161b4c05-78a8-4d88-8260-553cf5362f69

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz1_colIdx_ne_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_indexRatio
import Theorems.Thm_Formalism_FourierDecayAlt_P_factorialCancel
import Theorems.Thm_Formalism_FourierDecayAlt_P_volumeChain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Formalism.FourierDecayAlt.Sz Formalism.FourierDecayAlt.P.Sz1
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Sz.PropA := by
  intro ι _ S hOk hM hC
  have hvc := volumeChain ι S hOk hM
  have hkn : S.k ≤ S.n := by unfold SizeData.n SizeData.m; omega
  have hfac : ((∏ i ∈ Ico S.k S.n, i.factorial : ℕ) : ℝ) * (sfac S.k : ℝ) = (sfac S.n : ℝ) := by
    exact_mod_cast factorialCancel S.k S.n hkn
  have hg1 : (1 : ℝ) < S.g1 := by exact_mod_cast (lt_of_lt_of_le one_lt_two hOk.hg1)
  have hg2 : (1 : ℝ) < S.g2 := by exact_mod_cast (lt_of_lt_of_le one_lt_two hOk.hg2)
  have hT : (1 : ℝ) < S.T := by exact_mod_cast (lt_of_lt_of_le one_lt_two hOk.hT)
  have hi1 := indexRatio S.k S.r S.m S.n S.g1 rfl rfl hg1
  have hi2 := indexRatio S.k S.r S.m S.n S.g2 rfl rfl hg2
  have hc1 := colIdx_ne_zero S.k S.g1 hg1
  have hc2 := colIdx_ne_zero S.k S.g2 hg2
  rw [div_eq_iff hc1] at hi1
  rw [div_eq_iff hc2] at hi2
  have hsk : (sfac S.k : ℝ) ≠ 0 := by
    unfold sfac
    exact_mod_cast (Finset.prod_ne_zero_iff.mpr fun i _ => Nat.factorial_ne_zero i)
  have hTk : (1 : ℝ) < (S.T : ℝ) ^ S.k := one_lt_pow₀ hT (by have := hOk.hk; omega)
  have hTk0 : (S.T : ℝ) ^ S.k ≠ 0 := by linarith
  have hTk1 : (S.T : ℝ) ^ S.k - 1 ≠ 0 := by linarith
  have hVu : ∏ w, S.Vu w ≠ 0 := Finset.prod_ne_zero_iff.mpr fun w _ => (hOk.hVu w).ne'
  have hvol : S.vol S.k ≠ 0 := hOk.hvol.ne'
  have hdim : ∏ w, S.dimPi w = (∏ w, S.Vu w) / (sfac S.k : ℝ) ^ S.f := by
    unfold SizeData.dimPi SizeData.f
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ]
  have hprod : ∏ w, (S.TcritPow w / (S.T : ℝ) ^ S.k) =
      ((S.ka ^ ((S.m - 1) * S.k + S.m * (S.m - 1) / 2))⁻¹ * S.rd ^ (-(((S.m : ℝ) - 1) / 2)) *
        S.g ^ (S.k * S.m + S.m * (S.m - 1) / 2) * (sfac S.n : ℝ) / (S.T : ℝ) ^ S.k) ^ S.f *
        (∏ w, S.dsig w) / (∏ w, S.Vu w) := by
    have h : ∀ w ∈ (Finset.univ : Finset ι), S.TcritPow w / (S.T : ℝ) ^ S.k =
        ((S.ka ^ ((S.m - 1) * S.k + S.m * (S.m - 1) / 2))⁻¹ * S.rd ^ (-(((S.m : ℝ) - 1) / 2)) *
        S.g ^ (S.k * S.m + S.m * (S.m - 1) / 2) * (sfac S.n : ℝ) / (S.T : ℝ) ^ S.k) *
        S.dsig w / S.Vu w := by
      intro w _
      unfold SizeData.TcritPow Sz.TcritPow SizeData.VV
      ring
    rw [Finset.prod_congr rfl h, Finset.prod_div_distrib, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ]
    rfl
  have hT1 : (1 - ((S.T : ℝ) ^ S.k)⁻¹) = ((S.T : ℝ) ^ S.k - 1) / (S.T : ℝ) ^ S.k := by
    field_simp
  rw [hprod, hC, hdim]
  unfold SizeData.Dstar SizeData.Ea SizeData.idxRow SizeData.idxCol SizeData.g
  rw [hvc, hi1, hi2, hT1, ← hfac]
  generalize (S.ka ^ ((S.m - 1) * S.k + S.m * (S.m - 1) / 2))⁻¹ = A
  generalize S.rd ^ (-(((S.m : ℝ) - 1) / 2)) = B
  generalize ((∏ i ∈ Ico S.k S.n, i.factorial : ℕ) : ℝ) = F
  generalize (∏ M ∈ Ioc S.k S.n, S.Lv M) = L
  generalize (∏ j ∈ Ioc S.k S.n, (1 - (((S.g1 : ℝ)) ^ j)⁻¹)) = P1
  generalize (∏ j ∈ Ioc S.k S.n, (1 - (((S.g2 : ℝ)) ^ j)⁻¹)) = P2
  generalize (∏ w, S.dsig w) = D
  generalize (∏ w, S.Vu w) = V at hVu ⊢
  generalize colIdx S.k (S.g1 : ℝ) = c1 at hc1 ⊢
  generalize colIdx S.k (S.g2 : ℝ) = c2 at hc2 ⊢
  generalize (sfac S.k : ℝ) = s at hsk ⊢
  generalize (S.T : ℝ) ^ S.k = t at hTk0 hTk1 ⊢
  generalize S.vol S.k = v0 at hvol ⊢
  generalize S.k * S.m + S.m * (S.m - 1) / 2 = e
  simp only [mul_pow, div_pow]
  field_simp
end Formalism.FourierDecayAlt.P
