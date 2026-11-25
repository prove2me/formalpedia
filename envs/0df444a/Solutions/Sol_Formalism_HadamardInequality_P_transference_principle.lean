-- Prove2me | solution 1 for Formalism.HadamardInequality.P.transference_principle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:15:36.211905+00:00
-- url     : https://prove2.me/submissions/c514cec9-5c3d-4d5e-9897-a290cbc259f4

import Definitions.Def_Formalism_GelfandTransference_EnergyIdentity
import Definitions.Def_Formalism_NormUnitaryBounds_NormUnitary
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ShortIndependentVectorsOfDualMinimum
import Definitions.Def_Formalism_LatticeTheta_ThetaShiftInversion
import Definitions.Def_Formalism_GelfandTransference_HadamardGelfand_Transference
import Theorems.Thm_Formalism_HadamardInequality_P_tr_chain
import Theorems.Thm_Formalism_HadamardInequality_P_tr_dual
import Theorems.Thm_Formalism_HadamardInequality_P_tr_succMin_le
import Theorems.Thm_Formalism_HadamardInequality_P_tr_succMin_nonneg
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_Final_h1
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_Final_h2
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HadamardInequality Formalism.HadamardInequality.P
namespace Formalism.HadamardInequality.P
theorem _root_.solution : Formalism.HadamardInequality.Transference := by
  intro E _ _ _ M hMd hspan i hi1 hin
  set n := finrank ℝ E with hn
  set k := n + 1 - i with hk
  have hkn : k ≤ n := by omega
  have hk1 : 1 ≤ k := by omega
  obtain ⟨b, t, hbM, hli, ht0, hbn, hWs, -⟩ := tr_chain M hspan k hkn
  obtain ⟨j0, -, hj0⟩ := Finset.exists_max_image Finset.univ t
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  set T := t j0 with hT
  have hTpos : 0 < T := ht0 j0
  have htT : ∀ l, t l ^ 2 ≤ T ^ 2 := fun l =>
    pow_le_pow_left₀ (ht0 l).le (hj0 l (Finset.mem_univ _)) 2
  have hS : ∑ l, t l ^ 2 ≤ (k : ℝ) * T ^ 2 := by
    calc ∑ l, t l ^ 2 ≤ ∑ _l : Fin k, T ^ 2 := Finset.sum_le_sum fun l _ => htT l
      _ = (k : ℝ) * T ^ 2 := by simp
  set R := Real.sqrt (((k : ℝ) + 3) / 4 * T ^ 2) with hR
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hbR : ∀ j, ‖b j‖ ≤ R := by
    intro j
    have h1 := hbn j
    have h2 := htT j
    have h3 : ‖b j‖ ^ 2 ≤ ((k : ℝ) + 3) / 4 * T ^ 2 := by nlinarith
    have := Real.abs_le_sqrt h3
    rwa [abs_of_nonneg (norm_nonneg _)] at this
  have hMk : Formalism.HadamardInequality.succMin M k ≤ R := tr_succMin_le M b hbM hli hR0 hbR
  obtain ⟨W, hWr, hWm⟩ := hWs j0
  obtain ⟨y, hyD, hyli, hyn⟩ := tr_dual M hspan W hTpos hWm
  have hfr : finrank ℝ W + finrank ℝ Wᗮ = n := Submodule.finrank_add_finrank_orthogonal W
  have hj0k := j0.2
  have hij : i ≤ finrank ℝ Wᗮ := by omega
  have hWn : finrank ℝ Wᗮ ≤ n := by omega
  set A := (n : ℝ) ^ ((3 : ℝ) / 2) / T with hA
  have hA0 : 0 ≤ A := by positivity
  have hyA : ∀ j, ‖y (Fin.castLE hij j)‖ ≤ A := by
    intro j
    refine (hyn _).trans (div_le_div_of_nonneg_right ?_ hTpos.le)
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hWn) (by norm_num)
  have hDi : Formalism.HadamardInequality.succMin (Formalism.HadamardInequality.zdual M) i ≤ A :=
    tr_succMin_le _ (fun j => y (Fin.castLE hij j)) (fun j => hyD _)
      (hyli.comp _ (Fin.castLE_injective hij)) hA0 hyA
  have hAR : A * R ≤ (n : ℝ) ^ 2 := by
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hA2 : A ^ 2 = (n : ℝ) ^ 3 / T ^ 2 := by
      rw [hA, div_pow, ← Real.rpow_natCast ((n : ℝ) ^ ((3 : ℝ) / 2)) 2, ← Real.rpow_mul hn0]
      norm_num
    have hR2 : R ^ 2 = ((k : ℝ) + 3) / 4 * T ^ 2 := Real.sq_sqrt (by positivity)
    have hk' : (k : ℝ) ≤ n := by exact_mod_cast hkn
    rw [← pow_le_pow_iff_left₀ (mul_nonneg hA0 hR0) (by positivity) two_ne_zero]
    rw [mul_pow, hA2, hR2]
    have e : (n : ℝ) ^ 3 / T ^ 2 * (((k : ℝ) + 3) / 4 * T ^ 2) =
        (n : ℝ) ^ 3 * (((k : ℝ) + 3) / 4) := by
      field_simp
    rw [e]
    have h4 : ((k : ℝ) + 3) / 4 ≤ n := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk1
      linarith
    calc (n : ℝ) ^ 3 * (((k : ℝ) + 3) / 4) ≤ (n : ℝ) ^ 3 * n :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = ((n : ℝ) ^ 2) ^ 2 := by ring
  calc Formalism.HadamardInequality.succMin (Formalism.HadamardInequality.zdual M) i * Formalism.HadamardInequality.succMin M k ≤ A * R :=
        mul_le_mul hDi hMk (tr_succMin_nonneg _ _) hA0
    _ ≤ (n : ℝ) ^ 2 := hAR
end Formalism.HadamardInequality.P
