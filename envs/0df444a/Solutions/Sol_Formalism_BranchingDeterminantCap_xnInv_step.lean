-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.xnInv_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:47:57.198993+00:00
-- url     : https://prove2.me/submissions/b66fa9b6-1024-40c6-ab2b-9d0b439d8703

import Mathlib
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockbLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylNonDom
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_XiNorm
import Theorems.Thm_Formalism_BranchingDeterminantCap_xn_det_supported
import Theorems.Thm_Formalism_BranchingDeterminantCap_xn_U
import Theorems.Thm_Formalism_BranchingDeterminantCap_xn_L
import Theorems.Thm_Formalism_BranchingDeterminantCap_xn_hR
import Theorems.Thm_Formalism_BranchingDeterminantCap_xn_hW
import Theorems.Thm_Formalism_BranchingDeterminantCap_xn_sum_rows
import Theorems.Thm_Formalism_BranchingDeterminantCap_xn_W_ratio
import Theorems.Thm_Formalism_BranchingDeterminantCap_xnC_nonneg
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeyl_mul
import Theorems.Thm_Formalism_GradedWeylDivisibility_initMinor_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.REAL
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
variable {r n : ℕ}
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution {k : ℕ} {μ : ℕ → ℕ} {x h : MvPolynomial (Fin r × Fin n) ℂ} (H : xnInv k μ x h)
    (hk : k ≤ n) (hkr : k ≤ r) (J : Fin k → Fin r) (hJ : Function.Injective J) :
    xnInv k (xnAdd μ k) (initMinor ℂ J hk * x) (lpMinor ℂ k hkr hk * h) := by
  have hw : initW n k + (fun q : Fin n => μ q.val) = fun q : Fin n => xnAdd μ k q.val := by
    funext q
    simp only [initW, xnAdd, Pi.add_apply]
    split_ifs <;> omega
  have hL0 : lpMinor ℂ k hkr hk = initMinor ℂ (Fin.castLE hkr) hk := rfl
  have hLm : lpMinor ℂ k hkr hk ∈ dualWeyl ℂ r n (initW n k) := by
    rw [hL0]
    exact initMinor_mem _ _
  have hRx : ∀ t s : Fin n, t < s →
      ∑ b : Fin r, X ((id : Fin r → Fin r) b, t) * pderiv ((id : Fin r → Fin r) b, s) x = 0 :=
    fun t s hts => xn_hR H.xm t s hts
  have hWx : ∀ s : Fin n, ∑ b : Fin r, X ((id : Fin r → Fin r) b, s) *
      pderiv ((id : Fin r → Fin r) b, s) x = C ((μ s.val : ℕ) : ℂ) * x :=
    fun s => xn_hW H.xm s
  have hRh : ∀ t s : Fin n, t < s →
      ∑ b : Fin k, X (Fin.castLE hkr b, t) * pderiv (Fin.castLE hkr b, s) h = 0 :=
    fun t s hts => by
      rw [xn_sum_rows hkr H.hs]
      exact xn_hR H.hm t s hts
  have hWh : ∀ s : Fin n, ∑ b : Fin k, X (Fin.castLE hkr b, s) * pderiv (Fin.castLE hkr b, s) h =
      C ((μ s.val : ℕ) : ℂ) * h :=
    fun s => by
      rw [xn_sum_rows hkr H.hs]
      exact xn_hW H.hm s
  have hU := xn_U (id : Fin r → Fin r) Function.injective_id μ x hRx hWx k hk J hJ
  rw [Fintype.card_fin] at hU
  have hLeq := xn_L (Fin.castLE hkr) (Fin.castLE_injective hkr) μ h hRh hWh hk
  rw [← hL0] at hLeq
  have hR := xn_W_ratio r μ k hkr H.supp
  have hC := xnC_nonneg r μ k hkr
  refine ⟨fun q hq => ?_, ?_, ?_, ?_, ?_⟩
  · simp only [xnAdd, if_neg (show ¬ q < k by omega), Nat.add_zero]
    exact H.supp q hq
  · rw [← hw]
    exact dualWeyl_mul (initMinor_mem J hk) H.xm
  · rw [← hw]
    exact dualWeyl_mul hLm H.hm
  · refine mul_mem ?_ H.hs
    rw [hL0]
    unfold initMinor
    refine xn_det_supported _ _ fun i j => ?_
    rw [Matrix.of_apply]
    first
    | exact (MvPolynomial.X_mem_supported (R := ℂ)).2 (show (Fin.castLE hkr i).val < k from i.isLt)
    | exact MvPolynomial.X_mem_supported.mpr (show (Fin.castLE hkr i).val < k from i.isLt)
  · rw [hLeq]
    calc xnN (initMinor ℂ J hk * x) ≤ xnC r μ k * xnN x := hU
      _ ≤ xnC r μ k * (xnW r μ * xnN h) := mul_le_mul_of_nonneg_left H.le hC
      _ = (xnW r μ * xnC r μ k) * xnN h := by ring
      _ = (xnW r (xnAdd μ k) * xnC k μ k) * xnN h := by rw [hR]
      _ = xnW r (xnAdd μ k) * (xnC k μ k * xnN h) := by ring
end Formalism.BranchingDeterminantCap
