-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.mem_cond_of_euler_eigen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:58:11.813532+00:00
-- url     : https://prove2.me/submissions/2792a44d-076d-4524-9086-084ae9dc8048

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FirstWeightLeOfSupport
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_ycond_pderiv
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_free_le_ycond
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_mulX_ycond
import Theorems.Thm_Formalism_GM_ProjS_coeff_eulL
import Theorems.Thm_Formalism_GM_ProjS_eulL_apply
import Theorems.Thm_Formalism_GM_ProjS_pderiv_comm
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply


section
namespace Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
section Res
variable {p : ℕ} [Fact p.Prime] {σ : Type}
end Res
section Last
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
private theorem pderiv_last_eulL_eq (c : Fin r) (g : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    pderiv (Fin.last K, c) (Formalism.GM.ProjS.eulL (fun d : Fin r => (Fin.last K, d)) g) =
      pderiv (Fin.last K, c) g +
        Formalism.GM.ProjS.eulL (fun d : Fin r => (Fin.last K, d)) (pderiv (Fin.last K, c) g) := by
  classical
  rw [Formalism.GM.ProjS.eulL_apply, Formalism.GM.ProjS.eulL_apply, map_sum]
  simp only [Derivation.leibniz, MvPolynomial.pderiv_X, smul_eq_mul, Finset.sum_add_distrib]
  refine (add_comm _ _).trans ?_
  congr 1
  · rw [Finset.sum_eq_single c]
    · simp
    · intro d _ hd
      have hne : ((Fin.last K, d) : Fin (K + 1) × Fin r) ≠ (Fin.last K, c) := by simp [hd]
      simp [Pi.single_apply, hne]
    · intro h
      exact absurd (Finset.mem_univ c) h
  · refine Finset.sum_congr rfl fun d _ => ?_
    rw [Formalism.GM.ProjS.pderiv_comm]
end Last
end Formalism.InvariantFactorPaths.L4
end

set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution [NeZero r] (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) (Mt : WithTop ℤ) :
    ∀ (o : ℕ) (F : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]), F ∈ YCond p LL (K + 1) Mt →
      ProjS.eulL (fun c : Fin r => (Fin.last K, c)) F = ((o : ℕ) : ℚ_[p]) • F → F ∈ YCond p LL K Mt := by
  intro o
  induction o with
  | zero =>
    intro F hF he
    apply free_le_ycond LL hv Mt
    refine ⟨hF, ?_⟩
    rw [FreeLast, SetLike.mem_coe, MvPolynomial.mem_restrictSupport_iff]
    intro m hm c
    rw [Finset.mem_coe, MvPolynomial.mem_support_iff] at hm
    have hc := congrArg (MvPolynomial.coeff m) he
    rw [Formalism.GM.ProjS.coeff_eulL, Nat.cast_zero, zero_smul, MvPolynomial.coeff_zero] at hc
    have hs : (∑ d : Fin r, (m (Fin.last K, d) : ℚ_[p])) = 0 := (mul_eq_zero.1 hc).resolve_left hm
    have hs' : ∑ d : Fin r, m (Fin.last K, d) = 0 := by exact_mod_cast hs
    exact (Finset.sum_eq_zero_iff.1 hs') c (Finset.mem_univ c)
  | succ o ih =>
    intro F hF he
    have hne : ((o + 1 : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero o
    have hF' : F = ((o + 1 : ℕ) : ℚ_[p])⁻¹ • Formalism.GM.ProjS.eulL (fun c : Fin r => (Fin.last K, c)) F := by
      rw [he, smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [hF', Formalism.GM.ProjS.eulL_apply]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun c _ => mulX_ycond LL Mt c _ (ih _
      (ycond_pderiv LL hv Mt c F hF) ?_))
    have hcomm := pderiv_last_eulL_eq c F
    rw [he, Derivation.map_smul] at hcomm
    rw [eq_sub_of_add_eq' hcomm.symm]
    push_cast
    rw [add_smul, one_smul, add_sub_cancel_right]
end Formalism.InvariantFactorPaths.L4
