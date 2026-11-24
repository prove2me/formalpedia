-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.free_le_ycond
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:49:18.08783+00:00
-- url     : https://prove2.me/submissions/e2733486-6696-44b3-b903-58e3781bfbe3

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FirstWeightLeOfSupport
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_glAct_succ
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_wt_succ
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_last_ne_of_lt
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_pderiv_freeLast
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_le_ycond
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
private theorem yCond_le_restrictSupport_wt_le {N : ℕ} [NeZero r] (LL : Letters N) (j : ℕ) (Mt : WithTop ℤ) :
    YCond p LL j Mt ≤
      restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt} :=
  sSup_le fun _ hS => hS.1
private theorem glAct_mem_yCond_of_neZero {N : ℕ} [NeZero r] (LL : Letters N) (j : ℕ) (Mt : WithTop ℤ)
    (a b : Fin r) : ∀ y ∈ YCond p LL j Mt, glAct p LL j a b y ∈ YCond p LL j Mt := by
  have h : YCond p LL j Mt ≤ (YCond p LL j Mt).comap (glAct p LL j a b) :=
    sSup_le fun _ hS y hy => le_sSup hS (hS.2 a b y hy)
  exact fun y hy => h hy
private theorem pderiv_mem_freeLast (v : Fin (K + 1) × Fin r) :
    ∀ y ∈ FreeLast p K r, pderiv v y ∈ FreeLast p K r := by
  intro y hy
  rw [FreeLast, MvPolynomial.mem_restrictSupport_iff] at hy
  rw [y.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  rw [MvPolynomial.pderiv_monomial, FreeLast, MvPolynomial.mem_restrictSupport_iff]
  refine (Finset.coe_subset.2 MvPolynomial.support_monomial_subset).trans ?_
  rw [Finset.coe_singleton, Set.singleton_subset_iff]
  intro c
  rw [Finsupp.tsub_apply, hy hm c, Nat.zero_sub]
private theorem X_mul_mem_freeLast_of_ne_last (v : Fin (K + 1) × Fin r) (hv : v.1 ≠ Fin.last K) :
    ∀ y ∈ FreeLast p K r, X v * y ∈ FreeLast p K r := by
  classical
  intro y hy
  rw [FreeLast, MvPolynomial.mem_restrictSupport_iff] at hy ⊢
  intro m hm c
  rw [Finset.mem_coe, MvPolynomial.mem_support_iff, MvPolynomial.coeff_X_mul'] at hm
  split_ifs at hm with hmem
  · have h1 := hy (MvPolynomial.mem_support_iff.2 hm) c
    have hne : v ≠ (Fin.last K, c) := fun h => hv (congrArg Prod.fst h)
    rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg hne, Nat.sub_zero] at h1
    exact h1
  · exact absurd rfl hm
private theorem glAct_mem_freeLast (LL : Letters (K + 1)) (a b : Fin r) :
    ∀ y ∈ FreeLast p K r, glAct p LL K a b y ∈ FreeLast p K r := by
  intro y hy
  rw [glAct, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun i _ => ?_
  by_cases hij : (i : ℕ) < K
  · have hi : i ≠ Fin.last K := fun h => last_ne_of_lt i hij h.symm
    by_cases hvi : LL.vec i
    · simp only [hij, hvi, if_true, LinearMap.comp_apply, LinearMap.mulLeft_apply]
      exact X_mul_mem_freeLast_of_ne_last (i, a) hi _ (pderiv_mem_freeLast (i, b) y hy)
    · simp only [hij, hvi, if_true, Bool.false_eq_true, if_false, LinearMap.neg_apply,
        LinearMap.comp_apply, LinearMap.mulLeft_apply]
      exact Submodule.neg_mem _ (X_mul_mem_freeLast_of_ne_last (i, b) hi _ (pderiv_mem_freeLast (i, a) y hy))
  · simp only [hij, if_false, LinearMap.zero_apply]
    exact Submodule.zero_mem _
end Last
end Formalism.InvariantFactorPaths.L4
end

set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution [NeZero r] (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) (Mt : WithTop ℤ) :
    YCond p LL (K + 1) Mt ⊓ FreeLast p K r ≤ YCond p LL K Mt := by
  rintro y ⟨hY, hF⟩
  refine le_ycond LL K Mt (YCond p LL (K + 1) Mt ⊓ FreeLast p K r) ?_ ?_ ⟨hY, hF⟩
  · rintro z ⟨hzY, hzF⟩
    have h1 := yCond_le_restrictSupport_wt_le LL (K + 1) Mt hzY
    rw [MvPolynomial.mem_restrictSupport_iff] at h1 ⊢
    rw [FreeLast, SetLike.mem_coe, MvPolynomial.mem_restrictSupport_iff] at hzF
    intro m hm
    have hw := h1 hm
    have h0 : m (Fin.last K, 0) = 0 := hzF hm 0
    simp only [Set.mem_setOf_eq] at hw ⊢
    rw [wt_succ LL hv, h0, Nat.cast_zero, add_zero] at hw
    exact hw
  · rintro a b z ⟨hzY, hzF⟩
    have e := glAct_succ LL hv a b z
    rw [pderiv_freeLast z hzF b, mul_zero, add_zero] at e
    refine ⟨?_, glAct_mem_freeLast LL a b z hzF⟩
    rw [← e]
    exact glAct_mem_yCond_of_neZero LL (K + 1) Mt a b z hzY
end Formalism.InvariantFactorPaths.L4
