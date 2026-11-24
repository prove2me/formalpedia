-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.mulX_ycond
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:49:18.738634+00:00
-- url     : https://prove2.me/submissions/2c4a93e1-0298-494c-9097-c4d5bc516c2a

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FirstWeightLeOfSupport
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_wt_congr
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_last_ne_of_lt
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
private theorem glAct_X_last_mul_eq (LL : Letters (K + 1)) (a b c : Fin r)
    (y : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    glAct p LL K a b (X (Fin.last K, c) * y) = X (Fin.last K, c) * glAct p LL K a b y := by
  classical
  rw [glAct, LinearMap.sum_apply, LinearMap.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hij : (i : ℕ) < K
  · have hne : ∀ d : Fin r, ((Fin.last K, c) : Fin (K + 1) × Fin r) ≠ (i, d) :=
      fun d h => last_ne_of_lt i hij (congrArg Prod.fst h)
    by_cases hvi : LL.vec i
    · simp only [hij, hvi, if_true, LinearMap.comp_apply, LinearMap.mulLeft_apply,
        Derivation.coeFn_coe]
      rw [Derivation.leibniz, MvPolynomial.pderiv_X_of_ne (hne b), smul_zero, add_zero, smul_eq_mul]
      ring
    · simp only [hij, hvi, if_true, Bool.false_eq_true, if_false, LinearMap.neg_apply,
        LinearMap.comp_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe]
      rw [Derivation.leibniz, MvPolynomial.pderiv_X_of_ne (hne a), smul_zero, add_zero, smul_eq_mul]
      ring
  · simp [hij]
private theorem X_last_mul_mem_restrictSupport_wt_le [NeZero r] (LL : Letters (K + 1)) (Mt : WithTop ℤ) (c : Fin r) :
    ∀ y ∈ restrictSupport ℚ_[p] {m : Fin (K + 1) × Fin r →₀ ℕ | ((wt LL K 0 m : ℤ) : WithTop ℤ) ≤ Mt},
      X (Fin.last K, c) * y ∈
        restrictSupport ℚ_[p] {m : Fin (K + 1) × Fin r →₀ ℕ | ((wt LL K 0 m : ℤ) : WithTop ℤ) ≤ Mt} := by
  classical
  intro y hy
  rw [MvPolynomial.mem_restrictSupport_iff] at hy ⊢
  intro m hm
  rw [Finset.mem_coe, MvPolynomial.mem_support_iff, MvPolynomial.coeff_X_mul'] at hm
  split_ifs at hm with hmem
  · have h1 := hy (MvPolynomial.mem_support_iff.2 hm)
    simp only [Set.mem_setOf_eq] at h1 ⊢
    rwa [wt_congr LL K 0 m (m - Finsupp.single (Fin.last K, c) 1)]
    intro i hi
    have hne : ((Fin.last K, c) : Fin (K + 1) × Fin r) ≠ (i, 0) :=
      fun h => last_ne_of_lt i hi (congrArg Prod.fst h)
    rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg hne, Nat.sub_zero]
  · exact absurd rfl hm
end Last
end Formalism.InvariantFactorPaths.L4
end

set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution [NeZero r] (LL : Letters (K + 1)) (Mt : WithTop ℤ) (c : Fin r) :
    ∀ x ∈ YCond p LL K Mt, X (Fin.last K, c) * x ∈ YCond p LL K Mt := by
  intro x hx
  refine le_ycond LL K Mt ((YCond p LL K Mt).map (LinearMap.mulLeft ℚ_[p] (X (Fin.last K, c))))
    ?_ ?_ ⟨x, hx, rfl⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact X_last_mul_mem_restrictSupport_wt_le LL Mt c y (yCond_le_restrictSupport_wt_le LL K Mt hy)
  · rintro a b _ ⟨y, hy, rfl⟩
    refine ⟨glAct p LL K a b y, glAct_mem_yCond_of_neZero LL K Mt a b y hy, ?_⟩
    simp only [LinearMap.mulLeft_apply]
    exact (glAct_X_last_mul_eq LL a b c y).symm
end Formalism.InvariantFactorPaths.L4
