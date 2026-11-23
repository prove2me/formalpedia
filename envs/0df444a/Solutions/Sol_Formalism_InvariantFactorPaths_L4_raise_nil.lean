-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.raise_nil
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:03:16.877796+00:00
-- url     : https://prove2.me/submissions/1c888f75-3485-42c8-bb99-35878679cbe3

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementB
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds
import Theorems.Thm_Formalism_CountingSumsFrames_glAct_keep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.InvariantFactorPaths.L4
open Formalism.GM.M MvPolynomial Finset Formalism.CountingSumsFrames
section Gen
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
private theorem single_add_sub_single_eq_of_one_le {σ : Type} (m : σ →₀ ℕ) (v : σ) (hv : 1 ≤ m v) :
    Finsupp.single v 1 + (m - Finsupp.single v 1) = m :=
  add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr hv)
end Gen
section Tools
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
private theorem sum_weight_mul_single_add_eq {σ : Type} [Fintype σ] (w : σ → ℕ) (u : σ) (m : σ →₀ ℕ) :
    ∑ v, w v * (Finsupp.single u 1 + m : σ →₀ ℕ) v = w u + ∑ v, w v * m v := by
  classical
  simp [Finsupp.single_apply, mul_add, Finset.sum_add_distrib]
end Tools
section Last
variable (p : ℕ) [Fact p.Prime] {K r : ℕ} [NeZero r] (LL : Letters (K + 1)) (j : ℕ) (M : WithTop ℤ)
end Last
end Formalism.InvariantFactorPaths.L4
end

set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM.M MvPolynomial Finset Formalism.CountingSumsFrames
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution [NeZero r] (LL : Letters N) (j : ℕ) (c : Fin r) (hc : c ≠ 0)
    (h : MvPolynomial (Fin N × Fin r) ℚ_[p]) : ∃ n : ℕ, ((glAct p LL j 0 c) ^ n) h = 0 := by
  classical
  let wg : Fin N × Fin r → ℕ := fun v => if (v.1 : ℕ) < j then
      (if LL.vec v.1 then (if v.2 = c then 1 else 0) else (if v.2 = 0 then 1 else 0)) else 0
  let φ : (Fin N × Fin r →₀ ℕ) → ℕ := fun m => ∑ v, wg v * m v
  have step : ∀ k : ℕ, ∀ x ∈ restrictSupport ℚ_[p] {m | φ m < k + 1},
      glAct p LL j 0 c x ∈ restrictSupport ℚ_[p] {m | φ m < k} := by
    intro k
    refine glAct_keep (p := p) LL j 0 c _ _ ?_ ?_
    · intro i hi hv m hm h1
      have hm' := single_add_sub_single_eq_of_one_le m (i, c) h1
      simp only [Set.mem_setOf_eq] at hm ⊢
      rw [← hm'] at hm
      simp only [φ, sum_weight_mul_single_add_eq] at hm ⊢
      have e0 : wg (i, 0) = 0 := by simp [wg, hi, hv, Ne.symm hc]
      have e1 : wg (i, c) = 1 := by simp [wg, hi, hv]
      omega
    · intro i hi hv m hm h1
      have hm' := single_add_sub_single_eq_of_one_le m (i, 0) h1
      simp only [Set.mem_setOf_eq] at hm ⊢
      rw [← hm'] at hm
      simp only [φ, sum_weight_mul_single_add_eq] at hm ⊢
      have e0 : wg (i, c) = 0 := by simp [wg, hi, hv, hc]
      have e1 : wg (i, 0) = 1 := by simp [wg, hi, hv]
      omega
  have iter : ∀ n k : ℕ, ∀ x ∈ restrictSupport ℚ_[p] {m | φ m < n + k},
      ((glAct p LL j 0 c) ^ n) x ∈ restrictSupport ℚ_[p] {m | φ m < k} := by
    intro n
    induction n with
    | zero => intro k x hx; simpa using hx
    | succ n ih =>
      intro k x hx
      rw [pow_succ, Module.End.mul_apply]
      exact ih k _ (step (n + k) x (by rw [show n + k + 1 = n + 1 + k by omega]; exact hx))
  refine ⟨h.support.sup φ + 1, ?_⟩
  have h0 := iter (h.support.sup φ + 1) 0 h (by
    rw [mem_restrictSupport_iff]
    intro m hm
    simp only [Set.mem_setOf_eq, add_zero]
    exact Nat.lt_succ_of_le (Finset.le_sup (f := φ) (Finset.mem_coe.mp hm)))
  rw [mem_restrictSupport_iff] at h0
  apply MvPolynomial.support_eq_empty.mp
  by_contra hne
  obtain ⟨m, hm⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  have := h0 (Finset.mem_coe.mpr hm)
  simp at this
end Formalism.InvariantFactorPaths.L4
