-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.low_keep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:30.267882+00:00
-- url     : https://prove2.me/submissions/12417db0-2034-4c03-a2d3-0adb35452161

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
private theorem wt_single_add_eq (LL : Letters N) (j : ℕ) (c' : Fin r) (i : Fin N) (c : Fin r)
    (m : Fin N × Fin r →₀ ℕ) :
    wt LL j c' (Finsupp.single (i, c) 1 + m) = wt LL j c' m +
      (if (i : ℕ) < j then (if LL.vec i then (1 : ℤ) else -1) else 0) * (if c = c' then 1 else 0) := by
  classical
  unfold wt
  rw [← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib, Finset.sum_eq_single i]
  · by_cases hc : c = c'
    · subst hc
      by_cases hi : (i : ℕ) < j
      · cases hv : LL.vec i <;> simp [hi, hv] <;> ring
      · simp [hi]
    · have h0 : (Finsupp.single (i, c) 1 : Fin N × Fin r →₀ ℕ) (i, c') = 0 := by
        simp [Finsupp.single_apply, hc]
      simp [h0, hc]
  · intro k _ hk
    have h0 : (Finsupp.single (i, c) 1 : Fin N × Fin r →₀ ℕ) (k, c') = 0 := by
      simp [Finsupp.single_apply, Ne.symm hk]
    simp [h0]
  · simp
end Gen
section Tools
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
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
theorem _root_.solution [NeZero r] (LL : Letters N) (j : ℕ) (a b : Fin r) (ha : a ≠ 0) (M : WithTop ℤ) :
    ∀ x ∈ SuppLE p LL j M, glAct p LL j a b x ∈ SuppLE p LL j M := by
  intro x hx
  refine glAct_keep (p := p) LL j a b _ _ ?_ ?_ x hx
  · intro i hi hv m hm h1
    have hm' := single_add_sub_single_eq_of_one_le m (i, b) h1
    simp only [Set.mem_setOf_eq] at hm ⊢
    rw [← hm'] at hm
    rw [wt_single_add_eq] at hm ⊢
    refine le_trans (WithTop.coe_le_coe.mpr ?_) hm
    simp [hi, hv, ha] <;> split_ifs <;> omega
  · intro i hi hv m hm h1
    have hm' := single_add_sub_single_eq_of_one_le m (i, a) h1
    simp only [Set.mem_setOf_eq] at hm ⊢
    rw [← hm'] at hm
    rw [wt_single_add_eq] at hm ⊢
    refine le_trans (WithTop.coe_le_coe.mpr ?_) hm
    simp [hi, hv, ha] <;> split_ifs <;> omega
end Formalism.InvariantFactorPaths.L4
