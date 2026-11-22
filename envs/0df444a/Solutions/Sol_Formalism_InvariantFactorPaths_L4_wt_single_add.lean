-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.wt_single_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:44:23.31271+00:00
-- url     : https://prove2.me/submissions/42d2bf19-7139-4a01-9db6-849e0823282d

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementB
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds
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
theorem _root_.solution (LL : Letters N) (j : ℕ) (c' : Fin r) (i : Fin N) (c : Fin r) (m : Fin N × Fin r →₀ ℕ) :
    wt LL j c' (Finsupp.single (i, c) 1 + m) = wt LL j c' m +
      (if (i : ℕ) < j then (if LL.vec i then (1 : ℤ) else -1) else 0) * (if c = c' then 1 else 0) := by
  exact wt_single_add_eq LL j c' i c m
end Formalism.InvariantFactorPaths.L4
