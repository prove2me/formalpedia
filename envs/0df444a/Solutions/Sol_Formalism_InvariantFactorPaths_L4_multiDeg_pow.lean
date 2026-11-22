-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.multiDeg_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:34:43.681151+00:00
-- url     : https://prove2.me/submissions/59146176-649c-4e26-808e-49c368ba46ef

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_InitPartZeroXMul
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
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



set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {K r : ℕ} (LL : Letters (K + 1))
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (ρ : Fin r) (e : ℕ) (he : e ≤ LL.deg (Fin.last K)) (m : Fin (K + 1) × Fin r →₀ ℕ) :
    MultiDeg LL (Finsupp.single (Fin.last K, ρ) e + m) ↔ MultiDeg (setLast LL (LL.deg (Fin.last K) - e)) m := by
  have hsum : ∀ i, ∑ c, (Finsupp.single (Fin.last K, ρ) e + m) (i, c) =
      ∑ c, m (i, c) + (if i = Fin.last K then e else 0) := by
    intro i
    simp only [Finsupp.add_apply, Finset.sum_add_distrib, Finsupp.single_apply, Prod.mk.injEq]
    by_cases hi : i = Fin.last K
    · subst hi
      simp [add_comm]
    · simp [Ne.symm hi, hi]
  unfold MultiDeg setLast
  constructor
  · intro h i
    have h1 := h i
    rw [hsum] at h1
    simp only [Function.update_apply]
    split_ifs with hi
    · subst hi
      simp only [if_true] at h1
      omega
    · simp only [hi, if_false, add_zero] at h1
      exact h1
  · intro h i
    have h1 := h i
    simp only [Function.update_apply] at h1
    rw [hsum]
    split_ifs at h1 with hi
    · subst hi
      simp only [if_true]
      omega
    · simp only [hi, if_false, add_zero]
      exact h1
end Formalism.InvariantFactorPaths.L4
