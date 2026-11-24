-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.wt_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:49:47.369797+00:00
-- url     : https://prove2.me/submissions/7f56c690-235b-4726-a8e4-4ef282b5735a

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
theorem _root_.solution (hv : LL.vec (Fin.last K) = true) (ρ c : Fin r) (e : ℕ) (m : Fin (K + 1) × Fin r →₀ ℕ) :
    wt LL (K + 1) c (Finsupp.single (Fin.last K, ρ) e + m) = wt LL (K + 1) c m + (if ρ = c then (e : ℤ) else 0) := by
  unfold wt
  have hterm : ∀ i : Fin (K + 1),
      (if (i : ℕ) < K + 1 then (if LL.vec i then (((Finsupp.single (Fin.last K, ρ) e + m) (i, c) : ℕ) : ℤ)
        else -(((Finsupp.single (Fin.last K, ρ) e + m) (i, c) : ℕ) : ℤ)) else 0) =
      (if (i : ℕ) < K + 1 then (if LL.vec i then ((m (i, c) : ℕ) : ℤ) else -((m (i, c) : ℕ) : ℤ)) else 0) +
        (if i = Fin.last K then (if ρ = c then (e : ℤ) else 0) else 0) := by
    intro i
    by_cases hi : i = Fin.last K
    · subst hi
      by_cases hρ : ρ = c <;> simp [hv, Finsupp.single_apply, hρ] <;> (try ring)
    · simp [hi, Finsupp.single_apply, Ne.symm hi]
  refine (Finset.sum_congr rfl fun i _ => hterm i).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp
end Formalism.InvariantFactorPaths.L4
