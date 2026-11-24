-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.wtSpC_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:58:12.422716+00:00
-- url     : https://prove2.me/submissions/e8e166f2-dd28-432f-a95f-5d93449456d5

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_InitPartZeroXMul
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_pow_mul_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_wt_setLast
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_wt_pow
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
theorem _root_.solution (hv : LL.vec (Fin.last K) = true) (ρ : Fin r) (e o : ℕ) (Cs : Finset (Fin r)) (w : Fin r → ℤ)
    (h : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    X (Fin.last K, ρ) ^ e * h ∈ WtSpC p LL (K + 1) Cs w ↔
      h ∈ WtSpC p (setLast LL o) (K + 1) Cs (shiftWt w ρ e) := by
  unfold WtSpC
  rw [pow_mul_mem]
  have hset : {m | Finsupp.single (Fin.last K, ρ) e + m ∈ {m | ∀ c ∈ Cs, wt LL (K + 1) c m = w c}} =
      {m | ∀ c ∈ Cs, wt (setLast LL o) (K + 1) c m = shiftWt w ρ e c} := by
    ext m
    simp only [Set.mem_setOf_eq, wt_setLast, wt_pow LL hv, shiftWt, Function.update_apply]
    refine forall₂_congr fun c _ => ?_
    by_cases hc : c = ρ
    · subst hc
      rw [if_pos rfl, if_pos rfl]
      omega
    · rw [if_neg (Ne.symm hc), if_neg hc, add_zero]
  rw [hset]
end Formalism.InvariantFactorPaths.L4
