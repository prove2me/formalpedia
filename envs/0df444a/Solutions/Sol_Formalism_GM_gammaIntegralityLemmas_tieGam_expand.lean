-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.tieGam_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:34:03.065+00:00
-- url     : https://prove2.me/submissions/8e5bf950-96ed-40ab-bcd5-4803491592fe

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_fock_smul_left
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_fock_sum_left
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_fock_E_pow
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_fock_F_pow_expand
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_hy_wv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.gammaIntegralityLemmas
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [hp : Fact p.Prime]
variable {N r : ℕ}
namespace Formalism.GM.gammaIntegralityLemmas
theorem _root_.solution (LL : Letters (N + 1)) (ρ : Fin r) (z : ℕ)
    (f f' : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) (m : ℕ) :
    tieGam p LL ρ z (m + LL.total) f f' =
      ∑ j ∈ range (LL.deg (Fin.last N) + 1), ∑ a ∈ range (j + 1), ∑ a' ∈ range (j + 1),
        ∑ β ∈ ((FT wv ev (univ.erase ρ) ^ (j - a)) (aeval (freezeSub p LL ρ) f)).support,
          ∑ γ ∈ ((FT wv ev (univ.erase ρ) ^ (j - a')) (aeval (freezeSub p LL ρ) f')).support,
            termF LL ρ z j a a' β γ (coeff β ((FT wv ev (univ.erase ρ) ^ (j - a)) (aeval (freezeSub p LL ρ) f)))
              (coeff γ ((FT wv ev (univ.erase ρ) ^ (j - a')) (aeval (freezeSub p LL ρ) f'))) m := by
  have hdeg1 : (LL.snoc (m + LL.total)).deg (Fin.castSucc (Fin.last N)) = LL.deg (Fin.last N) := by
    simp [Letters.snoc]
  have hdeg2 : (LL.snoc (m + LL.total)).deg (Fin.last (N + 1)) = m + LL.total := by
    simp [Letters.snoc]
  unfold tieGam tiePhiAt freeze termF
  rw [hdeg1, hdeg2]
  unfold Formalism.GM.tiePhi
  rw [LinearMap.sum_apply, fock_sum_left, mul_sum, sum_div]
  apply sum_congr rfl; intro j _
  rw [LinearMap.smul_apply, LinearMap.comp_apply, fock_smul_left, fock_E_pow wv ev]
  simp only [Nat.add_sub_cancel]
  rw [fock_F_pow_expand wv ev ρ (hy_wv ρ)]
  simp only [mul_sum, sum_div]
end Formalism.GM.gammaIntegralityLemmas
