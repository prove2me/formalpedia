-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.fock_F_pow_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:25:00.896053+00:00
-- url     : https://prove2.me/submissions/3e73cb88-6f7c-4b33-be49-bf3b1666c008

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_fock_smul_left
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_fock_sum_left
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_fock_sum_right
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_fock_smul_right
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_FT_pow_X_pow_mul
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_tieF_pow_apply

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
variable {σ : Type} [Fintype σ] [DecidableEq σ] {r : ℕ} (w e : Fin r → σ) (ρ : Fin r)
namespace Formalism.GM.gammaIntegralityLemmas
theorem _root_.solution (hy : ∀ c ∈ univ.erase ρ, w c ≠ e ρ ∧ e c ≠ e ρ)
    (G G' : MvPolynomial σ ℚ_[p]) (j m : ℕ) :
    Formalism.GM.M.fock p ((Formalism.GM.tieF w e ^ j) (X (e ρ) ^ m * G)) ((Formalism.GM.tieF w e ^ j) (X (e ρ) ^ m * G')) =
      ∑ a ∈ range (j + 1), ∑ a' ∈ range (j + 1),
        ∑ β ∈ ((FT w e (univ.erase ρ) ^ (j - a)) G).support,
          ∑ γ ∈ ((FT w e (univ.erase ρ) ^ (j - a')) G').support,
            (((j.choose a : ℕ) : ℚ_[p]) * ((j.choose a' : ℕ) : ℚ_[p]) *
              Formalism.GM.M.fock p ((Dop (w ρ) (e ρ) ^ a) (X (e ρ) ^ m *
                        monomial β (coeff β ((FT w e (univ.erase ρ) ^ (j - a)) G))))
                ((Dop (w ρ) (e ρ) ^ a') (X (e ρ) ^ m *
                  monomial γ (coeff γ ((FT w e (univ.erase ρ) ^ (j - a')) G'))))) := by
  rw [tieF_pow_apply w e ρ, tieF_pow_apply w e ρ, fock_sum_left]
  apply sum_congr rfl; intro a _
  rw [fock_sum_right]
  apply sum_congr rfl; intro a' _
  rw [fock_smul_left, fock_smul_right, FT_pow_X_pow_mul w e (e ρ) _ hy, FT_pow_X_pow_mul w e (e ρ) _ hy]
  conv_lhs => rw [((FT w e (univ.erase ρ) ^ (j - a)) G).as_sum, ((FT w e (univ.erase ρ) ^ (j - a')) G').as_sum]
  rw [mul_sum, mul_sum, map_sum, map_sum, fock_sum_left, mul_sum, mul_sum]
  apply sum_congr rfl; intro β _
  rw [fock_sum_right, mul_sum, mul_sum]
  apply sum_congr rfl; intro γ _
  ring
end Formalism.GM.gammaIntegralityLemmas
