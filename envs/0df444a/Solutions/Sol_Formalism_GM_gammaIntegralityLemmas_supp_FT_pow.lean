-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.supp_FT_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:53:58.052854+00:00
-- url     : https://prove2.me/submissions/45eb18c0-14b9-4a3f-a288-76059342121b

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_zero
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_coeff_Dop_pow
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_FT_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.gammaIntegralityLemmas
open MvPolynomial Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {σ : Type} [DecidableEq σ] {r : ℕ} (w e : Fin r → σ)
namespace Formalism.GM.gammaIntegralityLemmas
theorem _root_.solution (T : Finset (Fin r)) (Q : ℕ → (σ →₀ ℕ) → Prop)
    (hstep : ∀ b β c, c ∈ T → Q b (β + Finsupp.single (w c) 1 + Finsupp.single (e c) 1) → Q (b + 1) β)
    (hwe : ∀ c, w c ≠ e c)
    (G : MvPolynomial σ ℚ_[p]) (h0 : ∀ β ∈ G.support, Q 0 β) :
    ∀ b, ∀ β ∈ ((FT w e T ^ b) G).support, Q b β := by
  intro b
  induction b with
  | zero => simpa using h0
  | succ b ih =>
    intro β hβ
    rw [pow_succ', Module.End.mul_apply, mem_support_iff] at hβ
    rw [FT_apply, coeff_sum] at hβ
    obtain ⟨c, hc, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hβ
    have := coeff_Dop_pow (w c) (e c) (hwe c) 1 ((FT w e T ^ b) G) β
    rw [pow_one] at this
    rw [this] at hne
    have hm : coeff (β + 1 • (Finsupp.single (w c) 1 + Finsupp.single (e c) 1)) ((FT w e T ^ b) G) ≠ 0 := by
      intro h0'; apply hne; rw [h0']; ring
    rw [one_smul, ← add_assoc] at hm
    exact hstep b β c hc (ih _ (mem_support_iff.mpr hm))
end Formalism.GM.gammaIntegralityLemmas
