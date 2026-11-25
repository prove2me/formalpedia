-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.IVP.toChoose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:59:49.851637+00:00
-- url     : https://prove2.me/submissions/788db255-2d53-4600-b399-1b3e636acd1e

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_congr
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_newton
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_choose_sub_expand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.gammaIntegralityLemmas
open Finset Polynomial
variable {p : ℕ} [Fact p.Prime]
namespace Formalism.GM.gammaIntegralityLemmas
namespace IVP
theorem _root_.solution {D S : ℕ} {g : ℕ → ℚ_[p]} (hg : IVP p D g) :
    ∃ c : ℕ → ℤ_[p], ∀ n, S ≤ n →
      g (n - S) = ∑ i ∈ range (D + 1), (c i : ℚ_[p]) * ((n.choose i : ℕ) : ℚ_[p]) := by
  obtain ⟨d, hd⟩ := hg.newton
  have hex : ∀ k, ∃ e : ℕ → ℤ, k ≤ D → ∀ n, S ≤ n →
      (((n - S).choose k : ℕ) : ℤ) = ∑ i ∈ range (D + 1), e i * ((n.choose i : ℕ) : ℤ) := by
    intro k
    by_cases hk : k ≤ D
    · obtain ⟨e, he⟩ := choose_sub_expand D S k hk
      exact ⟨e, fun _ => he⟩
    · exact ⟨fun _ => 0, fun h => absurd h hk⟩
  choose e he using hex
  refine ⟨fun i => ∑ k ∈ range (D + 1), d k * (e k i : ℤ_[p]), fun n hn => ?_⟩
  rw [hd]
  have : ∀ k ∈ range (D + 1), (d k : ℚ_[p]) * (((n - S).choose k : ℕ) : ℚ_[p]) =
      ∑ i ∈ range (D + 1), (d k : ℚ_[p]) * (e k i : ℚ_[p]) * ((n.choose i : ℕ) : ℚ_[p]) := by
    intro k hk
    have h := he k (by simpa [Nat.lt_succ_iff] using hk) n hn
    have h' : (((n - S).choose k : ℕ) : ℚ_[p]) = ∑ i ∈ range (D + 1), (e k i : ℚ_[p]) * ((n.choose i : ℕ) : ℚ_[p]) := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℚ_[p])) h
    rw [h', mul_sum]
    apply sum_congr rfl; intro i _; ring
  rw [sum_congr rfl this, sum_comm]
  apply sum_congr rfl
  intro i _
  rw [← sum_mul]
  congr 1
  rw [PadicInt.coe_sum]
  apply sum_congr rfl; intro k _
  rw [PadicInt.coe_mul, PadicInt.coe_intCast]
end IVP
end Formalism.GM.gammaIntegralityLemmas
