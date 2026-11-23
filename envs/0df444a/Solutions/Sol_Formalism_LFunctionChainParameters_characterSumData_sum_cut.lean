-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.characterSumData.sum_cut
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:38:05.851345+00:00
-- url     : https://prove2.me/submissions/8e0df0a9-2318-409b-af10-5d1eee485d48

import Definitions.Def_Formalism_SizeWindowBrackets_FirstPrimeNeSecondPrime
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.characterSumData
open Formalism Formalism.D5
open PB
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Formalism.LFunctionChainParameters.characterSumData
theorem _root_.solution (D : ArithData H) (ψ : AddChar (E0 × H) ℂ) (N : ℕ) (a W : ℝ) (ha : 0 < a) (hW : 0 < W)
    (hN : a / W ≤ N) :
    ∑ n ∈ Icc 1 N, (Λ n : ℂ) * primVal D ψ n * ((max (a / n - W) 0 : ℝ) : ℂ)
      = ∑ n ∈ Icc 1 ⌊a / W⌋₊, (Λ n : ℂ) * primVal D ψ n * ((a / n - W : ℝ) : ℂ) := by
  have hMN : ⌊a / W⌋₊ ≤ N := by
    have h1 : ((⌊a / W⌋₊ : ℕ) : ℝ) ≤ N := (Nat.floor_le (by positivity)).trans hN
    exact_mod_cast h1
  have hterm : ∀ n ∈ Icc 1 N, (Λ n : ℂ) * primVal D ψ n * ((max (a / n - W) 0 : ℝ) : ℂ)
      = if n ≤ ⌊a / W⌋₊ then (Λ n : ℂ) * primVal D ψ n * ((a / n - W : ℝ) : ℂ) else 0 := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.1 hn).1
    have hn0 : (0 : ℝ) < n := by linarith
    split_ifs with h
    · have h2 : (n : ℝ) ≤ a / W := (Nat.le_floor_iff (by positivity)).1 h
      rw [le_div_iff₀ hW] at h2
      have h3 : W ≤ a / n := by
        rw [le_div_iff₀ hn0]
        linarith [mul_comm W (n : ℝ)]
      rw [max_eq_left (by linarith)]
    · have h2 : a / W < n := (Nat.floor_lt (by positivity)).1 (not_le.1 h)
      rw [div_lt_iff₀ hW] at h2
      have h3 : a / n < W := by
        rw [div_lt_iff₀ hn0]
        linarith [mul_comm W (n : ℝ)]
      rw [max_eq_right (by linarith)]
      simp
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, _⟩, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, h2.trans hMN⟩, h2⟩
end Formalism.LFunctionChainParameters.characterSumData
