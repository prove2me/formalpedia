-- Prove2me | solution 1 for Erdos684.frequently_smallPrimePart_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:20:04.599541+00:00
-- url     : https://prove2.me/submissions/344bd885-46c1-4a54-acf8-5ff445cc1f98

module
public import Definitions.Def_Erdos684_Finite
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Definitions.Def_Erdos684_Lower
public import Theorems.Thm_Erdos684_smallPrimePart_obstruction_eq_one
public import Theorems.Thm_Erdos684_lt_obstructionModulus
public import Theorems.Thm_Erdos684_log_obstructionModulus_le

set_option autoImplicit false
@[expose] public section
public section
open Filter Real
open scoped Topology
open Erdos684
namespace Erdos684
theorem _root_.solution :
    ∃ᶠ n : ℕ in atTop, 1 < n ∧
      ∀ k : ℕ, (k : ℝ) ≤ log (n : ℝ) / 8 → smallPrimePart n k = 1 := by
  apply frequently_atTop'.mpr
  intro N
  let K := max (N + 1) 3
  have hK : 2 < K := by dsimp [K]; omega
  have hNK : N < K := by dsimp [K]; omega
  have hmod := lt_obstructionModulus hK
  let n := obstructionModulus K - 1
  have hKn : K ≤ n := by dsimp [n]; omega
  have hn : 1 < n := by omega
  refine ⟨n, hNK.trans_le hKn, hn, ?_⟩
  intro k hk
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hlog : log (n : ℝ) ≤ log (obstructionModulus K : ℝ) := by
    apply Real.log_le_log hnpos
    exact_mod_cast (show n ≤ obstructionModulus K by dsimp [n]; omega)
  have hbound := log_obstructionModulus_le K
  have hkK : k ≤ K := by
    have : (k : ℝ) ≤ K := by linarith
    exact_mod_cast this
  exact smallPrimePart_obstruction_eq_one K hkK
end Erdos684
