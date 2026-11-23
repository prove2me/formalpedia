-- Prove2me | solution 1 for CatalyticTreeEval.Main.corollary_3_11
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:27:42.209845+00:00
-- url     : https://prove2.me/submissions/85975735-4e6f-4649-841f-c4ddfc572e74
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_CatalyticTreeEval_Main_Matching
import Definitions.Def_CatalyticTreeEval_Corollary311Parameters
import Theorems.Thm_CatalyticTreeEval_Main_theorem_3_10
import Theorems.Thm_CatalyticTreeEval_Main_corollary_3_11_exact_restriction
import Theorems.Thm_CatalyticTreeEval_Main_corollary_3_11_fixed_estimates
import Theorems.Thm_CatalyticTreeEval_Main_corollary_3_11_variable_estimates

set_option autoImplicit false

open CatalyticTreeEval.Main

theorem solution :
    (∀ (t : ℕ) (p : Fin t → ℕ), 2 ≤ t → OddPrimeData p →
      ∃ (M : Machine) (Cd Cs : ℝ), 0 < Cd ∧ 0 < Cs ∧
        ∀ l : ℕ, 1 ≤ l →
        ∃ (d : ℕ) (U V : Fin (2 ^ l) → Vec (modulus p) d),
          (d : ℝ) ≤ exp₂ (Cd * (l : ℝ) ^ (1 / (t : ℝ)) *
            (log₂ (l + 2)) ^ (1 - 1 / (t : ℝ))) ∧
          SMatching (canonical p (modulus p)) U V ∧
          VectorAccess M (natCode l) U V (Cs * (l + lg d + lg (modulus p)))) ∧
    (∃ (M : Machine) (Cd Cs : ℝ) (L : ℕ), 0 < Cd ∧ 0 < Cs ∧ 2 ≤ L ∧
      ∀ l : ℕ, L ≤ l →
      ∃ (d : ℕ) (U V : Fin (2 ^ l) → Vec (modulus (firstOddPrimes (variablePrimeCount l))) d),
        (d : ℝ) ≤ exp₂ (exp₂ (Cd * Real.sqrt (log₂ l))) ∧
        SMatching (canonical (firstOddPrimes (variablePrimeCount l))
          (modulus (firstOddPrimes (variablePrimeCount l)))) U V ∧
        VectorAccess M (natCode l) U V
          (Cs * (l + lg d + lg (modulus (firstOddPrimes (variablePrimeCount l)))))) := by
  obtain ⟨M₀, C₀, hC₀, hconstruction⟩ := theorem_3_10
  have hcontract : LargeFamilyConstruction M₀ C₀ := hconstruction
  obtain ⟨hfixed, hvariable⟩ :=
    corollary_3_11_exact_restriction M₀ C₀ hC₀ hcontract
  constructor
  · intro t p ht hp
    obtain ⟨Mn, Cn, hCn, haccess⟩ := hfixed t p ht hp
    obtain ⟨Cd, Cs, hCd, hCs, hestimates⟩ :=
      corollary_3_11_fixed_estimates p ht hp
    refine ⟨Mn, Cd, Cn * Cs, hCd, mul_pos hCn hCs, ?_⟩
    intro l hl
    obtain ⟨hw₀, hwH, hN, hdim, hspace⟩ := hestimates l hl
    obtain ⟨U, V, hmatching, haccess⟩ := haccess l hl
    refine ⟨regimeDimension p l, U, V, hdim, hmatching, ?_⟩
    intro i j
    obtain ⟨time, c, hrun, hstate, houtput, hwork⟩ := haccess i j
    refine ⟨time, c, hrun, hstate, houtput, ?_⟩
    have hs : Cn * regimeSpace p l ≤
        (Cn * Cs) * (l + lg (regimeDimension p l) + lg (modulus p)) := by
      calc
        Cn * regimeSpace p l ≤
            Cn * (Cs * (l + lg (regimeDimension p l) + lg (modulus p))) :=
          mul_le_mul_of_nonneg_left hspace hCn.le
        _ = (Cn * Cs) * (l + lg (regimeDimension p l) + lg (modulus p)) := by ring
    intro s hs' c' hrun'
    exact lt_of_lt_of_le (hwork s hs' c' hrun') (Nat.ceil_le_ceil hs)
  · obtain ⟨Mn, Cn, hCn, haccess⟩ := hvariable
    obtain ⟨Cd, Cs, L, hCd, hCs, hL, hestimates⟩ :=
      corollary_3_11_variable_estimates
    refine ⟨Mn, Cd, Cn * Cs, L, hCd, mul_pos hCn hCs, hL, ?_⟩
    intro l hl
    obtain ⟨hw₀, hwH, hN, hdim, hspace⟩ := hestimates l hl
    have hpow_all : ∀ n : ℕ, 1 + n ≤ 2 ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          rw [Nat.pow_succ]
          omega
    have hrestriction : 1 + l ≤
        (regimeHeight (firstOddPrimes (variablePrimeCount l)) l).choose
          (regimeWidth (firstOddPrimes (variablePrimeCount l)) l) :=
      (hpow_all l).trans hN
    obtain ⟨U, V, hmatching, haccess⟩ := haccess l hrestriction
    refine ⟨regimeDimension (firstOddPrimes (variablePrimeCount l)) l, U, V,
      hdim, hmatching, ?_⟩
    intro i j
    obtain ⟨time, c, hrun, hstate, houtput, hwork⟩ := haccess i j
    refine ⟨time, c, hrun, hstate, houtput, ?_⟩
    have hs : Cn * regimeSpace (firstOddPrimes (variablePrimeCount l)) l ≤
        (Cn * Cs) * (l + lg (regimeDimension (firstOddPrimes (variablePrimeCount l)) l) +
          lg (modulus (firstOddPrimes (variablePrimeCount l)))) := by
      calc
        Cn * regimeSpace (firstOddPrimes (variablePrimeCount l)) l ≤
            Cn * (Cs * (l + lg (regimeDimension (firstOddPrimes (variablePrimeCount l)) l) +
              lg (modulus (firstOddPrimes (variablePrimeCount l))))) :=
          mul_le_mul_of_nonneg_left hspace hCn.le
        _ = (Cn * Cs) * (l + lg (regimeDimension (firstOddPrimes (variablePrimeCount l)) l) +
              lg (modulus (firstOddPrimes (variablePrimeCount l)))) := by ring
    intro s hs' c' hrun'
    exact lt_of_lt_of_le (hwork s hs' c' hrun') (Nat.ceil_le_ceil hs)
