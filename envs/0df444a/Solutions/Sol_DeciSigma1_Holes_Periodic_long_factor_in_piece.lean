-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.long_factor_in_piece
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:12:59.058024+00:00
-- url     : https://prove2.me/submissions/f95ac7a7-0773-4a4a-97e9-9f656c4b1d3a

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_Periods
public import Mathlib.Order.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Basic
public import Theorems.Thm_DeciSigma1_Holes_Periodic_exists_piece_of_stretch
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Words_hasPeriod_leastPeriod
public import Theorems.Thm_DeciSigma1_Words_leastPeriod_dvd
public import Theorems.Thm_DeciSigma1_Words_periodicOn_iff_hasPeriod
public import Theorems.Thm_DeciSigma1_Words_primitive_take_leastPeriod
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
variable {α : Type} {k : ℕ}
namespace DeciSigma1.Holes.Periodic
theorem _root_.solution [DecidableEq α] (W : Fin k → List α) (l : Fin k) {p x y : ℕ}
    (hp : 0 < p) (hy : y ≤ (W l).length) (hlen : x + 2 * p ≤ y) (hper : PeriodicOn (W l) p x y) :
    ∃ P : Piece W (leastPeriod (((W l).drop x).take (y - x))), P.coordinate = l ∧ P.start ≤ x ∧ y ≤
        P.stop ∧
      leastPeriod (((W l).drop x).take (y - x)) ∣ p := by
  set f := ((W l).drop x).take (y - x) with hf
  have hflen : f.length = y - x := by simp [hf]; omega
  have hfp : f.HasPeriod p := (periodicOn_iff_hasPeriod (by omega) hy).mp hper
  have hdvd : leastPeriod f ∣ p := leastPeriod_dvd hfp (by omega)
  have hdle : leastPeriod f ≤ p := Nat.le_of_dvd hp hdvd
  have hdper : PeriodicOn (W l) (leastPeriod f) x y :=
    (periodicOn_iff_hasPeriod (by omega) hy).mpr (hasPeriod_leastPeriod f)
  have hprim : IsPrimitive (((W l).drop x).take (leastPeriod f)) := by
    have h := primitive_take_leastPeriod (w := f) (by omega)
    have e : f.take (leastPeriod f) = ((W l).drop x).take (leastPeriod f) := by
      change (((W l).drop x).take (y - x)).take (leastPeriod f) = _
      rw [List.take_take, min_eq_left (by omega)]
    rwa [e] at h
  obtain ⟨P, hPl, hPs, hPe, _⟩ := exists_piece_of_stretch W l (by omega) hy hdper hprim
  exact ⟨P, hPl, hPs, hPe, hdvd⟩
end DeciSigma1.Holes.Periodic
