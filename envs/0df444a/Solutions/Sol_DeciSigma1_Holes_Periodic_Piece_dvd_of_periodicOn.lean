-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.Piece.dvd_of_periodicOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:48:49.631539+00:00
-- url     : https://prove2.me/submissions/2b341063-c3c4-4d1b-b98a-d440a14cb851

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_Periods
public import Mathlib.Order.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Basic
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_periodicOn
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_period_pos
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_window_isConjugate
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_isPrimitive
public import Theorems.Thm_DeciSigma1_Words_PeriodicOn_mono
public import Theorems.Thm_DeciSigma1_Words_period_extend_gcd
public import Theorems.Thm_DeciSigma1_Words_periodicOn_iff_hasPeriod
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
open DeciSigma1.Holes.Periodic.Piece
variable {W : Fin k → List α} {d : ℕ}
namespace DeciSigma1.Holes.Periodic.Piece
theorem _root_.solution
    (P : Piece W d) {x δ : ℕ}
    (hx : P.start ≤ x) (hδ : PeriodicOn (W P.coordinate) δ x P.stop)
        (hlen : x + d + δ ≤ P.stop) : d ∣ δ := by
  have hd := P.period_pos
  have hg := period_extend_gcd (by omega) P.stop_le_length (P.periodicOn.mono hx le_rfl) hδ
    (by have := Nat.gcd_le_left δ hd; omega)
  have hgpos : 0 < d.gcd δ := Nat.gcd_pos_of_pos_left _ hd
  have hgle : d.gcd δ ≤ d := Nat.gcd_le_left _ hd
  have hwin := P.window_isConjugate hx (by omega)
  have hprim := hwin.isPrimitive P.primitive
  have hwlen : (((W P.coordinate).drop x).take d).length = d := by
    have := P.stop_le_length; simp; omega
  have hgd : d.gcd δ = d := by
    by_contra hne
    rw [isPrimitive_iff_period] at hprim
    apply hprim.2 (d.gcd δ) hgpos (by rw [hwlen]; omega) (by rw [hwlen]; exact Nat.gcd_dvd_left _ _)
    have := (periodicOn_iff_hasPeriod (w := W P.coordinate) (s := x) (e := x + d) (by omega)
      (by have := P.stop_le_length; omega)).mp (hg.mono le_rfl (by omega))
    rwa [show x + d - x = d by omega] at this
  rw [← hgd]
  exact Nat.gcd_dvd_right _ _
end DeciSigma1.Holes.Periodic.Piece
