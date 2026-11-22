-- Prove2me | solution 1 for Egrs75.Probe.clearing_high
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:32:01.587984+00:00
-- url     : https://prove2.me/submissions/723f61b4-5615-4ae1-b3c1-4c2ec9206941

module
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit
public import Definitions.Def_LeanPool_Egrs75_RoundUp
public import Mathlib.Data.Finset.Attr
public import Definitions.Def_LeanPool_Egrs75_ClearingHigh
public import Theorems.Thm_Egrs75_Probe_good_above_of_mem_window
public import Theorems.Thm_Egrs75_RoundUp_exists_lowDigits_between


set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.Probe
open Nat
open Egrs75
open Egrs75.RepairPaperfaithful
namespace Egrs75.Probe
theorem _root_.solution {p q : ℕ} (hp3 : 3 ≤ p) (hpo : Odd p) (hq3 : 3 ≤ q)
    (N : ℕ) {j : ℕ} (hjN : N < q ^ j) :
    ∃ n', LowDigits p n' ∧ N < n' ∧ (∀ i, j ≤ i → ¬ BadAt q i n') := by
  have hx1 : 1 ≤ q ^ j := Nat.one_le_pow _ _ (by omega)
  obtain ⟨m, hlo, hhi, hlowp⟩ := RoundUp.exists_lowDigits_between hp3 hpo (q ^ j) hx1
  refine ⟨m, hlowp, lt_of_lt_of_le hjN hlo, ?_⟩
  intro i hi
  unfold BadAt digitAt
  have := good_above_of_mem_window hq3 hlo hhi i hi
  omega
end Egrs75.Probe
