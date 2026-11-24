-- Prove2me | solution 1 for BalanceSpecification.shortlexWord_strictMono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:44:09.681952+00:00
-- url     : https://prove2.me/submissions/f5e292db-ef28-4973-8274-7484c69b328f

module
public import Definitions.Def_BalanceSpecificaton_Counting
public import Mathlib.Data.List.Shortlex
public import Mathlib.Data.List.Lex
public import Mathlib.Data.Finset.Sort
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Shortlex
public import Theorems.Thm_BalanceSpecification_shortlexThrough_pairwise
public import Theorems.Thm_BalanceSpecification_shortlexWord_eq_getElem

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*} [Fintype A] [LinearOrder A]
variable [Nonempty A]
namespace BalanceSpecification
theorem _root_.solution {i j : ℕ} (hij : i < j) :
    List.Shortlex (· < ·) (shortlexWord (A := A) i) (shortlexWord j) := by
  have hj : j < (shortlexThrough (A := A) j).length := by
    have := shortlexThrough_length (A := A) j
    omega
  rw [shortlexWord_eq_getElem (lt_trans hij hj), shortlexWord_eq_getElem hj]
  exact List.pairwise_iff_getElem.mp (shortlexThrough_pairwise j) i j (lt_trans hij hj) hj hij
end BalanceSpecification
