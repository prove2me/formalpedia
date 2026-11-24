-- Prove2me | solution 1 for BalanceSpecification.entropy_unrestrictedShift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:31:08.102802+00:00
-- url     : https://prove2.me/submissions/d89005f8-292b-4fb3-a7f4-a0d122970404

module
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Definitions.Def_BalanceSpecificaton_TilingBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_ProductShift
public import Theorems.Thm_BalanceSpecification_wordCount_unrestrictedShift
public import Theorems.Thm_BalanceSpecification_tendsto_entropy


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open Filter
open scoped Topology
variable {A B : Type*}
namespace BalanceSpecification
theorem _root_.solution [Fintype A] [TopologicalSpace A] [Nonempty A] :
    entropy (unrestrictedShift A) unrestrictedShift_nonempty = Real.log (Fintype.card A) := by
  have ht : Tendsto
      (fun n : ℕ => Real.log (wordCount (language (unrestrictedShift A)) n) / n)
      atTop (𝓝 (Real.log (Fintype.card A))) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
    rw [wordCount_unrestrictedShift, Nat.cast_pow, Real.log_pow]
    have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    field_simp
  exact tendsto_nhds_unique (tendsto_entropy unrestrictedShift_nonempty) ht
end BalanceSpecification
