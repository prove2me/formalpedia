-- Prove2me | solution 1 for BalanceSpecification.betaResidual_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:58:35.525174+00:00
-- url     : https://prove2.me/submissions/02a93481-5abd-4f2c-8ce0-5e006d7db0e6

module
public import Definitions.Def_BalanceSpecificaton_SGapBounds
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_EntropyRealization

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter Set
open scoped Topology
open BalanceSpecification
namespace BalanceSpecification
theorem _root_.solution {β a x R : ℝ} (hβ : 1 < β) (ha : 0 < a)
    (hax : a ≤ x) (hxR : x ≤ R) (haR : 1 + a ≤ R) (hR : (β - 1) * R ≤ 1)
    (n : ℕ) : a ≤ betaResidual β a x n ∧ betaResidual β a x n ≤ R := by
  have hβ0 : 0 ≤ β := (zero_lt_one.trans hβ).le
  induction n with
  | zero => exact ⟨hax, hxR⟩
  | succ n ih =>
    dsimp only [betaResidual]
    split_ifs with h
    · have H := mul_le_mul_of_nonneg_left ih.2 hβ0
      constructor <;> nlinarith only [h, H, hR]
    · have H : betaResidual β a x n ≤ β * betaResidual β a x n :=
        le_mul_of_one_le_left (ha.le.trans ih.1) hβ.le
      exact ⟨ih.1.trans H, (lt_of_not_ge h).le.trans haR⟩
end BalanceSpecification
