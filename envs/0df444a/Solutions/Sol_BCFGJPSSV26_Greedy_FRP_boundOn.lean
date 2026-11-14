-- Prove2me | solution 1 for BCFGJPSSV26.Greedy.FRP.boundOn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:03:54.550086+00:00
-- url     : https://prove2.me/submissions/ba4f17d9-f233-4419-abb4-c4c61b738255

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Bid
public import Definitions.Def_KMedian195_FactorRevealingPrimal
public import Mathlib.Data.Fintype.Order
public import Mathlib.Order.Fin.Basic
public import Definitions.Def_BCFGJPSSV26_Greedy_FRP
import all Definitions.Def_BCFGJPSSV26_Greedy_FRP
public import Theorems.Thm_KMedian195_originalPrimalUpperBound_exact

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Greedy.FRP

open Finset

/-- The bound for `∑ d = 1`: the program cast to `ℝ` is `KMedian195`'s. -/
theorem boundFin_one {n : ℕ} {r : Fin n → Fin (n + 1) → ℚ} {d : Fin n → ℚ} {f : ℚ}
    (h : FeasibleFin n r d f) (hd : ∑ j, d j = 1) : objFin n r ≤ f + ρ := by
  have hn : n ≠ 0 := by
    rintro rfl
    simp at hd
  have hb := KMedian195.originalPrimalUpperBound_exact (153 / 125) (by norm_num) le_rfl n hn
    ⟨fun j ↦ (d j : ℝ), (f : ℝ), fun j ℓ ↦ (r j ℓ : ℝ)⟩ ?_
  · have hobj : KMedian195.OriginalPrimalSolution.objective (153 / 125)
        ⟨fun j ↦ (d j : ℝ), (f : ℝ), fun j ℓ ↦ (r j ℓ : ℝ)⟩ = ((objFin n r - f : ℚ) : ℝ) := by
      simp only [KMedian195.OriginalPrimalSolution.objective, bidValue_ratCast, objFin,
        KMedian195.suffixRange, KMedian195.TimeIdx.ofIdx, KMedian195.TimeIdx.succ,
        KMedian195.TimeIdx.last]
      push_cast
      rfl
    have hρ : (2 - ((153 : ℝ) / 125 - 1) ^ 2) = (ρ : ℝ) := by
      simp only [ρ, γ]
      push_cast
      rfl
    rw [hobj, hρ] at hb
    have : objFin n r - f ≤ ρ := by exact_mod_cast hb
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    dsimp only [KMedian195.TimeIdx.ofIdx, KMedian195.TimeIdx.succ]
  · exact_mod_cast hd
  · intro j i hji
    exact_mod_cast h.mono j i hji
  · intro j k hjk
    exact_mod_cast h.tri j k hjk
  · intro j k ℓ hjk hj hk
    exact_mod_cast h.metric j k ℓ hjk hj hk
  · intro k
    have hk := (Rat.cast_le (K := ℝ)).mpr (h.facility k)
    push_cast [apply_ite (Rat.cast : ℚ → ℝ)] at hk
    simpa only [dite_eq_ite, bidValue_ratCast] using hk
  · exact_mod_cast h.f_nonneg
  · intro j
    exact_mod_cast h.d_nonneg j
  · intro j ℓ
    exact_mod_cast h.r_nonneg j ℓ

/-- **The bound on the factor-revealing program**, unnormalized: `obj ≤ f + ρ ∑ d`. From
`KMedian195.originalPrimalUpperBound_exact` at `γ = 153/125`, applied to `(r, d, f) / ∑ d`. -/
theorem boundFin {n : ℕ} {r : Fin n → Fin (n + 1) → ℚ} {d : Fin n → ℚ} {f : ℚ}
    (h : FeasibleFin n r d f) (hd : 0 < ∑ j, d j) : objFin n r ≤ f + ρ * ∑ j, d j := by
  set S := ∑ j, d j with hS
  have hc : 0 < S⁻¹ := inv_pos.mpr hd
  have h1 : ∑ j, S⁻¹ * d j = 1 := by
    rw [← Finset.mul_sum, ← hS, inv_mul_cancel₀ hd.ne']
  have hb := boundFin_one (h.smul hc) h1
  rw [objFin_smul n r hc] at hb
  have hb' := mul_le_mul_of_nonneg_left hb hd.le
  rw [mul_add, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hd.ne', one_mul, one_mul] at hb'
  linarith

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

section finTime

variable {n : ℕ} (e : Fin n ≃o ι)

end finTime

/-- **The bound on the factor-revealing program over a finite linear order**:
`∑_j term j ≤ f + ρ ∑ d`. From `BCFGJPSSV26.Greedy.FRP.boundFin` along `ι ≃o Fin n`. -/
theorem boundOn {r : ι → WithTop ι → ℚ} {d : ι → ℚ} {f : ℚ} (h : FeasibleOn r d f)
    (hd : 0 < ∑ j, d j) : ∑ j, term r j ≤ f + ρ * ∑ j, d j := by
  let e := Fintype.orderIsoFinOfCardEq ι rfl
  have hsum : ∑ j, d (e j) = ∑ j, d j := e.toEquiv.sum_comp d
  have hb := boundFin (h.fin e) (by rwa [hsum])
  rwa [objFin_finTime, hsum] at hb

end BCFGJPSSV26.Greedy.FRP

end

public section

theorem solution : type_of% @BCFGJPSSV26.Greedy.FRP.boundOn := @BCFGJPSSV26.Greedy.FRP.boundOn
