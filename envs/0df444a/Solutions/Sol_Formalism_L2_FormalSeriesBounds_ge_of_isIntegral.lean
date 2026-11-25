-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.ge_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:33:07.256837+00:00
-- url     : https://prove2.me/submissions/eb193404-34f4-4558-a127-b9697dfefe78

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_HostTraceIdentity
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePEmbIntSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieLab
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_add
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_neg
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_add
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul_int
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_neg
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_one
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero
import Theorems.Thm_Formalism_L2_Pj_IsEval_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution {C : Type} [Field C] (V : VF C) {x : C} (hx : IsIntegral ℤ x) : V.Ge 0 x := by
  obtain ⟨p, hpm, hp⟩ := hx
  have hZ : ∀ z : ℤ, V.Ge 0 (algebraMap ℤ C z) := by
    intro z
    rw [eq_intCast]
    refine Int.induction_on z ?_ ?_ ?_
    · rw [Int.cast_zero]; exact VF.Ge.zero 0
    · intro i ih
      rw [Int.cast_add, Int.cast_one]
      exact VF.Ge.add ih VF.Ge.one
    · intro i ih
      rw [Int.cast_sub, Int.cast_one, sub_eq_add_neg]
      exact VF.Ge.add ih (VF.Ge.neg VF.Ge.one)
  by_contra hneg
  have hlt : V.v x < ((0 : ℝ) : WithTop ℝ) := not_le.mp hneg
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hlt)
  have hr0 : r < 0 := by
    rw [← hr] at hlt
    exact WithTop.coe_lt_coe.mp hlt
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, AddValuation.map_zero] at hr
    exact WithTop.coe_ne_top hr
  set yv := x⁻¹ with hyv
  have hy0 : yv ≠ 0 := inv_ne_zero hx0
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp (fun h => hy0 ((AddValuation.top_iff V.v).mp h))
  have hrs : r + s = 0 := by
    have h1 : V.v (x * yv) = 0 := by rw [hyv, mul_inv_cancel₀ hx0, AddValuation.map_one]
    rw [AddValuation.map_mul, ← hr, ← hs] at h1
    exact_mod_cast h1
  have hy : V.Ge (-r) yv := by
    unfold VF.Ge
    rw [← hs]
    exact WithTop.coe_le_coe.mpr (by linarith)
  have hy0' : V.Ge 0 yv := by
    unfold VF.Ge
    rw [← hs]
    exact WithTop.coe_le_coe.mpr (by linarith)
  have hpow : ∀ k : ℕ, V.Ge 0 (yv ^ k) := by
    intro k
    induction k with
    | zero => rw [pow_zero]; exact VF.Ge.one
    | succ k ih => rw [pow_succ]; exact VF.Ge.mul_int ih hy0'
  rw [hpm.as_sum] at hp
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finset_sum,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow] at hp
  set n := p.natDegree
  have hsum : 1 + ∑ i ∈ Finset.range n, algebraMap ℤ C (p.coeff i) * yv ^ (n - i) = 0 := by
    have h2 := congrArg (· * yv ^ n) hp
    simp only [add_mul, Finset.sum_mul, zero_mul] at h2
    rw [← h2]
    congr 1
    · rw [← mul_pow, hyv, mul_inv_cancel₀ hx0, one_pow]
    · refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≤ n := le_of_lt (Finset.mem_range.mp hi)
      conv_rhs => rw [show n = (n - i) + i from (Nat.sub_add_cancel hi').symm]
      rw [pow_add, mul_assoc, mul_left_comm (x ^ i), ← mul_pow, hyv, mul_inv_cancel₀ hx0, one_pow, mul_one]
  have hS : V.Ge (-r) (∑ i ∈ Finset.range n, algebraMap ℤ C (p.coeff i) * yv ^ (n - i)) := by
    refine Finset.sum_induction _ (fun z => V.Ge (-r) z) (fun _ _ ha hb => VF.Ge.add ha hb) (VF.Ge.zero _) ?_
    intro i hi
    have hi' : n - i = (n - i - 1) + 1 := by
      have := Finset.mem_range.mp hi
      omega
    rw [hi', pow_succ, ← mul_assoc]
    exact VF.Ge.mul_int (VF.Ge.mul_int (hZ _) (hpow _)) hy
  have h1 : (1 : C) = -∑ i ∈ Finset.range n, algebraMap ℤ C (p.coeff i) * yv ^ (n - i) :=
    eq_neg_of_add_eq_zero_left hsum
  have hS' := VF.Ge.neg hS
  rw [← h1] at hS'
  unfold VF.Ge at hS'
  rw [AddValuation.map_one] at hS'
  have : (-r : ℝ) ≤ 0 := by exact_mod_cast hS'
  linarith
end Formalism.L2.FormalSeriesBounds
