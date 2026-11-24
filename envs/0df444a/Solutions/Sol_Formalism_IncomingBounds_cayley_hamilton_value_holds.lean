-- Prove2me | solution 1 for Formalism.IncomingBounds.cayley_hamilton_value_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:11.152264+00:00
-- url     : https://prove2.me/submissions/f63a40b9-f453-4e82-b828-c2cd3faec558

import Definitions.Def_Formalism_IncomingBounds_LevelTail
import Definitions.Def_Formalism_IncomingBounds_FrobOrbitPeriod
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_Series
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
namespace Formalism.IncomingBounds
private lemma even_mod_iff_of_even {d : ℕ} (hd : Even d) (x : ℕ) : Even (x % d) ↔ Even x := by
  have h := Nat.mod_add_div x d
  have hq : Even (d * (x / d)) := hd.mul_right _
  constructor
  · intro hm; rw [← h]; exact hm.add hq
  · intro hx
    rw [← h] at hx
    exact (Nat.even_add.mp hx).mpr hq
private lemma even_val_add_natCast_iff {d : ℕ} [NeZero d] (hd : Even d) (a : ZMod d) (ha : Even a.val)
    (n : ℕ) : Even (a + (n : ZMod d)).val ↔ Even n := by
  rw [ZMod.val_add, even_mod_iff_of_even hd, ZMod.val_natCast, Nat.even_add, even_mod_iff_of_even hd]
  exact ⟨fun h => h.mp ha, fun h => iff_of_true ha h⟩
private lemma hasSum_congr {f g : ℕ → ℝ} {a b : ℝ} (h : HasSum g b) (hfg : ∀ n, f n = g n)
    (hab : b = a) : HasSum f a := by
  rw [show f = g from funext hfg, ← hab]; exact h
private lemma hasSum_inv_pow_odd (l : ℝ) (hl : 1 < l) :
    HasSum (fun m : ℕ => (l ^ (2 * m + 1))⁻¹) (l / (l ^ 2 - 1)) := by
  have hl0 : 0 < l := by linarith
  have hsq : l ^ 2 - 1 ≠ 0 := (by nlinarith : (0 : ℝ) < l ^ 2 - 1).ne'
  have hq0 : 0 ≤ (l ^ 2)⁻¹ := by positivity
  have hq1 : (l ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hl two_ne_zero)
  have h := (hasSum_geometric_of_lt_one hq0 hq1).mul_left l⁻¹
  have e : (fun m : ℕ => (l ^ (2 * m + 1))⁻¹) = fun m : ℕ => l⁻¹ * ((l ^ 2)⁻¹) ^ m := by
    funext m; rw [pow_succ, pow_mul, mul_inv, ← inv_pow, mul_comm]
  refine hasSum_congr h (fun m => congrFun e m) ?_
  have h1 : 1 - (l ^ 2)⁻¹ = (l ^ 2 - 1) / l ^ 2 := by field_simp
  rw [h1]
  field_simp
private lemma hasSum_inv_pow_even (l : ℝ) (hl : 1 < l) :
    HasSum (fun m : ℕ => (l ^ (2 * m + 2))⁻¹) (1 / (l ^ 2 - 1)) := by
  have hl0 : 0 < l := by linarith
  have hsq : l ^ 2 - 1 ≠ 0 := (by nlinarith : (0 : ℝ) < l ^ 2 - 1).ne'
  have hq0 : 0 ≤ (l ^ 2)⁻¹ := by positivity
  have hq1 : (l ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hl two_ne_zero)
  have h := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (l ^ 2)⁻¹
  have e : (fun m : ℕ => (l ^ (2 * m + 2))⁻¹) = fun m : ℕ => (l ^ 2)⁻¹ * ((l ^ 2)⁻¹) ^ m := by
    funext m
    rw [show 2 * m + 2 = 2 * (m + 1) by ring, pow_mul, ← inv_pow, pow_succ']
  refine hasSum_congr h (fun m => congrFun e m) ?_
  have h1 : 1 - (l ^ 2)⁻¹ = (l ^ 2 - 1) / l ^ 2 := by field_simp
  rw [h1]
  field_simp
end Formalism.IncomingBounds
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.IncomingBounds
namespace Formalism.IncomingBounds
theorem _root_.solution : CHValue := by
  intro d _ l hl2 hd2 hd r j j' rh hrh hjr
  have hl : (1 : ℝ) < l := by
    have : 1 < l := by omega
    exact_mod_cast this
  have hl0 : (0 : ℝ) < l := by linarith
  have hpos : (0 : ℝ) < (l : ℝ) ^ 2 - 1 := by nlinarith
  have hl1 : (l : ℝ) - 1 ≠ 0 := (by linarith : (0 : ℝ) < (l : ℝ) - 1).ne'
  have hsq : (l : ℝ) ^ 2 - 1 ≠ 0 := hpos.ne'
  have hgr : gam l + rho l = 1 / ((l : ℝ) - 1) := by
    unfold gam rho
    field_simp
    ring
  have hγ0 : 0 ≤ gam l := div_nonneg hl0.le hpos.le
  have hρ0 : 0 ≤ rho l := div_nonneg zero_le_one hpos.le
  have hgS : HasSum (fun m : ℕ => ((l : ℝ) ^ (2 * m + 1))⁻¹) (gam l) :=
    hasSum_inv_pow_odd (l : ℝ) hl
  have hrS : HasSum (fun m : ℕ => ((l : ℝ) ^ (2 * m + 2))⁻¹) (rho l) :=
    hasSum_inv_pow_even (l : ℝ) hl
  have hrh0 : (0 : ℝ) ≤ rh := Nat.cast_nonneg _
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hj'0 : (0 : ℝ) ≤ j' := Nat.cast_nonneg _
  refine ⟨fun a ha => ?_, fun a => ?_⟩
  · have hsum : HasSum (fun k : ℕ => ((r : ℝ) - rh -
        (if Even (a + ((k + 1 : ℕ) : ZMod d)).val then (r : ℝ) - j' else (j' : ℝ))) /
          (l : ℝ) ^ (k + 1)) (((r : ℝ) - j' - rh) * gam l + ((j' : ℝ) - rh) * rho l) := by
      refine HasSum.even_add_odd ?_ ?_
      · refine hasSum_congr (hgS.mul_left ((r : ℝ) - j' - rh)) (fun m => ?_) rfl
        have hodd : ¬ Even (a + ((2 * m + 1 : ℕ) : ZMod d)).val := by
          rw [even_val_add_natCast_iff hd a ha]
          exact Nat.not_even_iff_odd.mpr (odd_two_mul_add_one m)
        simp only [hodd, ↓reduceIte]
        ring
      · refine hasSum_congr (hrS.mul_left ((j' : ℝ) - rh)) (fun m => ?_) rfl
        have hev : Even (a + ((2 * m + 1 + 1 : ℕ) : ZMod d)).val := by
          rw [even_val_add_natCast_iff hd a ha]
          exact ⟨m + 1, by ring⟩
        simp only [hev, ↓reduceIte]
        ring
    have hval : chSol d l ((r : ℝ) - rh) (fun b => if Even b.val then (r : ℝ) - j' else (j' : ℝ)) a =
        ((r : ℝ) - j' - rh) * gam l + ((j' : ℝ) - rh) * rho l := hsum.tsum_eq
    refine ⟨hval, ?_⟩
    rw [hval]
    have hrj : ((r - j' - j : ℕ) : ℝ) = (r : ℝ) - j' - j := by
      rw [Nat.cast_sub (show j ≤ r - j' by omega), Nat.cast_sub (show j' ≤ r by omega)]
    rw [hrj, Nat.cast_add]
    have hgu : gam l ≤ 1 / ((l : ℝ) - 1) := by linarith
    have hru : rho l ≤ 1 / ((l : ℝ) - 1) := by linarith
    have e1 : ((j : ℝ) + j') / ((l : ℝ) - 1) = (j + j') * (1 / ((l : ℝ) - 1)) := by ring
    rw [e1]
    nlinarith [mul_le_mul_of_nonneg_left hgu hj0, mul_le_mul_of_nonneg_left hru hj'0,
      mul_nonneg hrh0 hγ0, mul_nonneg hrh0 hρ0]
  · have hq0 : (0 : ℝ) ≤ (l : ℝ)⁻¹ := by positivity
    have hq1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl
    have hg := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (((j' : ℝ) - rh) * (l : ℝ)⁻¹)
    have hsum : HasSum (fun k : ℕ => ((r : ℝ) - rh - ((r : ℝ) - j')) / (l : ℝ) ^ (k + 1))
        (((j' : ℝ) - rh) / ((l : ℝ) - 1)) := by
      refine hasSum_congr hg (fun k => ?_) ?_
      · rw [inv_pow, pow_succ']
        field_simp
        ring
      · have h1 : 1 - (l : ℝ)⁻¹ = ((l : ℝ) - 1) / l := by field_simp
        rw [h1]
        field_simp
    have hval : chSol d l ((r : ℝ) - rh) (fun _ => (r : ℝ) - j') a =
        ((j' : ℝ) - rh) / ((l : ℝ) - 1) := hsum.tsum_eq
    refine ⟨hval, ?_⟩
    rw [Nat.cast_add, div_le_div_iff_of_pos_right (by linarith : (0 : ℝ) < (l : ℝ) - 1)]
    linarith
end Formalism.IncomingBounds
