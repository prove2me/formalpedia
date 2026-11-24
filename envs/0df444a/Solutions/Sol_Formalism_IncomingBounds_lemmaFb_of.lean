-- Prove2me | solution 1 for Formalism.IncomingBounds.lemmaFb_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:13.979938+00:00
-- url     : https://prove2.me/submissions/44f4ed1f-9f78-4dfd-b1bc-79b26ac51ca2

import Definitions.Def_Formalism_IncomingBounds_IncomingBound
import Definitions.Def_Formalism_IncomingBounds_LevelTail
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_LemmaF
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
section Helpers
variable {l d : ℕ} [NeZero d]
private lemma oddLevels_one_le {d i : ℕ} (hi : i ∈ oddLevels d) : 1 ≤ i := by
  unfold oddLevels at hi
  have h := (Finset.mem_filter.1 hi).2.pos
  omega
private lemma gam_sub_inv (hl : 2 ≤ l) : gam l - 1 / ((l : ℝ) + 1) = rho l := by
  have h2 : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have h1 : (l : ℝ) ^ 2 - 1 ≠ 0 := (by nlinarith : (0 : ℝ) < (l : ℝ) ^ 2 - 1).ne'
  have h3 : (l : ℝ) + 1 ≠ 0 := (by linarith : (0 : ℝ) < (l : ℝ) + 1).ne'
  unfold gam rho
  rw [div_sub_div _ _ h1 h3, div_eq_div_iff (mul_ne_zero h1 h3) h1]
  ring
private theorem one_le_pow_of_one_le_real {a : ℝ} (ha : 1 ≤ a) (n : ℕ) : 1 ≤ a ^ n := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ]; nlinarith
private theorem pow_le_pow_right_of_one_le_real {a : ℝ} (ha : 1 ≤ a) {m n : ℕ} (h : m ≤ n) : a ^ m ≤ a ^ n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add]
  have h1 := one_le_pow_of_one_le_real ha k
  have h2 : 0 ≤ a ^ m := pow_nonneg (by linarith) m
  nlinarith
private theorem self_le_pow_of_one_le_of_one_le_exp {a : ℝ} (ha : 1 ≤ a) {n : ℕ} (hn : 1 ≤ n) : a ≤ a ^ n := by
  have h := pow_le_pow_right_of_one_le_real ha hn
  rwa [pow_one] at h
private lemma isDual_const (hl : 1 ≤ l) : IsDual l d (fun _ => 1 / ((l : ℝ) + 1)) := by
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hpos : (0 : ℝ) < (l : ℝ) + 1 := by linarith
  have hc : ((l : ℝ) + 1) * (1 / ((l : ℝ) + 1)) = 1 := mul_one_div_cancel hpos.ne'
  have hc0 : 0 ≤ 1 / ((l : ℝ) + 1) := by positivity
  refine ⟨fun s => ⟨hc0, ?_⟩, fun s i hi => ?_⟩
  · show 1 / ((l : ℝ) + 1) ≤ 1
    nlinarith
  · show 1 ≤ (l : ℝ) ^ i * (1 / ((l : ℝ) + 1)) + 1 / ((l : ℝ) + 1)
    have hli := self_le_pow_of_one_le_of_one_le_exp hl1 (oddLevels_one_le hi)
    have hm := mul_le_mul_of_nonneg_right hli hc0
    nlinarith
private theorem sum_deficit_le_Fnum_of_isDual (hA : LemmaFa) (hl : 3 ≤ l) (hd : 2 ≤ d) (hev : Even d)
    {D sig : ZMod d → ℝ} (hD : 0 ≤ D) (hsig : IsDual l d sig) :
    ∑ s, D s * (gam l - sig s) ≤ Fnum l d D := by
  have h := (hA l d hl hd hev D hD).2
  exact h.2 ⟨sig, hsig, rfl⟩
private theorem exists_isDual_Fnum_eq_sum_deficit (hA : LemmaFa) (hl : 3 ≤ l) (hd : 2 ≤ d) (hev : Even d)
    {D : ZMod d → ℝ} (hD : 0 ≤ D) :
    ∃ sig, IsDual l d sig ∧ Fnum l d D = ∑ s, D s * (gam l - sig s) :=
  (hA l d hl hd hev D hD).2.1
private theorem sum_smul_apply_mul (c : ℝ) (D f : ZMod d → ℝ) :
    ∑ s, (c • D) s * f s = c * ∑ s, D s * f s := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, mul_assoc]
private theorem sum_add_apply_mul (D E f : ZMod d → ℝ) :
    ∑ s, (D + E) s * f s = ∑ s, D s * f s + ∑ s, E s * f s := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Pi.add_apply, add_mul]
end Helpers
end Formalism.IncomingBounds
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.IncomingBounds
namespace Formalism.IncomingBounds
theorem _root_.solution (hF : FlowAttained) (hA : LemmaFa) : LemmaFb := by
  intro l d _ hl hd hev
  refine ⟨fun c D hc hD => ?_, ⟨convex_Ici 0, fun D hD E hE a b ha hb hab => ?_⟩, fun D hD => ?_⟩
  · have hcD : 0 ≤ c • D := fun s => by
      rw [Pi.smul_apply, smul_eq_mul]
      exact mul_nonneg hc (hD s)
    obtain ⟨s1, hs1, e1⟩ := exists_isDual_Fnum_eq_sum_deficit hA hl hd hev hcD
    obtain ⟨s0, hs0, e0⟩ := exists_isDual_Fnum_eq_sum_deficit hA hl hd hev hD
    apply le_antisymm
    · rw [e1, sum_smul_apply_mul]
      exact mul_le_mul_of_nonneg_left (sum_deficit_le_Fnum_of_isDual hA hl hd hev hD hs1) hc
    · have h := sum_deficit_le_Fnum_of_isDual hA hl hd hev hcD hs0
      rw [sum_smul_apply_mul, ← e0] at h
      exact h
  · have hD' : 0 ≤ D := hD
    have hE' : 0 ≤ E := hE
    have hF0 : 0 ≤ a • D + b • E := fun s => by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_nonneg (mul_nonneg ha (hD' s)) (mul_nonneg hb (hE' s))
    obtain ⟨sg, hsg, e⟩ := exists_isDual_Fnum_eq_sum_deficit hA hl hd hev hF0
    rw [e, sum_add_apply_mul, sum_smul_apply_mul, sum_smul_apply_mul, smul_eq_mul, smul_eq_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left (sum_deficit_le_Fnum_of_isDual hA hl hd hev hD' hsg) ha)
      (mul_le_mul_of_nonneg_left (sum_deficit_le_Fnum_of_isDual hA hl hd hev hE' hsg) hb)
  · have h := sum_deficit_le_Fnum_of_isDual hA hl hd hev hD (isDual_const (d := d) (by omega : 1 ≤ l))
    rw [gam_sub_inv (by omega : 2 ≤ l), ← Finset.sum_mul] at h
    rw [mul_comm]
    exact h
end Formalism.IncomingBounds
