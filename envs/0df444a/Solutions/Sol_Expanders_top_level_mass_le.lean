-- Prove2me | solution 1 for Expanders.top_level_mass_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:40:21.24806+00:00
-- url     : https://prove2.me/submissions/d90829ef-9a81-4fb0-872f-de316dd98f13

module
public import Mathlib
public import Definitions.Def_ExpanderLib_NilliBall
public import Theorems.Thm_Expanders_card_level_succ_le

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open Expanders
variable {V : Type*} [Fintype V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] {d k : ℕ} (B : Finset V) (h : V → ℕ)
namespace Expanders
theorem _root_.solution (hd1 : 1 ≤ d) (hd : G.IsRegularOfDegree d)
    (hB : ∀ v ∈ B, h v ≤ k)
    (hstep : ∀ v ∈ B, ∀ w ∈ B, G.Adj v w → h w ≤ h v + 1)
    (hpar : ∀ v ∈ B, ∃ w ∈ B, G.Adj v w ∧ h w ≤ h v - 1) {q : ℝ} (hq : 0 ≤ q)
    (hqd : q * ((d : ℝ) - 1) = 1) :
    ((k : ℝ) + 1) * ∑ v ∈ B.filter (fun v => h v = k), q ^ h v ≤ ∑ v ∈ B, q ^ h v := by
  classical
  set n : ℕ → ℝ := fun i => ((B.filter (fun v => h v = i)).card : ℝ) with hn
  have hlev : ∀ i, ∑ v ∈ B.filter (fun v => h v = i), q ^ h v = n i * q ^ i := by
    intro i
    rw [Finset.sum_congr rfl (fun v hv => by rw [(Finset.mem_filter.mp hv).2]),
      Finset.sum_const, nsmul_eq_mul]
  have htot : ∑ v ∈ B, q ^ h v = ∑ i ∈ Finset.range (k + 1), n i * q ^ i := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := h) (t := Finset.range (k + 1))
      (fun v hv => Finset.mem_range.mpr (Nat.lt_succ_of_le (hB v hv)))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← hlev i]
  have hstep1 : ∀ i, n (i + 1) * q ^ (i + 1) ≤ n i * q ^ i := by
    intro i
    have hc := card_level_succ_le G B h hd hstep hpar i
    have hc' : n (i + 1) ≤ n i * ((d : ℝ) - 1) := by
      simp only [hn]
      have : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by push_cast [Nat.cast_sub hd1]; ring
      rw [← this]; exact_mod_cast hc
    calc n (i + 1) * q ^ (i + 1) ≤ n i * ((d : ℝ) - 1) * q ^ (i + 1) :=
          mul_le_mul_of_nonneg_right hc' (pow_nonneg hq _)
      _ = n i * q ^ i * (q * ((d : ℝ) - 1)) := by ring
      _ = n i * q ^ i := by rw [hqd, mul_one]
  have hmono : ∀ j i, n (i + j) * q ^ (i + j) ≤ n i * q ^ i := by
    intro j
    induction j with
    | zero => intro i; simp
    | succ j ih => intro i; exact (hstep1 (i + j)).trans (ih i)
  rw [hlev, htot]
  calc ((k : ℝ) + 1) * (n k * q ^ k) = ∑ i ∈ Finset.range (k + 1), n k * q ^ k := by
        simp
    _ ≤ ∑ i ∈ Finset.range (k + 1), n i * q ^ i := by
        refine Finset.sum_le_sum (fun i hi => ?_)
        have hik : i + (k - i) = k := by
          have := Finset.mem_range.mp hi; omega
        have := hmono (k - i) i
        rwa [hik] at this
end Expanders
