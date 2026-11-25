-- Prove2me | solution 1 for Expanders.nilli_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:50:08.880797+00:00
-- url     : https://prove2.me/submissions/4ed56a4d-9d3b-4f1a-aa0f-09c6282f1e5b

module
public import Mathlib
public import Definitions.Def_ExpanderLib_NilliBall
public import Theorems.Thm_Expanders_quadForm_eq_of_split
public import Theorems.Thm_Expanders_top_level_mass_le

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open Expanders
variable {V : Type*} [Fintype V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] {d k : ℕ} (B : Finset V) (h : V → ℕ)
namespace Expanders
theorem _root_.solution (hd2 : 2 ≤ d) (hd : G.IsRegularOfDegree d)
    (hB : ∀ v ∈ B, h v ≤ k)
    (hout : ∀ v ∈ B, ∀ w, G.Adj v w → w ∉ B → h v = k)
    (hstep : ∀ v ∈ B, ∀ w ∈ B, G.Adj v w → h w ≤ h v + 1)
    (hpar : ∀ v ∈ B, ∃ w ∈ B, G.Adj v w ∧ h w ≤ h v - 1) :
    (2 * Real.sqrt (d - 1) - (2 * Real.sqrt (d - 1) - 1) / (k + 1)) *
        dotProduct (nilliVec (Real.sqrt (d - 1)) B h) (nilliVec (Real.sqrt (d - 1)) B h) ≤
      dotProduct (nilliVec (Real.sqrt (d - 1)) B h)
        (G.adjMatrix ℝ *ᵥ nilliVec (Real.sqrt (d - 1)) B h) := by
  classical
  set s := Real.sqrt ((d : ℝ) - 1) with hs
  have hd1 : (1 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd2
    linarith
  have hs1 : 1 ≤ s := Real.one_le_sqrt.mpr hd1
  have hs0 : 0 < s := by linarith
  have hss : s ^ 2 = (d : ℝ) - 1 := Real.sq_sqrt (by linarith)
  set r := s⁻¹ with hr
  have hr0 : 0 ≤ r := inv_nonneg.mpr hs0.le
  set f := nilliVec s B h with hf
  have hfB : ∀ v ∈ B, f v = r ^ h v := fun v hv => by simp [hf, nilliVec, hv, hr]
  have hfn : ∀ v, v ∉ B → f v = 0 := fun v hv => by simp [hf, nilliVec, hv]
  -- oriented edge contributions
  set c : V → V → ℝ := fun v w =>
    if v ∈ B ∧ (w ∉ B ∨ h w = h v + 1) then (f v - f w) ^ 2 else 0 with hc
  have hsplit : ∀ v, ∀ w ∈ G.neighborFinset v, (f v - f w) ^ 2 = c v w + c w v := by
    intro v w hw
    rw [mem_neighborFinset] at hw
    by_cases hv : v ∈ B <;> by_cases hw' : w ∈ B
    · have h1 := hstep v hv w hw' hw
      have h2 := hstep w hw' v hv hw.symm
      rcases (show h w = h v + 1 ∨ h v = h w + 1 ∨ h v = h w by omega) with e | e | e
      · have hc1 : c v w = (f v - f w) ^ 2 := by simp [hc, hv, e]
        have hc2 : c w v = 0 := by simp [hc, hv, show h v ≠ h w + 1 by omega]
        rw [hc1, hc2, add_zero]
      · have hc1 : c v w = 0 := by simp [hc, hw', show h w ≠ h v + 1 by omega]
        have hc2 : c w v = (f w - f v) ^ 2 := by simp [hc, hw', e]
        rw [hc1, hc2, zero_add]; ring
      · simp [hc, hv, hw', e, hfB v hv, hfB w hw']
    · simp [hc, hv, hw']
    · simp [hc, hv, hw']; ring
    · simp [hc, hv, hw', hfn v hv, hfn w hw']
  rw [quadForm_eq_of_split G hd f c hsplit]
  have hdot : dotProduct f f = ∑ v, f v ^ 2 := by simp [dotProduct, sq]
  rw [hdot]
  -- the top-layer mass
  set M : ℝ := ∑ v, if v ∈ B ∧ h v = k then f v ^ 2 else 0 with hM
  -- per-vertex estimate
  have hvert : ∀ v, ∑ w ∈ G.neighborFinset v, c v w ≤
      (d : ℝ) * f v ^ 2 - 2 * s * f v ^ 2 +
        (2 * s - 1) * (if v ∈ B ∧ h v = k then f v ^ 2 else 0) := by
    intro v
    by_cases hv : v ∈ B
    swap
    · simp [hc, hv, hfn v hv]
    obtain ⟨w0, hw0B, hvw0, hw0⟩ := hpar v hv
    set C := (G.neighborFinset v).filter (fun w => w ∉ B ∨ h w = h v + 1) with hC
    have hsumC : ∑ w ∈ G.neighborFinset v, c v w = ∑ w ∈ C, (f v - f w) ^ 2 := by
      rw [hC, Finset.sum_filter]
      refine Finset.sum_congr rfl (fun w _ => ?_)
      simp [hc, hv]
    have hcardC : (C.card : ℝ) ≤ (d : ℝ) - 1 := by
      have hsub : C ⊆ (G.neighborFinset v).erase w0 := by
        intro w hw
        rw [hC, Finset.mem_filter] at hw
        rw [Finset.mem_erase]
        refine ⟨?_, hw.1⟩
        rintro rfl
        rcases hw.2 with h' | h'
        · exact h' hw0B
        · omega
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem (by simpa using hvw0), card_neighborFinset_eq_degree,
        hd v] at h1
      have h2 : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
        push_cast [Nat.cast_sub (by omega : 1 ≤ d)]; ring
      rw [← h2]; exact_mod_cast h1
    have hfv : 0 ≤ f v ^ 2 := sq_nonneg _
    rw [hsumC]
    by_cases hk : h v = k
    · have hterm : ∀ w ∈ C, (f v - f w) ^ 2 ≤ f v ^ 2 := by
        intro w hw
        rw [hC, Finset.mem_filter] at hw
        have hwB : w ∉ B := by
          rcases hw.2 with h' | h'
          · exact h'
          · intro hwB; have := hB w hwB; omega
        rw [hfn w hwB, sub_zero]
      refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
      rw [nsmul_eq_mul, if_pos ⟨hv, hk⟩]
      nlinarith
    · have hterm : ∀ w ∈ C, (f v - f w) ^ 2 ≤ f v ^ 2 * (1 - r) ^ 2 := by
        intro w hw
        rw [hC, Finset.mem_filter] at hw
        have hwB : w ∈ B := by
          by_contra hwB
          exact hk (hout v hv w (by simpa using hw.1) hwB)
        have hlev : h w = h v + 1 := by
          rcases hw.2 with h' | h'
          · exact absurd hwB h'
          · exact h'
        rw [hfB w hwB, hfB v hv, hlev]
        apply le_of_eq; ring
      refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
      rw [nsmul_eq_mul, if_neg (fun h' => hk h'.2)]
      have hkey : ((d : ℝ) - 1) * (1 - r) ^ 2 = d - 2 * s := by
        rw [← hss, hr]
        field_simp
        linear_combination hss
      have hnn : 0 ≤ f v ^ 2 * (1 - r) ^ 2 := by positivity
      calc (C.card : ℝ) * (f v ^ 2 * (1 - r) ^ 2) ≤ ((d : ℝ) - 1) * (f v ^ 2 * (1 - r) ^ 2) :=
            mul_le_mul_of_nonneg_right hcardC hnn
        _ = (d : ℝ) * f v ^ 2 - 2 * s * f v ^ 2 + (2 * s - 1) * 0 := by
            rw [show ((d : ℝ) - 1) * (f v ^ 2 * (1 - r) ^ 2) =
              (((d : ℝ) - 1) * (1 - r) ^ 2) * f v ^ 2 by ring, hkey]; ring
  have hsum : ∑ v, ∑ w ∈ G.neighborFinset v, c v w ≤
      (d : ℝ) * ∑ v, f v ^ 2 - 2 * s * ∑ v, f v ^ 2 + (2 * s - 1) * M := by
    refine (Finset.sum_le_sum (fun v _ => hvert v)).trans (le_of_eq ?_)
    rw [hM, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
  -- the top layer bound
  have hq : r ^ 2 * ((d : ℝ) - 1) = 1 := by
    rw [← hss, hr]; field_simp
  have hmass := top_level_mass_le G B h (by omega) hd hB hstep hpar (sq_nonneg r) hq
  have hpow : ∀ v ∈ B, (r ^ 2) ^ h v = f v ^ 2 := by
    intro v hv; rw [hfB v hv, ← pow_mul, ← pow_mul, mul_comm]
  have hMeq : M = ∑ v ∈ B.filter (fun v => h v = k), (r ^ 2) ^ h v := by
    rw [hM, ← Finset.sum_filter, Finset.filter_and]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
    refine Finset.sum_congr ?_ (fun v hv => (hpow v ?_).symm)
    · ext v; simp
    · simp only [Finset.mem_filter] at hv; exact hv.1
  have hFeq : ∑ v, f v ^ 2 = ∑ v ∈ B, (r ^ 2) ^ h v := by
    rw [← Finset.sum_subset (Finset.subset_univ B) (fun v _ hv => by rw [hfn v hv]; ring)]
    exact Finset.sum_congr rfl (fun v hv => (hpow v hv).symm)
  rw [← hMeq, ← hFeq] at hmass
  have hk1 : (0 : ℝ) < k + 1 := by positivity
  have hMle : M ≤ (∑ v, f v ^ 2) / (k + 1) := by
    rw [le_div_iff₀ hk1]; linarith
  have h2s : 0 ≤ 2 * s - 1 := by linarith
  have := mul_le_mul_of_nonneg_left hMle h2s
  rw [sub_mul, div_mul_eq_mul_div]
  rw [mul_div_assoc'] at this
  linarith
end Expanders
