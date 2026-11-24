-- Prove2me | solution 1 for DataDrivenRO.KS.qL_qR_mem_ksRegion
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T01:24:36.319933+00:00
-- url     : https://prove2.me/submissions/559e7922-beb8-4323-9556-3f237ef87296

import Mathlib
import Definitions.Def_DataDrivenRO_KS_Setting

open MeasureTheory
open DataDrivenRO.KS

theorem ks_lawOn_apply {n : ℕ} (x q : Fin n → ℝ) (hq : ∀ j, 0 ≤ q j) (S : Set ℝ) :
    lawOn x q S = ENNReal.ofReal (∑ j, q j * S.indicator 1 (x j)) := by
  rw [ENNReal.ofReal_sum_of_nonneg (f := fun j => q j * S.indicator 1 (x j)) (fun j _ =>
    mul_nonneg (hq j) (Set.indicator_nonneg (fun _ _ => zero_le_one) _))]
  simp only [lawOn, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    Measure.dirac_apply, smul_eq_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases h : x j ∈ S <;> simp [h]

theorem ks_cum (N F : ℕ) (Γ : ℝ) (g : ℕ → ℝ)
    (hg : ∀ k, g k = if k = 0 then Γ else if k ≤ F then 1 / (N : ℝ)
      else if k = F + 1 then 1 - Γ - (F : ℝ) / N else 0)
    (r : ℕ) : ∑ k ∈ Finset.range (r + 1), g k = if r ≤ F then Γ + (r : ℝ) / N else 1 := by
  induction r with
  | zero => simp [hg]
  | succ r ih =>
    rw [Finset.sum_range_succ, ih, hg]
    split_ifs <;> first | contradiction | omega |
      (rw [show (r : ℝ) = F by exact_mod_cast (show r = F by omega)]; ring) | (push_cast; ring)

theorem ks_T (N : ℕ) (g : ℕ → ℝ) (r : ℕ) (hr : r ≤ N + 1) :
    ∑ j : Fin (N + 2), (if (j : ℕ) ≤ r then g j else 0) = ∑ k ∈ Finset.range (r + 1), g k := by
  rw [Fin.sum_univ_eq_sum_range (fun k => if k ≤ r then g k else 0) (N + 2), ← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

theorem ks_Tgt (N : ℕ) (g : ℕ → ℝ) (c : ℕ) (hc : c ≤ N + 1) :
    ∑ j : Fin (N + 2), (if c < (j : ℕ) then g j else 0) =
      ∑ k ∈ Finset.range (N + 2), g k - ∑ k ∈ Finset.range (c + 1), g k := by
  rw [← ks_T N g c hc, ← ks_T N g (N + 1) le_rfl, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have := j.isLt
  split_ifs <;> first | omega | ring

theorem ks_region {d N : ℕ} (uhat : Fin d → Fin (N + 2) → ℝ) (Γ : ℝ) (i : Fin d)
    (hmono : Monotone (uhat i)) (q : Fin (N + 2) → ℝ) (hq0 : ∀ j, 0 ≤ q j)
    (htot : ∑ j, q j = 1)
    (hlow : ∀ j : Fin N, ((j : ℝ) + 1) / N - Γ ≤
      ∑ k : Fin (N + 2), (if (k : ℕ) ≤ (j : ℕ) + 1 then q k else 0))
    (hup : ∀ j : Fin N,
      ∑ k : Fin (N + 2), (if (k : ℕ) < (j : ℕ) + 1 then q k else 0) ≤ (j : ℝ) / N + Γ) :
    lawOn (uhat i) q ∈ ksRegion uhat Γ i := by
  have hind : ∀ (S : Set ℝ) x, 0 ≤ S.indicator (1 : ℝ → ℝ) x :=
    fun S x => Set.indicator_nonneg (fun _ _ => zero_le_one) x
  refine ⟨⟨?_⟩, ?_, fun j => ⟨?_, ?_⟩⟩
  · rw [ks_lawOn_apply _ _ hq0]
    simp [htot]
  · rw [ks_lawOn_apply _ _ hq0, ENNReal.ofReal_eq_zero]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro k _
    have hk1 : uhat i 0 ≤ uhat i k := hmono (Fin.zero_le k)
    have hk2 : uhat i k ≤ uhat i (Fin.last (N + 1)) := hmono (Fin.le_last k)
    simp [Set.indicator, hk1, hk2]
  · rw [ks_lawOn_apply _ _ hq0]
    apply ENNReal.ofReal_le_ofReal
    refine le_trans (hlow j) (Finset.sum_le_sum fun k _ => ?_)
    split_ifs with hk
    · have : uhat i k ≤ uhat i (obsIdx j) :=
        hmono (Fin.le_iff_val_le_val.2 (by show (k : ℕ) ≤ (j : ℕ) + 1; omega))
      simp [Set.indicator, this]
    · exact mul_nonneg (hq0 k) (hind _ _)
  · rw [ks_lawOn_apply _ _ hq0]
    apply ENNReal.ofReal_le_ofReal
    refine le_trans (Finset.sum_le_sum fun k _ => ?_) (hup j)
    split_ifs with hk
    · by_cases h : uhat i k < uhat i (obsIdx j) <;> simp [Set.indicator, h, hq0 k]
    · have : uhat i (obsIdx j) ≤ uhat i k :=
        hmono (Fin.le_iff_val_le_val.2 (by show (j : ℕ) + 1 ≤ (k : ℕ); omega))
      simp [Set.indicator, not_lt.2 this]

theorem solution {d N : ℕ} (uhat : Fin d → Fin (N + 2) → ℝ) (Γ : ℝ)
    (hN : 0 < N) (hΓ0 : 0 < Γ) (hΓ1 : Γ < 1) (hmono : ∀ i, Monotone (uhat i)) (i : Fin d) :
    lawOn (uhat i) (qL N Γ) ∈ ksRegion uhat Γ i ∧ lawOn (uhat i) (qR N Γ) ∈ ksRegion uhat Γ i := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨F, hFdef⟩ : ∃ F, F = ⌊(N : ℝ) * (1 - Γ)⌋₊ := ⟨_, rfl⟩
  have hF1 : (F : ℝ) ≤ N * (1 - Γ) := hFdef ▸ Nat.floor_le (by nlinarith)
  have hF2 : (N : ℝ) * (1 - Γ) < F + 1 := hFdef ▸ Nat.lt_floor_add_one _
  let g : ℕ → ℝ := fun k => if k = 0 then Γ else if k ≤ F then 1 / (N : ℝ)
    else if k = F + 1 then 1 - Γ - (F : ℝ) / N else 0
  have hg : ∀ k, g k = if k = 0 then Γ else if k ≤ F then 1 / (N : ℝ)
      else if k = F + 1 then 1 - Γ - (F : ℝ) / N else 0 := fun k => rfl
  have hqL : ∀ j : Fin (N + 2), qL N Γ j = g j := by
    intro j; rw [hg, hFdef]; rfl
  have hFN : F < N := by
    have : (F : ℝ) < N := by nlinarith
    exact_mod_cast this
  have hg0 : ∀ k, 0 ≤ g k := by
    intro k
    rw [hg]
    split_ifs
    · exact hΓ0.le
    · positivity
    · have : (F : ℝ) / N ≤ 1 - Γ := by rw [div_le_iff₀ hNr]; linarith
      linarith
    · exact le_rfl
  have hC := ks_cum N F Γ g hg
  have htot : ∑ k ∈ Finset.range (N + 2), g k = 1 := by
    rw [hC (N + 1), if_neg (by omega)]
  have hlowC : ∀ r, r ≤ N → (r : ℝ) / N - Γ ≤ ∑ k ∈ Finset.range (r + 1), g k := by
    intro r hr
    rw [hC r]
    split_ifs
    · linarith
    · have : (r : ℝ) / N ≤ 1 := by
        rw [div_le_one hNr]; exact_mod_cast hr
      linarith
  have hupC : ∀ r, ∑ k ∈ Finset.range (r + 1), g k ≤ Γ + (r : ℝ) / N := by
    intro r
    rw [hC r]
    split_ifs with h
    · exact le_rfl
    · have h1 : (F : ℝ) + 1 ≤ r := by exact_mod_cast (by omega : F + 1 ≤ r)
      have : 1 - Γ < (r : ℝ) / N := by rw [lt_div_iff₀ hNr]; nlinarith
      linarith
  have hsumL : ∑ j : Fin (N + 2), qL N Γ j = 1 := by
    simp only [hqL]
    rw [Fin.sum_univ_eq_sum_range g (N + 2)]
    exact htot
  constructor
  · refine ks_region uhat Γ i (hmono i) _ (fun j => by rw [hqL]; exact hg0 _) hsumL ?_ ?_
    · intro j
      simp only [hqL]
      rw [ks_T N g _ (by omega)]
      have := hlowC ((j : ℕ) + 1) (by omega)
      push_cast at this
      exact this
    · intro j
      simp only [hqL, Nat.lt_add_one_iff]
      rw [ks_T N g _ (by omega)]
      have := hupC j
      linarith
  · have hqR : ∀ j : Fin (N + 2), qR N Γ j = qL N Γ j.rev := fun j => rfl
    refine ks_region uhat Γ i (hmono i) _ (fun j => by rw [hqR, hqL]; exact hg0 _) ?_ ?_ ?_
    · simp only [hqR]
      exact (Equiv.sum_comp Fin.revPerm (qL N Γ)).trans hsumL
    · intro j
      have hre : ∑ k : Fin (N + 2), (if (k : ℕ) ≤ (j : ℕ) + 1 then qR N Γ k else 0) =
          ∑ m : Fin (N + 2), (if N - ((j : ℕ) + 1) < (m : ℕ) then g m else 0) := by
        rw [← Equiv.sum_comp Fin.revPerm]
        refine Finset.sum_congr rfl (fun m _ => ?_)
        have hm := m.isLt
        have hj := j.isLt
        have hv : ((Fin.revPerm m : Fin (N + 2)) : ℕ) = N + 1 - m := by
          simp [Fin.revPerm, Fin.val_rev]
        rw [hqR, hv]
        have hrr : (Fin.revPerm m).rev = m := by simp [Fin.revPerm]
        rw [hrr, hqL]
        split_ifs <;> first | rfl | omega
      rw [hre, ks_Tgt N g _ (by omega), htot]
      have hj := j.isLt
      have := hupC (N - ((j : ℕ) + 1))
      rw [Nat.cast_sub (by omega)] at this
      push_cast at this
      have e2 : ((N : ℝ) - ((j : ℝ) + 1)) / N = 1 - ((j : ℝ) + 1) / N := by
        field_simp
      linarith
    · intro j
      have hre : ∑ k : Fin (N + 2), (if (k : ℕ) < (j : ℕ) + 1 then qR N Γ k else 0) =
          ∑ m : Fin (N + 2), (if N - (j : ℕ) < (m : ℕ) then g m else 0) := by
        rw [← Equiv.sum_comp Fin.revPerm]
        refine Finset.sum_congr rfl (fun m _ => ?_)
        have hm := m.isLt
        have hj := j.isLt
        have hv : ((Fin.revPerm m : Fin (N + 2)) : ℕ) = N + 1 - m := by
          simp [Fin.revPerm, Fin.val_rev]
        rw [hqR, hv]
        have hrr : (Fin.revPerm m).rev = m := by simp [Fin.revPerm]
        rw [hrr, hqL]
        split_ifs <;> first | rfl | omega
      rw [hre, ks_Tgt N g _ (by omega), htot]
      have hj := j.isLt
      have := hlowC (N - (j : ℕ)) (by omega)
      rw [Nat.cast_sub (by omega)] at this
      have e2 : ((N : ℝ) - (j : ℝ)) / N = 1 - (j : ℝ) / N := by
        field_simp
      linarith
