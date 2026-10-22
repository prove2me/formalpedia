-- Prove2me | solution 1 for BanKeskin.KnownSparsity.eq_15
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:33:39.416141+00:00
-- url     : https://prove2.me/submissions/b0081f4c-0989-4a00-a46b-7d02680f60ea

import Mathlib
import Definitions.Def_BanKeskin_KnownSparsity_Model

set_option autoImplicit false
open MeasureTheory BanKeskin.KnownSparsity

theorem qqf_not_both (k : ℕ) (h1 : inM1 k) (h2 : inM2 k) : False := by
  obtain ⟨L, hL, rfl⟩ := h1
  obtain ⟨L', hL', h⟩ := h2
  have h' : L ^ 2 = L' ^ 2 + 1 := h.symm ▸ rfl
  have : L' < L := by nlinarith
  have : L ≤ L' := by nlinarith
  omega

theorem solution {d : ℕ} {S : Finset (Fin (d + 1))} {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (M : Model d S Ω P)
    (t : ℕ) (ht : 5 ≤ t) :
    (1 / 8 : ℝ) * (M.m1 - M.m2) ^ 2 * Real.sqrt (t : ℝ) ≤ M.J t := by
  classical
  set A := (Finset.Icc 1 t).filter inM1 with hA
  set B := (Finset.Icc 1 t).filter inM2 with hB
  have hsplit : ∀ f : ℕ → ℝ, ∑ k ∈ Finset.Icc 1 t, chi k * f k =
      ∑ k ∈ A, f k + ∑ k ∈ B, f k := by
    intro f
    rw [hA, hB, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h1 : inM1 k
    · have h2 : ¬ inM2 k := fun h2 => qqf_not_both k h1 h2
      simp [chi, h1, h2]
    · by_cases h2 : inM2 k
      · simp [chi, h1, h2]
      · simp [chi, h1, h2]
  set a : ℕ := A.card with ha
  set b : ℕ := B.card with hb
  have hAp : ∀ k ∈ A, M.experimentPrice k = M.m1 := by
    intro k hk
    have : inM1 k := (Finset.mem_filter.1 hk).2
    simp [Model.experimentPrice, this]
  have hBp : ∀ k ∈ B, M.experimentPrice k = M.m2 := by
    intro k hk
    have h2 : inM2 k := (Finset.mem_filter.1 hk).2
    have h1 : ¬ inM1 k := fun h1 => qqf_not_both k h1 h2
    simp [Model.experimentPrice, h1]
  -- cardinality lower bounds
  set s := Nat.sqrt t with hs
  have hs2 : 2 ≤ s := by
    rw [hs, Nat.le_sqrt]; omega
  have hss : s * s ≤ t := Nat.sqrt_le t
  have hlt : t < (s + 1) * (s + 1) := Nat.lt_succ_sqrt t
  have haS : s ≤ a := by
    have : (Finset.Icc 1 s).card ≤ A.card := by
      refine Finset.card_le_card_of_injOn (fun L => L ^ 2) ?_ ?_
      · intro L hL
        have hL' := Finset.mem_Icc.1 (Finset.mem_coe.1 hL)
        refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨?_, ?_⟩, ⟨L, hL'.1, rfl⟩⟩)
        · nlinarith
        · nlinarith
      · intro x _ y _ h
        exact Nat.pow_left_injective (by norm_num) h
    simpa using this
  have hbS : s - 1 ≤ b := by
    have : (Finset.Icc 1 (s - 1)).card ≤ B.card := by
      refine Finset.card_le_card_of_injOn (fun L => L ^ 2 + 1) ?_ ?_
      · intro L hL
        have hL' := Finset.mem_Icc.1 (Finset.mem_coe.1 hL)
        refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨?_, ?_⟩, ⟨L, hL'.1, rfl⟩⟩)
        · nlinarith
        · obtain ⟨c, hc⟩ : ∃ c, s = c + 1 := ⟨s - 1, by omega⟩
          have : L ≤ c := by simpa [hc] using hL'.2
          nlinarith
      · intro x _ y _ h
        have h' : x ^ 2 = y ^ 2 := by simpa using h
        exact Nat.pow_left_injective (by norm_num) h'
    simpa using this
  -- evaluate J
  have hsum1 : ∑ k ∈ Finset.Icc 1 t, chi k = (a : ℝ) + b := by
    have := hsplit (fun _ => 1)
    simpa [ha, hb] using this
  have hmean : M.meanPrice t = ((a : ℝ) * M.m1 + b * M.m2) / ((a : ℝ) + b) := by
    unfold Model.meanPrice
    have e1 : ∑ k ∈ A, M.experimentPrice k = ∑ k ∈ A, M.m1 := Finset.sum_congr rfl hAp
    have e2 : ∑ k ∈ B, M.experimentPrice k = ∑ k ∈ B, M.m2 := Finset.sum_congr rfl hBp
    rw [hsum1, hsplit (fun k => M.experimentPrice k), e1, e2]
    simp [ha, hb]
  have hJ : M.J t = (a : ℝ) * (M.m1 - M.meanPrice t) ^ 2 + b * (M.m2 - M.meanPrice t) ^ 2 := by
    unfold Model.J
    rw [hsplit (fun k => (M.experimentPrice k - M.meanPrice t) ^ 2)]
    have e1 : ∑ k ∈ A, (M.experimentPrice k - M.meanPrice t) ^ 2 =
        ∑ k ∈ A, (M.m1 - M.meanPrice t) ^ 2 :=
      Finset.sum_congr rfl (fun k hk => by rw [hAp k hk])
    have e2 : ∑ k ∈ B, (M.experimentPrice k - M.meanPrice t) ^ 2 =
        ∑ k ∈ B, (M.m2 - M.meanPrice t) ^ 2 :=
      Finset.sum_congr rfl (fun k hk => by rw [hBp k hk])
    rw [e1, e2]
    simp [ha, hb]
  have hapos : (0 : ℝ) < a := by
    have : (2 : ℝ) ≤ a := by exact_mod_cast hs2.trans haS
    linarith
  have hbpos : (0 : ℝ) < b := by
    have : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
    linarith
  have hJ2 : M.J t = (a : ℝ) * b / ((a : ℝ) + b) * (M.m1 - M.m2) ^ 2 := by
    rw [hJ, hmean]
    field_simp
    ring
  -- real inequalities
  have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hs2
  have haR : (s : ℝ) ≤ a := by exact_mod_cast haS
  have hbR : (s : ℝ) - 1 ≤ b := by
    have : ((s - 1 : ℕ) : ℝ) ≤ b := by exact_mod_cast hbS
    rwa [Nat.cast_sub (by omega), Nat.cast_one] at this
  have hsqrt : Real.sqrt (t : ℝ) ≤ s + 1 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have : (t : ℝ) < (s + 1) * (s + 1) := by exact_mod_cast hlt
    nlinarith
  have key : (s - 1 : ℝ) / 2 ≤ (a : ℝ) * b / ((a : ℝ) + b) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hfin : Real.sqrt (t : ℝ) / 8 ≤ (a : ℝ) * b / ((a : ℝ) + b) := by
    nlinarith
  rw [hJ2]
  have h0 : 0 ≤ (M.m1 - M.m2) ^ 2 := sq_nonneg _
  calc (1 / 8 : ℝ) * (M.m1 - M.m2) ^ 2 * Real.sqrt t
      = Real.sqrt t / 8 * (M.m1 - M.m2) ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hfin h0
