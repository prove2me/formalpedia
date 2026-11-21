-- Prove2me | solution 1 for FreeOrderEPTAS.delta_calibration
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T01:16:55.312647+00:00
-- url     : https://prove2.me/submissions/6efa3403-d170-4c67-99f9-a265063815ff

import Mathlib
import Definitions.Def_FreeOrderEPTAS_typeList
import Definitions.Def_FreeOrderEPTAS_delta

namespace Aux_delta_calibration

open FreeOrderEPTAS

lemma lt2pow (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ k ih => rw [pow_succ]; omega

lemma succ_le_pow (a : ℕ) (ha : 1 ≤ a) : a + 1 ≤ 2 ^ a := by
  induction a, ha using Nat.le_induction with
  | base => norm_num
  | succ k hk ih => rw [pow_succ]; omega

lemma seg_le {ϵ δ v : ℝ} (hϵ : 0 < ϵ) (hδ : 0 < δ) (hv : v ≤ 1) :
    seg ϵ δ v ≤ ⌈Real.log (1 / δ) / Real.log (1 + ϵ)⌉₊ := by
  unfold seg
  split_ifs with h
  · exact Nat.zero_le _
  · push_neg at h
    apply Nat.ceil_mono
    have hl : 0 < Real.log (1 + ϵ) := Real.log_pos (by linarith)
    have hv' : 0 < v := by linarith
    exact div_le_div_of_nonneg_right
      (Real.log_le_log (div_pos hv' hδ) (div_le_div_of_nonneg_right hv hδ.le)) hl.le

lemma numTypes_le {m D n : ℕ} (I : SCInstance m D n) (ϵ δ : ℝ) (S : ℕ)
    (hS : ∀ i j d, typeVec I ϵ δ j i d ≤ S) :
    numTypes I ϵ δ ≤ (S + 1) ^ (m * D) := by
  unfold numTypes
  have hnd : (typeList I ϵ δ).Nodup := List.nodup_dedup _
  rw [← List.toFinset_card_of_nodup hnd]
  have hsub : (typeList I ϵ δ).toFinset ⊆ Fintype.piFinset
      (fun _ : Fin m => Fintype.piFinset (fun _ : Fin D => Finset.range (S + 1))) := by
    intro f hf
    rw [List.mem_toFinset] at hf
    unfold typeList at hf
    rw [List.mem_dedup, List.mem_map] at hf
    obtain ⟨j, _, rfl⟩ := hf
    simp only [Fintype.mem_piFinset, Finset.mem_range]
    intro i d
    have := hS i j d
    omega
  calc _ ≤ _ := Finset.card_le_card hsub
    _ = (S + 1) ^ (m * D) := by
      simp only [Fintype.card_piFinset, Finset.card_range, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
      rw [← pow_mul, mul_comm]

lemma nat_key (a K N : ℕ) (ha : 1 ≤ a) (hK : 1 ≤ K)
    (hN : N ≤ (2 * (8 * (a + 1) * K) ^ 2 * K) ^ a) :
    32 * a * N ^ 2 * K ^ 3 ≤ 2 ^ ((8 * (a + 1) * K) ^ 2) := by
  have h1 : a + 1 ≤ 2 ^ a := succ_le_pow a ha
  have h2 : K ≤ 2 ^ K := (lt2pow K).le
  have ha2 : a ≤ 2 ^ a := (lt2pow a).le
  have hb : 2 * (8 * (a + 1) * K) ^ 2 * K ≤ 2 ^ (7 + 2 * a + 3 * K) := by
    calc 2 * (8 * (a + 1) * K) ^ 2 * K = 128 * (a + 1) ^ 2 * K ^ 3 := by ring
      _ ≤ 128 * (2 ^ a) ^ 2 * (2 ^ K) ^ 3 := by gcongr
      _ = 2 ^ (7 + 2 * a + 3 * K) := by ring
  have hN2 : N ^ 2 ≤ 2 ^ ((7 + 2 * a + 3 * K) * a * 2) := by
    have : N ≤ 2 ^ ((7 + 2 * a + 3 * K) * a) := by
      calc N ≤ (2 * (8 * (a + 1) * K) ^ 2 * K) ^ a := hN
        _ ≤ (2 ^ (7 + 2 * a + 3 * K)) ^ a := Nat.pow_le_pow_left hb a
        _ = 2 ^ ((7 + 2 * a + 3 * K) * a) := by rw [← pow_mul]
    calc N ^ 2 ≤ (2 ^ ((7 + 2 * a + 3 * K) * a)) ^ 2 := Nat.pow_le_pow_left this 2
      _ = 2 ^ ((7 + 2 * a + 3 * K) * a * 2) := by rw [← pow_mul]
  have hc : 32 * a * K ^ 3 ≤ 2 ^ (5 + a + 3 * K) := by
    calc 32 * a * K ^ 3 ≤ 32 * 2 ^ a * (2 ^ K) ^ 3 := by gcongr
      _ = 2 ^ (5 + a + 3 * K) := by ring
  have hexp : 5 + a + 3 * K + (7 + 2 * a + 3 * K) * a * 2 ≤ (8 * (a + 1) * K) ^ 2 := by
    have e1 : K ≤ K * K := Nat.le_mul_self K
    have e2 : a * K ≤ a * K * K := Nat.le_mul_of_pos_right _ hK
    have e3 : a * a ≤ a * a * (K * K) := Nat.le_mul_of_pos_right _ (Nat.mul_pos hK hK)
    have e4 : a ≤ a * K := Nat.le_mul_of_pos_right _ hK
    nlinarith
  calc 32 * a * N ^ 2 * K ^ 3 = (32 * a * K ^ 3) * N ^ 2 := by ring
    _ ≤ 2 ^ (5 + a + 3 * K) * 2 ^ ((7 + 2 * a + 3 * K) * a * 2) := Nat.mul_le_mul hc hN2
    _ = 2 ^ (5 + a + 3 * K + (7 + 2 * a + 3 * K) * a * 2) := by rw [← pow_add]
    _ ≤ 2 ^ ((8 * (a + 1) * K) ^ 2) := Nat.pow_le_pow_right (by norm_num) hexp

theorem main {m D n : ℕ} (I : SCInstance m D n) (ϵ : ℝ) (hϵ0 : 0 < ϵ) (hϵ1 : ϵ < 1)
    (hpos : 0 < m * D * numTypes I ϵ (delta ϵ m D)) :
    delta ϵ m D ≤ ϵ ^ 3 / (16 * (numTypes I ϵ (delta ϵ m D) : ℝ) *
      Real.log (2 * (m : ℝ) * (D : ℝ) * (numTypes I ϵ (delta ϵ m D) : ℝ))) := by
  obtain ⟨k, hk⟩ : ∃ k, k = ⌈1 / ϵ⌉₊ := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, C = calib ϵ m D := ⟨_, rfl⟩
  have hCdef : C = (8 * (m * D + 1) * (k + 1)) ^ 2 := by rw [hC, hk]; rfl
  have hδ : delta ϵ m D = 1 / 2 ^ C := by rw [hC]; unfold delta; rw [one_div_pow]
  have hδpos : 0 < delta ϵ m D := by rw [hδ]; positivity
  obtain ⟨N, hN⟩ : ∃ N, N = numTypes I ϵ (delta ϵ m D) := ⟨_, rfl⟩
  rw [← hN] at hpos ⊢
  have hnz := Nat.pos_iff_ne_zero.1 hpos
  rw [mul_ne_zero_iff, mul_ne_zero_iff] at hnz
  obtain ⟨⟨hm0, hD0⟩, hN0⟩ := hnz
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hm0
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hD0
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hN0
  -- k and ϵ
  have hkε : 1 ≤ (k : ℝ) * ϵ := by
    have := Nat.le_ceil (1 / ϵ)
    rw [← hk] at this
    rw [div_le_iff₀ hϵ0] at this
    linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  -- the segment bound
  obtain ⟨S, hS⟩ : ∃ S, S = ⌈Real.log (1 / delta ϵ m D) / Real.log (1 + ϵ)⌉₊ := ⟨_, rfl⟩
  have hSv : ∀ i j d, typeVec I ϵ (delta ϵ m D) j i d ≤ S := by
    intro i j d
    unfold typeVec
    split_ifs
    · rw [hS]; exact seg_le hϵ0 hδpos (I.ℓ_mem i j d).2
    · exact Nat.zero_le _
  have hNle : N ≤ (S + 1) ^ (m * D) := by
    rw [hN]; exact numTypes_le I ϵ _ S hSv
  have hl2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hl2p : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog1 : ϵ / 2 ≤ Real.log (1 + ϵ) := by
    have h := Real.one_sub_inv_le_log_of_pos (by linarith : (0 : ℝ) < 1 + ϵ)
    have h2 : (1 + ϵ)⁻¹ ≤ 1 - ϵ / 2 := by
      rw [← one_div, div_le_iff₀ (show (0 : ℝ) < 1 + ϵ by linarith)]; nlinarith
    linarith
  have hlogδ : Real.log (1 / delta ϵ m D) = C * Real.log 2 := by
    rw [hδ, one_div_one_div, Real.log_pow]
  have hC1 : (1 : ℝ) ≤ C := by
    rw [hCdef]; push_cast
    have hmD : (1 : ℝ) ≤ (m : ℝ) * D := by nlinarith
    have h2 : (1 : ℝ) ≤ ((m : ℝ) * D + 1) * (k + 1) := by nlinarith
    have : (1 : ℝ) ≤ 8 * ((m : ℝ) * D + 1) * (k + 1) := by nlinarith
    nlinarith
  have hSle : S ≤ 2 * C * k := by
    rw [hS, Nat.ceil_le, hlogδ, div_le_iff₀ (show (0 : ℝ) < Real.log (1 + ϵ) by linarith)]
    push_cast
    have h1 : (C : ℝ) * Real.log 2 ≤ C * 1 := by nlinarith
    have h2 : (C : ℝ) * 1 ≤ C * (k * ϵ) := by nlinarith
    have h3 : (C : ℝ) * (k * ϵ) = 2 * C * k * (ϵ / 2) := by ring
    have h4 : 2 * (C : ℝ) * k * (ϵ / 2) ≤ 2 * C * k * Real.log (1 + ϵ) := by
      apply mul_le_mul_of_nonneg_left hlog1; positivity
    linarith
  have hS1 : S + 1 ≤ 2 * (8 * (m * D + 1) * (k + 1)) ^ 2 * (k + 1) := by
    have hC1' : 1 ≤ C := by exact_mod_cast hC1
    rw [← hCdef]
    nlinarith
  have hNle2 : N ≤ (2 * (8 * (m * D + 1) * (k + 1)) ^ 2 * (k + 1)) ^ (m * D) :=
    le_trans hNle (Nat.pow_le_pow_left hS1 _)
  have hkey := nat_key (m * D) (k + 1) N (Nat.one_le_iff_ne_zero.2 (mul_ne_zero hm0 hD0))
    (by omega) hNle2
  rw [← hCdef] at hkey
  have hkeyR : (32 * ((m : ℝ) * D) * (N : ℝ) ^ 2 * ((k : ℝ) + 1) ^ 3) ≤ (2 : ℝ) ^ C := by
    exact_mod_cast hkey
  -- the logarithm
  have hx2 : (2 : ℝ) ≤ 2 * (m : ℝ) * (D : ℝ) * (N : ℝ) := by
    have : (1 : ℝ) ≤ (m : ℝ) * D := by nlinarith
    have : (1 : ℝ) ≤ (m : ℝ) * D * N := by nlinarith
    nlinarith
  have hLpos : 0 < Real.log (2 * (m : ℝ) * (D : ℝ) * (N : ℝ)) := Real.log_pos (by linarith)
  have hLle : Real.log (2 * (m : ℝ) * (D : ℝ) * (N : ℝ)) ≤ 2 * (m : ℝ) * (D : ℝ) * (N : ℝ) := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 2 * (m : ℝ) * (D : ℝ) * (N : ℝ))
    linarith
  have hden : 0 < 16 * (N : ℝ) * Real.log (2 * (m : ℝ) * (D : ℝ) * (N : ℝ)) := by positivity
  rw [le_div_iff₀ hden]
  have hδ2 : delta ϵ m D * (2 : ℝ) ^ C = 1 := by rw [hδ]; field_simp
  have hεK : 1 ≤ (((k : ℝ) + 1) * ϵ) ^ 3 := by
    have : 1 ≤ ((k : ℝ) + 1) * ϵ := by nlinarith
    exact one_le_pow₀ this
  have step1 : delta ϵ m D * (16 * (N : ℝ) * Real.log (2 * (m : ℝ) * (D : ℝ) * (N : ℝ))) ≤
      delta ϵ m D * (16 * (N : ℝ) * (2 * (m : ℝ) * (D : ℝ) * (N : ℝ))) := by
    apply mul_le_mul_of_nonneg_left _ hδpos.le
    apply mul_le_mul_of_nonneg_left hLle; positivity
  have step2 : delta ϵ m D * (16 * (N : ℝ) * (2 * (m : ℝ) * (D : ℝ) * (N : ℝ))) =
      delta ϵ m D * (32 * ((m : ℝ) * D) * (N : ℝ) ^ 2) := by ring
  have hA : 0 ≤ delta ϵ m D * (32 * ((m : ℝ) * D) * (N : ℝ) ^ 2) := by positivity
  have step3 : delta ϵ m D * (32 * ((m : ℝ) * D) * (N : ℝ) ^ 2) ≤
      delta ϵ m D * (32 * ((m : ℝ) * D) * (N : ℝ) ^ 2) * (((k : ℝ) + 1) * ϵ) ^ 3 :=
    le_mul_of_one_le_right hA hεK
  have step4 : delta ϵ m D * (32 * ((m : ℝ) * D) * (N : ℝ) ^ 2) * (((k : ℝ) + 1) * ϵ) ^ 3 =
      (delta ϵ m D * (32 * ((m : ℝ) * D) * (N : ℝ) ^ 2 * ((k : ℝ) + 1) ^ 3)) * ϵ ^ 3 := by ring
  have step5 : delta ϵ m D * (32 * ((m : ℝ) * D) * (N : ℝ) ^ 2 * ((k : ℝ) + 1) ^ 3) ≤ 1 := by
    calc _ ≤ delta ϵ m D * (2 : ℝ) ^ C := mul_le_mul_of_nonneg_left hkeyR hδpos.le
      _ = 1 := hδ2
  have hε3 : 0 ≤ ϵ ^ 3 := by positivity
  have step6 : (delta ϵ m D * (32 * ((m : ℝ) * D) * (N : ℝ) ^ 2 * ((k : ℝ) + 1) ^ 3)) * ϵ ^ 3 ≤
      ϵ ^ 3 := by
    calc _ ≤ 1 * ϵ ^ 3 := mul_le_mul_of_nonneg_right step5 hε3
      _ = ϵ ^ 3 := one_mul _
  linarith

end Aux_delta_calibration

open FreeOrderEPTAS in
theorem solution {m D n : ℕ} (I : SCInstance m D n) (ϵ : ℝ) (hϵ0 : 0 < ϵ) (hϵ1 : ϵ < 1)
    (hpos : 0 < m * D * numTypes I ϵ (delta ϵ m D)) :
    delta ϵ m D ≤ ϵ ^ 3 / (16 * (numTypes I ϵ (delta ϵ m D) : ℝ) *
      Real.log (2 * (m : ℝ) * (D : ℝ) * (numTypes I ϵ (delta ϵ m D) : ℝ))) :=
  Aux_delta_calibration.main I ϵ hϵ0 hϵ1 hpos
