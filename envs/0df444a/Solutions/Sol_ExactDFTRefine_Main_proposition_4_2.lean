-- Prove2me | solution 1 for ExactDFTRefine.Main.proposition_4_2
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-22T23:01:36.442805+00:00
-- url     : https://prove2.me/submissions/60222521-7069-4c4f-b0ac-6b75bd1d734c

import Mathlib
import Definitions.Def_ExactDFTRefine_Main_Moments
import Theorems.Thm_ExactDFTRefine_Main_proposition_3_2
import Theorems.Thm_ExactDFTRefine_Main_eq_11
import Theorems.Thm_ExactDFTRefine_Main_lemma_4_1
import Theorems.Thm_ExactDFTRefine_Main_eq_15

set_option maxRecDepth 100000

namespace ExactDFTRefine.Main

private theorem splitBlock_mem_le (J R p : ℕ) (hJ : 0 < J)
    (hp : p ∈ splitBlock J R) : p ≤ J := by
  unfold splitBlock at hp
  by_cases hRJ : R ≤ J
  · rw [if_pos hRJ, Multiset.mem_singleton] at hp
    omega
  · rw [if_neg hRJ, Multiset.mem_add] at hp
    rcases hp with hp | hp
    · obtain ⟨-, rfl⟩ := Multiset.mem_replicate.mp hp
      exact le_rfl
    · by_cases hzero : R % J = 0
      · rw [if_pos hzero] at hp
        simp at hp
      · rw [if_neg hzero, Multiset.mem_singleton] at hp
        subst p
        exact (Nat.mod_lt _ hJ).le

private theorem pprime_mem_le (P T : Multiset ℕ) (v J B p : ℕ) (hJ : 0 < J)
    (hp : p ∈ Pprime P T v J B) : p ≤ J := by
  rw [Pprime, splitBlocks] at hp
  obtain ⟨R, hR, hp⟩ := Multiset.mem_bind.mp hp
  exact splitBlock_mem_le _ _ _ hJ hp

private theorem tprime_mem_ge (T : Multiset ℕ) (v B q : ℕ)
    (hq : q ∈ Tprime T v B) : B ≤ q := by
  rw [Tprime, completeTargets] at hq
  obtain ⟨K, hK, rfl⟩ := Multiset.mem_map.mp hq
  exact le_max_right _ _

private theorem rank_separation_aux (v : ℕ) (hJ : 0 < 20 ^ v)
    (hJB : 20 ^ v < 21 ^ v) :
    ∀ p ∈ Pprime blocksP targetsT v (20 ^ v) (21 ^ v),
      ∀ q ∈ Tprime targetsT v (21 ^ v), p < q := by
  intro p hp q hq
  have hpJ : p ≤ 20 ^ v :=
    pprime_mem_le blocksP targetsT v (20 ^ v) (21 ^ v) p hJ hp
  have hqB : 21 ^ v ≤ q := tprime_mem_ge targetsT v (21 ^ v) q hq
  omega

private theorem moment_nonneg_aux (t : ℝ) (A : Multiset ℕ) : 0 ≤ moment t A := by
  unfold moment
  apply Multiset.sum_nonneg
  intro x hx
  obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hx
  obtain ⟨n, hn, hrn⟩ := Multiset.mem_bind.mp hr
  change r ∈ ({(n : ℝ)} : Multiset ℝ) at hrn
  rw [Multiset.mem_singleton] at hrn
  rw [hrn]
  exact Real.rpow_nonneg (Nat.cast_nonneg n) t

private theorem moment_comparison_aux (v : ℕ) (hv : 1 ≤ v)
    (hTpos : 0 < moment tpar targetsT)
    (hPT : moment tpar blocksP / moment tpar targetsT ≤ 1 - eps)
    (hPone : moment 1 blocksP / ((20 : ℝ) ^ Cpar * moment tpar targetsT) ≤ gam)
    (hCard : 21 * (Multiset.card targetsT : ℝ) /
      ((20 : ℝ) ^ Cpar * moment tpar targetsT) ≤ eta)
    (hnum : (1 - eps) ^ v + 2 * gam ^ v + 2 * eta ^ v < 1) :
    moment tpar (Pprime blocksP targetsT v (20 ^ v) (21 ^ v)) <
      moment tpar (Tprime targetsT v (21 ^ v)) := by
  have ht0 : 0 ≤ tpar := by norm_num [tpar, Cpar]
  have ht1 : tpar ≤ 1 := by norm_num [tpar, Cpar]
  have hJ : 0 < 20 ^ v := by positivity
  have hJB : 20 ^ v < 21 ^ v :=
    Nat.pow_lt_pow_left (by norm_num) (by omega)
  obtain ⟨hPupper, hTupper⟩ :=
    lemma_4_1 tpar ht0 ht1 v hv (20 ^ v) (21 ^ v) hJ hJB
  have hA0 : 0 ≤ moment tpar blocksP := moment_nonneg_aux _ _
  have hZ0 : 0 ≤ moment 1 blocksP := moment_nonneg_aux _ _
  have hRpos : 0 < (20 : ℝ) ^ Cpar := Real.rpow_pos_of_pos (by norm_num) _
  have hDpos : 0 < (20 : ℝ) ^ Cpar * moment tpar targetsT := mul_pos hRpos hTpos
  have hPTv : (moment tpar blocksP / moment tpar targetsT) ^ v ≤ (1 - eps) ^ v :=
    pow_le_pow_left₀ (div_nonneg hA0 hTpos.le) hPT _
  have hPonev : (moment 1 blocksP /
      ((20 : ℝ) ^ Cpar * moment tpar targetsT)) ^ v ≤ gam ^ v :=
    pow_le_pow_left₀ (div_nonneg hZ0 hDpos.le) hPone _
  have hCardnonneg : 0 ≤ 21 * (Multiset.card targetsT : ℝ) /
      ((20 : ℝ) ^ Cpar * moment tpar targetsT) :=
    div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hDpos.le
  have hCardv : (21 * (Multiset.card targetsT : ℝ) /
      ((20 : ℝ) ^ Cpar * moment tpar targetsT)) ^ v ≤ eta ^ v :=
    pow_le_pow_left₀ hCardnonneg hCard _
  have hSlt : (moment tpar blocksP / moment tpar targetsT) ^ v +
      2 * (moment 1 blocksP / ((20 : ℝ) ^ Cpar * moment tpar targetsT)) ^ v +
      2 * (21 * (Multiset.card targetsT : ℝ) /
        ((20 : ℝ) ^ Cpar * moment tpar targetsT)) ^ v < 1 := by
    linarith
  have hcast20 : (((20 ^ v : ℕ) : ℝ)) = (20 : ℝ) ^ v := by norm_num
  have hpow20 : ((20 ^ v : ℕ) : ℝ) ^ (tpar - 1) * ((20 : ℝ) ^ Cpar) ^ v = 1 := by
    calc
      ((20 ^ v : ℕ) : ℝ) ^ (tpar - 1) * ((20 : ℝ) ^ Cpar) ^ v =
          (20 : ℝ) ^ ((v : ℝ) * (tpar - 1)) * (20 : ℝ) ^ (Cpar * (v : ℝ)) := by
        congr 1
        · rw [hcast20, ← Real.rpow_natCast, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 20)]
        · rw [← Real.rpow_natCast, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 20)]
      _ = (20 : ℝ) ^ ((v : ℝ) * (tpar - 1) + Cpar * (v : ℝ)) := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 20)]
      _ = 1 := by
        have hz : (v : ℝ) * (tpar - 1) + Cpar * (v : ℝ) = 0 := by
          simp [tpar]
          ring
        rw [hz, Real.rpow_zero]
  have hQR : moment tpar targetsT ^ v /
      ((20 : ℝ) ^ Cpar * moment tpar targetsT) ^ v =
      ((20 ^ v : ℕ) : ℝ) ^ (tpar - 1) := by
    rw [mul_pow]
    apply (div_eq_iff (mul_ne_zero (pow_ne_zero _ hRpos.ne')
      (pow_ne_zero _ hTpos.ne'))).2
    calc
      moment tpar targetsT ^ v = 1 * moment tpar targetsT ^ v := by ring
      _ = (((20 ^ v : ℕ) : ℝ) ^ (tpar - 1) * ((20 : ℝ) ^ Cpar) ^ v) *
          moment tpar targetsT ^ v := by rw [hpow20]
      _ = ((20 ^ v : ℕ) : ℝ) ^ (tpar - 1) *
          (((20 : ℝ) ^ Cpar) ^ v * moment tpar targetsT ^ v) := by ring
  have hscaleZ : moment tpar targetsT ^ v *
      (moment 1 blocksP ^ v /
        ((20 : ℝ) ^ Cpar * moment tpar targetsT) ^ v) =
      moment 1 blocksP ^ v * ((20 ^ v : ℕ) : ℝ) ^ (tpar - 1) := by
    calc
      _ = moment 1 blocksP ^ v * (moment tpar targetsT ^ v /
        ((20 : ℝ) ^ Cpar * moment tpar targetsT) ^ v) := by ring
      _ = _ := by rw [hQR]
  have hscaleN : moment tpar targetsT ^ v *
      ((21 * (Multiset.card targetsT : ℝ)) ^ v /
        ((20 : ℝ) ^ Cpar * moment tpar targetsT) ^ v) =
      (21 * (Multiset.card targetsT : ℝ)) ^ v * ((20 ^ v : ℕ) : ℝ) ^ (tpar - 1) := by
    calc
      _ = (21 * (Multiset.card targetsT : ℝ)) ^ v * (moment tpar targetsT ^ v /
        ((20 : ℝ) ^ Cpar * moment tpar targetsT) ^ v) := by ring
      _ = _ := by rw [hQR]
  have hfactor : moment tpar blocksP ^ v +
      2 * ((20 ^ v : ℕ) : ℝ) ^ (tpar - 1) * moment 1 blocksP ^ v +
      2 * (Multiset.card targetsT : ℝ) ^ v * (21 ^ v : ℕ) *
        ((20 ^ v : ℕ) : ℝ) ^ (tpar - 1) =
      moment tpar targetsT ^ v *
        ((moment tpar blocksP / moment tpar targetsT) ^ v +
          2 * (moment 1 blocksP / ((20 : ℝ) ^ Cpar * moment tpar targetsT)) ^ v +
          2 * (21 * (Multiset.card targetsT : ℝ) /
            ((20 : ℝ) ^ Cpar * moment tpar targetsT)) ^ v) := by
    symm
    simp only [div_pow]
    calc
      moment tpar targetsT ^ v * (moment tpar blocksP ^ v /
          moment tpar targetsT ^ v +
          2 * (moment 1 blocksP ^ v /
            ((20 : ℝ) ^ Cpar * moment tpar targetsT) ^ v) +
          2 * ((21 * (Multiset.card targetsT : ℝ)) ^ v /
            ((20 : ℝ) ^ Cpar * moment tpar targetsT) ^ v)) =
          moment tpar targetsT ^ v * (moment tpar blocksP ^ v /
            moment tpar targetsT ^ v) +
          2 * (moment tpar targetsT ^ v * (moment 1 blocksP ^ v /
            ((20 : ℝ) ^ Cpar * moment tpar targetsT) ^ v)) +
          2 * (moment tpar targetsT ^ v *
            ((21 * (Multiset.card targetsT : ℝ)) ^ v /
              ((20 : ℝ) ^ Cpar * moment tpar targetsT) ^ v)) := by ring
      _ = _ := by
        rw [hscaleZ, hscaleN]
        have hQv : moment tpar targetsT ^ v ≠ 0 := pow_ne_zero _ hTpos.ne'
        rw [mul_pow]
        push_cast
        field_simp
  have hQvpos : 0 < moment tpar targetsT ^ v := pow_pos hTpos _
  have hright : moment tpar blocksP ^ v +
      2 * ((20 ^ v : ℕ) : ℝ) ^ (tpar - 1) * moment 1 blocksP ^ v +
      2 * (Multiset.card targetsT : ℝ) ^ v * (21 ^ v : ℕ) *
        ((20 ^ v : ℕ) : ℝ) ^ (tpar - 1) < moment tpar targetsT ^ v := by
    rw [hfactor]
    simpa using mul_lt_mul_of_pos_left hSlt hQvpos
  exact lt_of_lt_of_le (lt_of_le_of_lt hPupper hright) hTupper

end ExactDFTRefine.Main

open ExactDFTRefine.Main

theorem solution :
    moment tpar (Pprime blocksP targetsT 11640 (20 ^ 11640) (21 ^ 11640)) <
      moment tpar (Tprime targetsT 11640 (21 ^ 11640)) ∧
    ∀ p ∈ Pprime blocksP targetsT 11640 (20 ^ 11640) (21 ^ 11640),
      ∀ q ∈ Tprime targetsT 11640 (21 ^ 11640), p < q := by
  obtain ⟨hPupper, hTlower, hPT⟩ := proposition_3_2
  obtain ⟨-, -, hPone, hCard⟩ := eq_11
  obtain ⟨-, -, -, -, -, -, hsum_le, hsum_lt, -⟩ := eq_15
  have h145 : (0 : ℝ) < (145 : ℝ) ^ tpar := Real.rpow_pos_of_pos (by norm_num) _
  have hL : 0 < Lbound := by norm_num [Lbound]
  have hTpos : 0 < moment tpar targetsT := by
    have h := (le_div_iff₀ h145).mp hTlower
    exact lt_of_lt_of_le (mul_pos hL h145) h
  have hnum : (1 - eps) ^ 11640 + 2 * gam ^ 11640 + 2 * eta ^ 11640 < 1 :=
    lt_of_le_of_lt hsum_le hsum_lt
  constructor
  · exact moment_comparison_aux 11640 (by norm_num) hTpos hPT hPone hCard hnum
  · apply rank_separation_aux 11640 (by positivity)
    exact Nat.pow_lt_pow_left (by norm_num) (by norm_num)
