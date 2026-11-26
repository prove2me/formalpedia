-- Prove2me | solution 1 for BellWilliams2001.ThresholdPolicy.renewal_increments_from_epoch_blocks
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T06:08:58.735215+00:00
-- url     : https://prove2.me/submissions/03cf62ee-4835-4b02-a75b-b79652fe9b66

import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths

open BellWilliams2001.ThresholdPolicy
open Filter Set

private theorem bracket {e : ℕ → ℝ} (he : StrictMono e) (h0 : e 0 = 0)
    {N : ℕ} {s : ℝ} (hs : 0 ≤ s) (hN : s < e N) :
    ∃ j < N, e j ≤ s ∧ s < e (j+1) ∧ renewalCount e s = j := by
  let hEx : ∃ i, s < e i := ⟨N,hN⟩
  let k := Nat.find hEx
  have hk : s < e k := Nat.find_spec hEx
  have hk0 : k ≠ 0 := by
    intro hz
    rw [hz,h0] at hk
    exact hk.not_ge hs
  let j := k - 1
  have hjs : j+1=k := by dsimp [j]; omega
  have hjk : j < k := by omega
  have hj : e j ≤ s := le_of_not_gt (Nat.find_min hEx hjk)
  have hj' : s < e (j+1) := by rwa [hjs]
  refine ⟨j,hjk.trans_le (Nat.find_min' hEx hN),hj,hj',le_antisymm ?_ ?_⟩
  · refine iSup_le fun i => iSup_le fun hi => ?_
    have hh : i ≤ j := le_of_not_gt (fun h => (hj'.trans_le (he.monotone h)).not_ge hi)
    exact_mod_cast hh
  · exact le_iSup_of_le j (le_iSup_of_le hj le_rfl)

set_option maxHeartbeats 1100000 in
theorem solution (e : ℕ → ℝ) (he : StrictMono e) (he0 : e 0 = 0)
    (m : ℕ) (hm : 0 < m) (N : ℕ) (hmN : m ∣ N)
    (H : ℝ) (hH : 0 ≤ H) (hN : 2*H < (N:ℝ))
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/2)
    (hBlock : ∀ j ≤ N, |e (j+m) - e j - (m:ℝ)| ≤ δ*m) :
    ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ H →
      |((renewalCount e t).toNat:ℝ) - ((renewalCount e s).toNat:ℝ) - (t-s)| ≤
        2*δ*(t-s)+2*m := by
  have hlow (i q : ℕ) (hi : i + q*m ≤ N+m) :
      (1-δ)*(q:ℝ)*m ≤ e (i+q*m) - e i := by
    induction q with
    | zero => simp
    | succ q ih =>
      have hIdx : i + q*m ≤ N := by rw [Nat.succ_mul] at hi; omega
      have h := (abs_le.1 (hBlock _ hIdx)).1
      have hh := ih (by omega)
      rw [Nat.succ_mul, ← Nat.add_assoc]
      push_cast
      linarith
  have hupp (i q : ℕ) (hi : i + q*m ≤ N+m) :
      e (i+q*m) - e i ≤ (1+δ)*(q:ℝ)*m := by
    induction q with
    | zero => simp
    | succ q ih =>
      have hIdx : i + q*m ≤ N := by rw [Nat.succ_mul] at hi; omega
      have h := (abs_le.1 (hBlock _ hIdx)).2
      have hh := ih (by omega)
      rw [Nat.succ_mul, ← Nat.add_assoc]
      push_cast
      linarith
  obtain ⟨p,hp⟩ := hmN
  have hp' : N = p*m := hp.trans (Nat.mul_comm _ _)
  have hE : H < e N := by
    have h := hlow 0 p (by simp [← hp'])
    rw [zero_add, ← hp',he0,sub_zero] at h
    have hh : (N:ℝ) ≤ 2*((1-δ)*(p:ℝ)*m) := by
      have h' := mul_le_mul_of_nonneg_right (show (1/2:ℝ) ≤ 1-δ by linarith)
        (mul_nonneg (Nat.cast_nonneg (α := ℝ) p) (Nat.cast_nonneg (α := ℝ) m))
      rw [hp']; push_cast; linarith
    linarith
  intro s t hs hst ht
  have ht0 := hs.trans hst
  obtain ⟨j,hjN,hjs,hjs',hj⟩ := bracket he he0 hs (hst.trans_lt (ht.trans_lt hE))
  obtain ⟨k,hkN,hkt,hkt',hk⟩ := bracket he he0 ht0 (ht.trans_lt hE)
  have hjk : j ≤ k := le_of_not_gt (fun h => (hkt'.trans_le (he.monotone h)).not_ge (hjs.trans hst))
  rw [hj,hk,ENat.toNat_natCast,ENat.toNat_natCast]
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hd0 : 0 ≤ t-s := sub_nonneg.mpr hst
  have hUpper : ((k:ℝ)-(j:ℝ))-(t-s) ≤ 2*δ*(t-s)+2*(m:ℝ) := by
    by_cases hjk' : j < k
    · let q := (k-(j+1))/m
      have hq : j+1+q*m ≤ k := by
        have h := Nat.div_mul_le_self (k-(j+1)) m
        dsimp only [q]
        omega
      have hq' : k-(j+1) < (q+1)*m := by
        have h := Nat.mod_lt (k-(j+1)) hm
        have heq := Nat.mod_add_div (k-(j+1)) m
        rw [Nat.mul_comm m] at heq
        rw [Nat.succ_mul]
        dsimp [q]
        omega
      have hb := hlow (j+1) q (hq.trans (hkN.le.trans (Nat.le_add_right _ _)))
      have heng : (1-δ)*(q:ℝ)*m ≤ t-s := by
        have heq := (he.monotone hq).trans hkt
        linarith
      have hqB : (q:ℝ)*m ≤ (1+2*δ)*(t-s) := by
        have hfac : 1 ≤ (1+2*δ)*(1-δ) := by nlinarith [mul_nonneg hδ (show 0 ≤ 1-2*δ by linarith)]
        have hQ : (0:ℝ) ≤ (q:ℝ)*m := by positivity
        have h₁ := mul_le_mul_of_nonneg_right hfac hQ
        have h₂ := mul_le_mul_of_nonneg_left heng (show 0 ≤ 1+2*δ by positivity)
        linarith only [h₁,h₂]
      have hreal : (k:ℝ) - (j:ℝ) < ((q:ℝ)+1)*m+1 := by
        have hNat : k < j+1+(q+1)*m := by omega
        have hh : (k:ℝ) < ((j+1+(q+1)*m:ℕ):ℝ) := by exact_mod_cast hNat
        push_cast at hh
        linarith
      linarith
    · have heq : j=k := by omega
      rw [heq,sub_self]
      nlinarith [mul_nonneg hδ hd0]
  have hLower : (t-s)-((k:ℝ)-(j:ℝ)) ≤ 2*δ*(t-s)+2*(m:ℝ) := by
    let q := (k-j)/m
    have hq : j+q*m ≤ k := by
      have h := Nat.div_mul_le_self (k-j) m
      dsimp only [q]
      omega
    have hq' : k+1 ≤ j+(q+1)*m := by
      have h := Nat.mod_lt (k-j) hm
      have heq := Nat.mod_add_div (k-j) m
      rw [Nat.mul_comm m] at heq
      rw [Nat.succ_mul]
      dsimp [q]
      omega
    have hb := hupp j (q+1) (by rw [Nat.succ_mul,← Nat.add_assoc]; omega)
    have hd : t-s ≤ (1+δ)*((k:ℝ)-(j:ℝ)+(m:ℝ)) := by
      have heq : t < e (j+(q+1)*m) := hkt'.trans_le (he.monotone hq')
      have hqR : ((q:ℝ)+1)*m ≤ (k:ℝ)-(j:ℝ)+m := by
        have hh : ((j+q*m:ℕ):ℝ) ≤ k := by exact_mod_cast hq
        push_cast at hh
        linarith
      have hbb := mul_le_mul_of_nonneg_left hqR (show 0 ≤ 1+δ by positivity)
      push_cast at hb
      nlinarith
    by_cases h : (k:ℝ)-(j:ℝ) ≤ t-s
    · have hmul := mul_le_mul_of_nonneg_left h hδ
      have hmδ := mul_le_mul_of_nonneg_right hδ' (Nat.cast_nonneg (α := ℝ) m)
      nlinarith [mul_nonneg hδ hd0]
    · nlinarith [mul_nonneg hδ hd0]
  exact abs_le.2 ⟨by linarith,by linarith⟩
