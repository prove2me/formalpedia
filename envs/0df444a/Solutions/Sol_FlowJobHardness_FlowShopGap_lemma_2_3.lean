-- Prove2me | solution 1 for FlowJobHardness.FlowShopGap.lemma_2_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T22:24:23.945971+00:00
-- url     : https://prove2.me/submissions/e63169c4-ef0b-4125-8f30-2361304c3e51

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobHardness_FlowShopGap_Construction
import Definitions.Def_FlowJobHardness_FlowShopGap_GoodOps

open JobShopLTAS.Core
open FlowJobHardness.FlowShopGap

namespace Lemma23Proof

private lemma isLongOp_iff_isLongPair {r d : ℕ} (hr : 1 ≤ r) (q i : Fin (size r d)) :
    IsLongOp r d ⟨q, i⟩ ↔ IsLongPair r d q.val i.val := by
  unfold IsLongOp Instance.proc inst procTime
  dsimp
  split_ifs with h
  · refine ⟨fun _ => h, fun _ => ?_⟩
    have hr_pos : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
    exact pow_pos hr_pos _
  · exact ⟨fun h0 => (lt_irrefl (0 : ℝ) h0).elim, fun h' => (h h').elim⟩

private lemma schedule_step_aux {r d : ℕ} {s : (inst r d).Op → ℝ}
    (hs : (inst r d).IsFeasibleSchedule Finset.univ s)
    (q : Fin (size r d)) (m : ℕ) :
    ∀ (i i' : Fin (size r d)), i.val + 1 + m = i'.val →
      s ⟨q, i⟩ + (inst r d).proc ⟨q, i⟩ ≤ s ⟨q, i'⟩ := by
  induction m with
  | zero =>
    intro i i' h
    rw [Nat.add_zero] at h
    exact hs.precedence q (Finset.mem_univ q) i i' h
  | succ m ih =>
    intro i i' h
    let mid : Fin (size r d) := ⟨i.val + 1 + m, by have := i'.isLt; omega⟩
    have h1 : s ⟨q, i⟩ + (inst r d).proc ⟨q, i⟩ ≤ s ⟨q, mid⟩ := ih i mid rfl
    have h2 : s ⟨q, mid⟩ + (inst r d).p q mid ≤ s ⟨q, i'⟩ :=
      hs.precedence q (Finset.mem_univ q) mid i' h
    have h3 : 0 ≤ (inst r d).p q mid := (inst r d).p_nonneg q mid
    linarith

private lemma schedule_lt_le {r d : ℕ} {s : (inst r d).Op → ℝ}
    (hs : (inst r d).IsFeasibleSchedule Finset.univ s)
    (q : Fin (size r d)) (i i' : Fin (size r d)) (h : i < i') :
    s ⟨q, i⟩ + (inst r d).proc ⟨q, i⟩ ≤ s ⟨q, i'⟩ := by
  change i.val < i'.val at h
  exact schedule_step_aux hs q (i'.val - (i.val + 1)) i i' (by omega)

end Lemma23Proof

open Lemma23Proof in
theorem solution (r d : ℕ) (hr : 3 ≤ r) (s : (inst r d).Op → ℝ)
    (hs : (inst r d).IsFeasibleSchedule Finset.univ s)
    (g : ℕ) (hg1 : 1 ≤ g) (_hg2 : g ≤ r ^ (2 * d))
    (k ℓ : ℕ) (hk : 1 ≤ k) (hkℓ : k < ℓ) (hℓ : ℓ ≤ d) :
    ∀ I ∈ T r d s g k, ∀ J ∈ T r d s g ℓ, Disjoint I J := by
  classical
  rintro I ⟨⟨qk, pk⟩, hok_mem, rfl⟩ J ⟨⟨ql, pl⟩, hol_mem, rfl⟩
  simp only [goodOpsOn, Finset.mem_filter, Finset.mem_univ, true_and] at hok_mem hol_mem
  rcases hok_mem with ⟨hok_good, hpk_grp, hpk_freq⟩
  rcases hol_mem with ⟨hol_good, hpl_grp, hpl_freq⟩
  change machGroup d pk.val = g at hpk_grp
  change machFreq d pk.val = k at hpk_freq
  change machGroup d pl.val = g at hpl_grp
  change machFreq d pl.val = ℓ at hpl_freq
  have hd_pos : 0 < d := by omega
  have hr1 : 1 ≤ r := by omega
  have hpk_val : pk.val = (g - 1) * d + (d - k) := by
    have hmod_lt : pk.val % d < d := Nat.mod_lt pk.val hd_pos
    unfold machGroup at hpk_grp
    unfold machFreq at hpk_freq
    have hdiv : pk.val / d = g - 1 := by omega
    have hmod : pk.val % d = d - k := by omega
    rw [← hdiv, ← hmod, Nat.mul_comm (pk.val / d) d, Nat.div_add_mod]
  have hpl_val : pl.val = (g - 1) * d + (d - ℓ) := by
    have hmod_lt : pl.val % d < d := Nat.mod_lt pl.val hd_pos
    unfold machGroup at hpl_grp
    unfold machFreq at hpl_freq
    have hdiv : pl.val / d = g - 1 := by omega
    have hmod : pl.val % d = d - ℓ := by omega
    rw [← hdiv, ← hmod, Nat.mul_comm (pl.val / d) d, Nat.div_add_mod]
  have hpl_lt_pk : pl < pk := by
    change pl.val < pk.val
    omega
  have hok_pair : IsLongPair r d qk.val pk.val :=
    (isLongOp_iff_isLongPair hr1 qk pk).mp hok_good.1
  have hol_pair : IsLongPair r d ql.val pl.val :=
    (isLongOp_iff_isLongPair hr1 ql pl).mp hol_good.1
  have hqk_freq : jobFreq r d qk.val = k := hok_pair.1.symm.trans hpk_freq
  have hql_freq : jobFreq r d ql.val = ℓ := hol_pair.1.symm.trans hpl_freq
  have hproc_ok : (inst r d).proc ⟨qk, pk⟩ = (r : ℝ) ^ (2 * (d - k)) := by
    change procTime r d qk.val pk.val = _
    unfold procTime
    rw [if_pos hok_pair, hqk_freq]
  have hproc_ol : (inst r d).proc ⟨ql, pl⟩ = (r : ℝ) ^ (2 * (d - ℓ)) := by
    change procTime r d ql.val pl.val = _
    unfold procTime
    rw [if_pos hol_pair, hql_freq]
  have hq_ne : qk ≠ ql := by
    intro h
    have hfreq_eq : jobFreq r d qk.val = jobFreq r d ql.val := by rw [h]
    omega
  obtain ⟨il', hpl_lt_il', hil'_long, _, hil'_delay⟩ := hol_good.2
  have hil'_pair : IsLongPair r d ql.val il'.val :=
    (isLongOp_iff_isLongPair hr1 ql il').mp hil'_long
  have hil'_freq : machFreq d il'.val = ℓ := hil'_pair.1.trans hql_freq
  have hil'_mod : il'.val % d = d - ℓ := by
    have hmod_lt : il'.val % d < d := Nat.mod_lt il'.val hd_pos
    unfold machFreq at hil'_freq
    omega
  have hil'_div_ge : g ≤ il'.val / d := by
    by_contra hlt
    have hle : il'.val / d ≤ g - 1 := by omega
    have h1 : (il'.val / d) * d ≤ (g - 1) * d := Nat.mul_le_mul_right d hle
    have h2 : (il'.val / d) * d + (d - ℓ) = il'.val := by
      rw [← hil'_mod, Nat.mul_comm (il'.val / d) d, Nat.div_add_mod]
    change pl.val < il'.val at hpl_lt_il'
    omega
  have hpk_lt_il' : pk < il' := by
    change pk.val < il'.val
    have h1 : g * d ≤ (il'.val / d) * d := Nat.mul_le_mul_right d hil'_div_ge
    have h2 : (il'.val / d) * d + (d - ℓ) = il'.val := by
      rw [← hil'_mod, Nat.mul_comm (il'.val / d) d, Nat.div_add_mod]
    have h3 : (g - 1) * d + d = g * d := by
      calc (g - 1) * d + d = (g - 1 + 1) * d := by rw [Nat.add_mul, Nat.one_mul]
        _ = g * d := by congr 1; omega
    omega
  have hop_ne : (⟨qk, pk⟩ : (inst r d).Op) ≠ ⟨ql, pk⟩ :=
    fun h => hq_ne (congrArg Sigma.fst h)
  have hdisj := hs.machine_disjoint ⟨qk, pk⟩ ⟨ql, pk⟩
    (Finset.mem_univ qk) (Finset.mem_univ ql) hop_ne rfl
  rcases hdisj with h_ok_before | h_ol_before
  · have h1 : s ⟨ql, pk⟩ + (inst r d).proc ⟨ql, pk⟩ ≤ s ⟨ql, il'⟩ :=
      schedule_lt_le hs ql pk il' hpk_lt_il'
    have h2 : 0 ≤ (inst r d).proc ⟨ql, pk⟩ := (inst r d).p_nonneg ql pk
    have h3 : s ⟨qk, pk⟩ + (inst r d).proc ⟨qk, pk⟩ ≤
        s ⟨ql, pl⟩ + (inst r d).proc ⟨ql, pl⟩ +
          (r : ℝ) ^ 2 / 4 * (r : ℝ) ^ (2 * (d - ℓ)) := by
      change s ⟨ql, il'⟩ - (s ⟨ql, pl⟩ + (inst r d).proc ⟨ql, pl⟩) ≤
        (r : ℝ) ^ 2 / 4 * (r : ℝ) ^ (2 * (d - jobFreq r d ql.val)) at hil'_delay
      rw [hql_freq] at hil'_delay
      linarith
    have hr_real : (3 : ℝ) ≤ r := by exact_mod_cast hr
    have hr_ge1 : (1 : ℝ) ≤ r := by linarith
    have hr2_ge4 : (4 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith
    have hpow_nonneg : 0 ≤ (r : ℝ) ^ (2 * (d - ℓ)) := by positivity
    have hpow_step : (r : ℝ) ^ 2 * (r : ℝ) ^ (2 * (d - ℓ)) ≤ (r : ℝ) ^ (2 * (d - k)) := by
      let m := 2 * (d - k) - (2 + 2 * (d - ℓ))
      have hm_eq : m + (2 + 2 * (d - ℓ)) = 2 * (d - k) := by omega
      have hpow_m : 1 ≤ (r : ℝ) ^ m := one_le_pow₀ hr_ge1
      calc (r : ℝ) ^ 2 * (r : ℝ) ^ (2 * (d - ℓ))
          = 1 * (r : ℝ) ^ (2 + 2 * (d - ℓ)) := by rw [one_mul, pow_add]
        _ ≤ (r : ℝ) ^ m * (r : ℝ) ^ (2 + 2 * (d - ℓ)) := by
            refine mul_le_mul_of_nonneg_right hpow_m ?_
            positivity
        _ = (r : ℝ) ^ (2 * (d - k)) := by rw [← pow_add, hm_eq]
    have hpow_le_quarter :
        (r : ℝ) ^ (2 * (d - ℓ)) ≤ (r : ℝ) ^ 2 / 4 * (r : ℝ) ^ (2 * (d - ℓ)) := by
      have hdiv : (1 : ℝ) ≤ (r : ℝ) ^ 2 / 4 := by linarith
      calc (r : ℝ) ^ (2 * (d - ℓ)) = 1 * (r : ℝ) ^ (2 * (d - ℓ)) := (one_mul _).symm
        _ ≤ ((r : ℝ) ^ 2 / 4) * (r : ℝ) ^ (2 * (d - ℓ)) :=
            mul_le_mul_of_nonneg_right hdiv hpow_nonneg
    have hsum_le_half :
        (inst r d).proc ⟨ql, pl⟩ + (r : ℝ) ^ 2 / 4 * (r : ℝ) ^ (2 * (d - ℓ)) ≤
          (inst r d).proc ⟨qk, pk⟩ / 2 := by
      rw [hproc_ok, hproc_ol]
      linarith
    have hend_le : s ⟨qk, pk⟩ + (inst r d).proc ⟨qk, pk⟩ / 2 ≤ s ⟨ql, pl⟩ := by linarith
    rw [Set.disjoint_iff]
    rintro x ⟨hxI, hxJ⟩
    unfold firstHalf at hxI hxJ
    simp only [Set.mem_Ico] at hxI hxJ
    linarith
  · have h1 : s ⟨ql, pl⟩ + (inst r d).proc ⟨ql, pl⟩ ≤ s ⟨ql, pk⟩ :=
      schedule_lt_le hs ql pl pk hpl_lt_pk
    have h2 : 0 ≤ (inst r d).proc ⟨ql, pk⟩ := (inst r d).p_nonneg ql pk
    have h3 : 0 ≤ (inst r d).proc ⟨ql, pl⟩ := (inst r d).p_nonneg ql pl
    have hend_le : s ⟨ql, pl⟩ + (inst r d).proc ⟨ql, pl⟩ / 2 ≤ s ⟨qk, pk⟩ := by linarith
    rw [Set.disjoint_iff]
    rintro x ⟨hxI, hxJ⟩
    unfold firstHalf at hxI hxJ
    simp only [Set.mem_Ico] at hxI hxJ
    linarith
