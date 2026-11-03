-- Prove2me | solution 1 for FlowJobHardness.FlowShopGap.lb_display
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T22:24:13.732529+00:00
-- url     : https://prove2.me/submissions/01b7ea9b-adef-4b15-9175-d9383b98400a

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobHardness_FlowShopGap_Construction

open JobShopLTAS.Core
open FlowJobHardness.FlowShopGap

namespace LbDisplayProof

private lemma mul_add_inj {d a b r1 r2 : ℕ} (hr1 : r1 < d) (hr2 : r2 < d)
    (h : a * d + r1 = b * d + r2) : a = b ∧ r1 = r2 := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · have h1 : (a + 1) * d ≤ b * d := Nat.mul_le_mul_right d hab
    rw [Nat.add_mul, Nat.one_mul] at h1
    omega
  · exact ⟨rfl, by omega⟩
  · have h1 : (b + 1) * d ≤ a * d := Nat.mul_le_mul_right d hba
    rw [Nat.add_mul, Nat.one_mul] at h1
    omega

private lemma div_mod_of_eq_mul_add {d p m rem : ℕ} (hrem : rem < d) (hp : p = m * d + rem) :
    p / d = m ∧ p % d = rem := by
  have hd_pos : 0 < d := by omega
  have h1 : (p / d) * d + p % d = m * d + rem := by
    rw [Nat.mul_comm (p / d) d, Nat.div_add_mod, hp]
  exact mul_add_inj (Nat.mod_lt p hd_pos) hrem h1

private lemma div_lt_of_lt_mul_right {p M d : ℕ} (hp : p < M * d) : p / d < M := by
  rcases Nat.eq_zero_or_pos d with rfl | hd_pos
  · simp at hp
  · by_contra hge
    have hle : M ≤ p / d := le_of_not_gt hge
    have h1 : M * d ≤ (p / d) * d := Nat.mul_le_mul_right d hle
    have h2 : (p / d) * d + p % d = p := by rw [Nat.mul_comm, Nat.div_add_mod]
    omega

private lemma div_eq_iff_le_and_lt {x g₀ M : ℕ} (hM : 0 < M) :
    (g₀ * M ≤ x ∧ x < (g₀ + 1) * M) ↔ x / M = g₀ := by
  have hx : (x / M) * M + x % M = x := by rw [Nat.mul_comm, Nat.div_add_mod]
  have hmod : x % M < M := Nat.mod_lt x hM
  constructor
  · rintro ⟨hle, hlt⟩
    rcases lt_trichotomy (x / M) g₀ with h1 | h1 | h1
    · have h2 : (x / M + 1) * M ≤ g₀ * M := Nat.mul_le_mul_right M h1
      rw [Nat.add_mul, Nat.one_mul] at h2
      omega
    · exact h1
    · have h2 : (g₀ + 1) * M ≤ (x / M) * M := Nat.mul_le_mul_right M h1
      omega
  · rintro rfl
    rw [Nat.add_mul, Nat.one_mul]
    omega

private lemma pos_of_fin_size {r d : ℕ} (x : Fin (size r d)) :
    0 < d ∧ 0 < r ^ (2 * d) ∧ 0 < r := by
  have h_size : 0 < size r d := by have := x.isLt; omega
  have hd_pos : 0 < d := by
    unfold size at h_size
    exact Nat.pos_of_mul_pos_left h_size
  have hR_pos : 0 < r ^ (2 * d) := by
    unfold size at h_size
    exact Nat.pos_of_mul_pos_right h_size
  have hr_pos : 0 < r := by
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · have h2d : 2 * d ≠ 0 := by omega
      rw [zero_pow h2d] at hR_pos
      omega
    · exact hr
  exact ⟨hd_pos, hR_pos, hr_pos⟩

private lemma jobFreq_bounds {r d : ℕ} (q : Fin (size r d)) :
    1 ≤ jobFreq r d q.val ∧ jobFreq r d q.val ≤ d := by
  have hq : q.val < d * r ^ (2 * d) := by
    rw [Nat.mul_comm]
    exact q.isLt
  have hdiv : q.val / r ^ (2 * d) < d := div_lt_of_lt_mul_right hq
  unfold jobFreq
  exact ⟨Nat.le_add_left 1 _, hdiv⟩

private lemma machFreq_bounds {r d : ℕ} (t : Fin (size r d)) :
    1 ≤ machFreq d t.val ∧ machFreq d t.val ≤ d := by
  obtain ⟨hd_pos, _, _⟩ := pos_of_fin_size t
  have hmod : t.val % d < d := Nat.mod_lt t.val hd_pos
  unfold machFreq
  omega

private lemma card_longMach_of_job (r d : ℕ) (q : Fin (size r d)) :
    (Finset.univ.filter (fun i : Fin (size r d) => IsLongPair r d q.val i.val)).card =
      r ^ (2 * jobFreq r d q.val) := by
  classical
  obtain ⟨hd_pos, hR_pos, hr_pos⟩ := pos_of_fin_size q
  obtain ⟨hf1, hf2⟩ := jobFreq_bounds q
  let f := jobFreq r d q.val
  have hR_split : r ^ (2 * d) = r ^ (2 * (d - f)) * r ^ (2 * f) := by
    rw [← pow_add]
    congr 1
    omega
  have hrf_pos : 0 < r ^ (2 * f) := pow_pos hr_pos _
  have hg_lt : jobGroup r d q.val - 1 < r ^ (2 * (d - f)) := by
    have hmod : q.val % r ^ (2 * d) < r ^ (2 * (d - f)) * r ^ (2 * f) := by
      rw [← hR_split]
      exact Nat.mod_lt q.val hR_pos
    have hdiv := div_lt_of_lt_mul_right hmod
    unfold jobGroup
    dsimp [f] at hdiv ⊢
    omega
  let c := (jobGroup r d q.val - 1) * r ^ (2 * f)
  have hc_le : c + r ^ (2 * f) ≤ r ^ (2 * d) := by
    have h1 : (jobGroup r d q.val - 1 + 1) * r ^ (2 * f) ≤ r ^ (2 * (d - f)) * r ^ (2 * f) :=
      Nat.mul_le_mul_right _ hg_lt
    rw [Nat.add_mul, Nat.one_mul, ← hR_split] at h1
    exact h1
  let φ : Fin (r ^ (2 * f)) → Fin (size r d) := fun k =>
    ⟨(c + k.val) * d + (d - f), by
      have hk_lt : c + k.val < r ^ (2 * d) := lt_of_lt_of_le (Nat.add_lt_add_left k.isLt c) hc_le
      have h1 : (c + k.val + 1) * d ≤ r ^ (2 * d) * d := Nat.mul_le_mul_right d hk_lt
      rw [Nat.add_mul, Nat.one_mul] at h1
      unfold size
      omega⟩
  have hφ_div_mod : ∀ k : Fin (r ^ (2 * f)),
      (φ k).val / d = c + k.val ∧ (φ k).val % d = d - f := by
    intro k
    exact div_mod_of_eq_mul_add (by omega) rfl
  have hφ_inj : Function.Injective φ := by
    intro k1 k2 h
    have h1 := (hφ_div_mod k1).1
    have h2 := (hφ_div_mod k2).1
    rw [h] at h1
    ext
    omega
  have hfilter_eq :
      Finset.univ.filter (fun i : Fin (size r d) => IsLongPair r d q.val i.val) =
        Finset.univ.image φ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨hfreq, hgrp1, hgrp2⟩
      unfold machFreq at hfreq
      unfold machGroup at hgrp1 hgrp2
      have himod : i.val % d < d := Nat.mod_lt i.val hd_pos
      have himod_eq : i.val % d = d - f := by dsimp [f]; omega
      have hidiv_ge : c ≤ i.val / d := by dsimp [c, f]; omega
      have hidiv_lt : i.val / d - c < r ^ (2 * f) := by dsimp [c, f]; omega
      refine ⟨⟨i.val / d - c, hidiv_lt⟩, ?_⟩
      ext
      dsimp [φ]
      have h_add : c + (i.val / d - c) = i.val / d := by omega
      rw [h_add, ← himod_eq, Nat.mul_comm (i.val / d) d, Nat.div_add_mod]
    · rintro ⟨k, rfl⟩
      obtain ⟨hdiv, hmod⟩ := hφ_div_mod k
      have hk_lt := k.isLt
      refine ⟨?_, ?_, ?_⟩
      · unfold machFreq
        rw [hmod]
        dsimp [f]
        omega
      · unfold machGroup
        rw [hdiv]
        dsimp [c, f]
        omega
      · unfold machGroup
        rw [hdiv]
        dsimp [c, f] at hk_lt ⊢
        omega
  rw [hfilter_eq, Finset.card_image_of_injective _ hφ_inj, Finset.card_univ, Fintype.card_fin]

private lemma card_longJob_of_mach (r d : ℕ) (t : Fin (size r d)) :
    (Finset.univ.filter (fun q : Fin (size r d) => IsLongPair r d q.val t.val)).card =
      r ^ (2 * machFreq d t.val) := by
  classical
  obtain ⟨hd_pos, hR_pos, hr_pos⟩ := pos_of_fin_size t
  obtain ⟨hf1, hf2⟩ := machFreq_bounds t
  let f := machFreq d t.val
  let R := r ^ (2 * d)
  have hR_split : R = r ^ (2 * (d - f)) * r ^ (2 * f) := by
    dsimp [R]
    rw [← pow_add]
    congr 1
    omega
  have hrf_pos : 0 < r ^ (2 * f) := pow_pos hr_pos _
  have ht_div_lt : t.val / d < R := div_lt_of_lt_mul_right t.isLt
  let g₀ := (t.val / d) / r ^ (2 * f)
  have hg₀_lt : g₀ < r ^ (2 * (d - f)) := by
    apply div_lt_of_lt_mul_right
    rw [← hR_split]
    exact ht_div_lt
  have hg₀_le : (g₀ + 1) * r ^ (2 * f) ≤ R := by
    rw [hR_split]
    exact Nat.mul_le_mul_right _ hg₀_lt
  let ψ : Fin (r ^ (2 * f)) → Fin (size r d) := fun a =>
    ⟨(f - 1) * R + (g₀ * r ^ (2 * f) + a.val), by
      have ha_rem : g₀ * r ^ (2 * f) + a.val < R := by
        have h1 : g₀ * r ^ (2 * f) + a.val < (g₀ + 1) * r ^ (2 * f) := by
          rw [Nat.add_mul, Nat.one_mul]
          omega
        exact lt_of_lt_of_le h1 hg₀_le
      have hf_lt : f - 1 < d := by omega
      have h2 : (f - 1) * R + R ≤ R * d := by
        calc (f - 1) * R + R = (f - 1 + 1) * R := by rw [Nat.add_mul, Nat.one_mul]
          _ ≤ d * R := Nat.mul_le_mul_right R hf_lt
          _ = R * d := Nat.mul_comm d R
      change (f - 1) * R + (g₀ * r ^ (2 * f) + a.val) < R * d
      exact lt_of_lt_of_le (Nat.add_lt_add_left ha_rem _) h2⟩
  have hψ_div_mod : ∀ a : Fin (r ^ (2 * f)),
      (ψ a).val / R = f - 1 ∧
      ((ψ a).val % R) / r ^ (2 * f) = g₀ ∧
      ((ψ a).val % R) % r ^ (2 * f) = a.val := by
    intro a
    have ha_rem : g₀ * r ^ (2 * f) + a.val < R := by
      have h1 : g₀ * r ^ (2 * f) + a.val < (g₀ + 1) * r ^ (2 * f) := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      exact lt_of_lt_of_le h1 hg₀_le
    obtain ⟨hq_div, hq_mod⟩ := div_mod_of_eq_mul_add ha_rem (rfl : (ψ a).val = _)
    obtain ⟨hrem_div, hrem_mod⟩ := div_mod_of_eq_mul_add a.isLt hq_mod
    exact ⟨hq_div, hrem_div, hrem_mod⟩
  have hψ_inj : Function.Injective ψ := by
    intro a1 a2 h
    have h1 := (hψ_div_mod a1).2.2
    have h2 := (hψ_div_mod a2).2.2
    rw [h] at h1
    ext
    exact h1.symm.trans h2
  have hfilter_eq :
      Finset.univ.filter (fun q : Fin (size r d) => IsLongPair r d q.val t.val) =
        Finset.univ.image ψ := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨hfreq, hgrp1, hgrp2⟩
      have hqf : jobFreq r d q.val = f := hfreq.symm
      have hq_div : q.val / R = f - 1 := by
        unfold jobFreq at hqf
        dsimp [R]
        omega
      have hgrp_bounds :
          (jobGroup r d q.val - 1) * r ^ (2 * f) ≤ t.val / d ∧
            t.val / d < (jobGroup r d q.val - 1 + 1) * r ^ (2 * f) := by
        unfold machGroup at hgrp1 hgrp2
        rw [hqf] at hgrp1 hgrp2
        rw [Nat.add_mul, Nat.one_mul]
        omega
      have hgrp_eq : (q.val % R) / r ^ (2 * f) = g₀ := by
        have h1 := (div_eq_iff_le_and_lt hrf_pos).mp hgrp_bounds
        unfold jobGroup at h1
        rw [hqf] at h1
        dsimp [R, g₀] at h1 ⊢
        omega
      let a_val := (q.val % R) % r ^ (2 * f)
      refine ⟨⟨a_val, Nat.mod_lt _ hrf_pos⟩, ?_⟩
      ext
      dsimp [ψ, a_val]
      have h_inner : g₀ * r ^ (2 * f) + (q.val % R) % r ^ (2 * f) = q.val % R := by
        rw [← hgrp_eq, Nat.mul_comm ((q.val % R) / r ^ (2 * f)), Nat.div_add_mod]
      rw [h_inner, ← hq_div, Nat.mul_comm (q.val / R) R, Nat.div_add_mod]
    · rintro ⟨a, rfl⟩
      obtain ⟨hq_div, hrem_div, _⟩ := hψ_div_mod a
      have hqf : jobFreq r d (ψ a).val = f := by
        unfold jobFreq
        change (ψ a).val / R + 1 = f
        rw [hq_div]
        omega
      have hqg : jobGroup r d (ψ a).val - 1 = g₀ := by
        unfold jobGroup
        rw [hqf]
        exact hrem_div
      have hbounds : g₀ * r ^ (2 * f) ≤ t.val / d ∧ t.val / d < (g₀ + 1) * r ^ (2 * f) :=
        (div_eq_iff_le_and_lt hrf_pos).mpr rfl
      rw [Nat.add_mul, Nat.one_mul] at hbounds
      refine ⟨hqf.symm, ?_, ?_⟩
      · unfold machGroup
        rw [hqf, hqg]
        omega
      · unfold machGroup
        rw [hqf, hqg]
        omega
  rw [hfilter_eq, Finset.card_image_of_injective _ hψ_inj, Finset.card_univ, Fintype.card_fin]

end LbDisplayProof

open LbDisplayProof in
theorem solution (r d : ℕ) :
    (∀ q : Fin (size r d), (inst r d).jobLength q = (r : ℝ) ^ (2 * d)) ∧
      (∀ t : Fin (size r d), (inst r d).load t = (r : ℝ) ^ (2 * d)) := by
  classical
  constructor
  · intro q
    obtain ⟨_, hf2⟩ := jobFreq_bounds q
    unfold Instance.jobLength inst procTime
    dsimp
    rw [← Finset.sum_filter]
    rw [Finset.sum_const, card_longMach_of_job r d q, nsmul_eq_mul, Nat.cast_pow, ← pow_add]
    congr 1
    omega
  · intro t
    obtain ⟨_, hf2⟩ := machFreq_bounds t
    unfold Instance.load
    let ι : Fin (size r d) → (inst r d).Op := fun q => ⟨q, t⟩
    have hι_inj : Function.Injective ι := by
      intro q1 q2 h
      injection h
    have hfilter_op :
        Finset.univ.filter (fun o : (inst r d).Op => (inst r d).mach o = t) =
          Finset.univ.image ι := by
      ext o
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro ho
        refine ⟨o.1, ?_⟩
        rcases o with ⟨q, i⟩
        change i = t at ho
        subst ho
        rfl
      · rintro ⟨q, rfl⟩
        rfl
    rw [hfilter_op, Finset.sum_image (fun q1 _ q2 _ h => hι_inj h)]
    have hproc_eq : ∀ q : Fin (size r d),
        (inst r d).proc (ι q) =
          if IsLongPair r d q.val t.val then (r : ℝ) ^ (2 * (d - machFreq d t.val)) else 0 := by
      intro q
      change procTime r d q.val t.val = _
      unfold procTime
      split_ifs with h
      · rw [h.1]
      · rfl
    simp_rw [hproc_eq]
    rw [← Finset.sum_filter, Finset.sum_const, card_longJob_of_mach r d t,
      nsmul_eq_mul, Nat.cast_pow, ← pow_add]
    congr 1
    omega
