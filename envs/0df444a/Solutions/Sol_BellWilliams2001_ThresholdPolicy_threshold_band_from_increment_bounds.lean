-- Prove2me | solution 1 for BellWilliams2001.ThresholdPolicy.threshold_band_from_increment_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T05:57:08.479515+00:00
-- url     : https://prove2.me/submissions/2e299497-8429-4069-ad74-a1a3923515a0

import Mathlib

open Set

private theorem last_visit_bound (q : ℝ → ℝ) (t L K B : ℝ) (ht : 0 ≤ t)
    (hN : 0 ≤ K) (hB : 0 ≤ B)
    (hV : ∃ u ∈ Icc 0 t, q u ≤ L)
    (hAny : ∀ u v, 0 ≤ u → u ≤ v → v ≤ t → |q v-q u| ≤ K*(v-u)+B)
    (hAbove : ∀ u v, 0 ≤ u → u ≤ v → v ≤ t → (∀ s ∈ Ioc u v, L < q s) → q v ≤ q u+B) :
    q t ≤ L+2*B := by
  let E := {u ∈ Icc 0 t | q u ≤ L}
  have hEn : E.Nonempty := by obtain ⟨u,hu,hq⟩ := hV; exact ⟨u,hu,hq⟩
  have hEb : BddAbove E := ⟨t,fun u hu => hu.1.2⟩
  let a := sSup E
  have hat : a ≤ t := csSup_le hEn fun u hu => hu.1.2
  have ha : 0 ≤ a := by obtain ⟨u,hu⟩ := hEn; exact hu.1.1.trans (le_csSup hEb hu)
  have hAfter : ∀ s ∈ Ioc a t, L < q s := by
    intro s hs
    by_contra! h
    exact hs.1.not_ge (le_csSup hEb (show s ∈ E from ⟨⟨ha.trans hs.1.le,hs.2⟩,h⟩))
  have hVal : q a ≤ L+B := by
    by_contra! hb
    let δ := (q a-(L+B))/(K+1)
    have hK1 : 0 < K+1 := by linarith
    have hδ : 0 < δ := div_pos (sub_pos.mpr hb) hK1
    have hδe : δ * (K+1) = q a - (L+B) := div_mul_cancel₀ _ hK1.ne'
    have hs : a-δ < sSup E := by change a-δ<a; linarith
    obtain ⟨u,hu,huNear⟩ := exists_lt_of_lt_csSup hEn hs
    have hua : u ≤ a := le_csSup hEb hu
    have hbnd := (abs_le.1 (hAny u a hu.1.1 hua hat)).2
    have hsmall := mul_le_mul_of_nonneg_left (show a-u ≤ δ by linarith) hN
    have hq : q u ≤ L := hu.2
    nlinarith
  have h := hAbove a t ha hat le_rfl hAfter
  linarith

set_option maxHeartbeats 900000 in
theorem solution (q : ℝ → ℝ) (H L K B α : ℝ) (hH : 0 ≤ H) (hL : 0 ≤ L)
    (hK : 0 ≤ K) (hB : 0 ≤ B) (hα : 0 < α) (hZero : q 0 = 0)
    (hAny : ∀ u v, 0 ≤ u → u ≤ v → v ≤ H → |q v-q u| ≤ K*(v-u)+B)
    (hBelow : ∀ u v, 0 ≤ u → u ≤ v → v ≤ H →
      (∀ s ∈ Ioc u v, q s ≤ L) → α*(v-u)-B ≤ q v-q u)
    (hAbove : ∀ u v, 0 ≤ u → u ≤ v → v ≤ H →
      (∀ s ∈ Ioc u v, L < q s) → q v-q u ≤ -α*(v-u)+B) :
    (∀ t ∈ Icc 0 H, q t ≤ L+2*B) ∧
    (∀ t ∈ Icc 0 H, (∃ u ∈ Icc 0 t, L ≤ q u) → L-2*B ≤ q t) ∧
    (∀ t ∈ Icc 0 H, L+B < α*t → ∃ u ∈ Icc 0 t, L ≤ q u) := by
  refine ⟨?_,?_,?_⟩
  · intro t ht
    refine last_visit_bound q t L K B ht.1 hK hB ⟨0,⟨le_rfl,ht.1⟩,by simpa only [hZero] using hL⟩
      (fun u v hu huv hv => hAny u v hu huv (hv.trans ht.2)) ?_
    intro u v hu huv hv hq
    have h := hAbove u v hu huv (hv.trans ht.2) hq
    linarith [mul_nonneg hα.le (sub_nonneg.mpr huv)]
  · intro t ht hVisit
    have hE : ∃ u ∈ Icc 0 t, (-q u) ≤ -L := by
      obtain ⟨u,hu,h⟩ := hVisit
      exact ⟨u,hu,neg_le_neg h⟩
    have h := last_visit_bound (fun u => -q u) t (-L) K B ht.1 hK hB hE ?_ ?_
    · linarith
    · intro u v hu huv hv
      rw [show -q v - -q u = -(q v-q u) by ring, abs_neg]
      exact hAny u v hu huv (hv.trans ht.2)
    · intro u v hu huv hv hq
      have hw := hBelow u v hu huv (hv.trans ht.2)
        (fun s hs => (neg_lt_neg_iff.1 (hq s hs)).le)
      linarith [mul_nonneg hα.le (sub_nonneg.mpr huv)]
  · intro t ht hh
    by_contra! he
    have h := hBelow 0 t le_rfl ht.1 ht.2
      (fun s hs => (he s ⟨hs.1.le,hs.2⟩).le)
    have hq := he t ⟨ht.1,le_rfl⟩
    rw [hZero,sub_zero] at h
    linarith
