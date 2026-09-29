-- Prove2me | solution 1 for Devaney.sarkovskii_odd_mul_pow_two
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-17T06:08:20.077764+00:00
-- url     : https://prove2.me/submissions/cee687eb-2271-4d6e-80ed-47457cfd908e

import Mathlib
import Definitions.Def_Devaney_sarkovskii

open Devaney Function Set

namespace Sark

/-! ## Translation between `HasPrimePeriod` and `Function.minimalPeriod`. -/

theorem hpp_isPeriodicPt {f : ℝ → ℝ} {x : ℝ} {n : ℕ} (h : HasPrimePeriod f x n) :
    Function.IsPeriodicPt f n x := h.2.1

theorem hpp_minimalPeriod {f : ℝ → ℝ} {x : ℝ} {n : ℕ} (h : HasPrimePeriod f x n) :
    Function.minimalPeriod f x = n := by
  obtain ⟨hn, hfix, hmin⟩ := h
  have hper : Function.IsPeriodicPt f n x := hfix
  have hmem : x ∈ Function.periodicPts f := ⟨n, hn, hper⟩
  have hpos : 0 < Function.minimalPeriod f x :=
    Function.minimalPeriod_pos_of_mem_periodicPts hmem
  have hle : Function.minimalPeriod f x ≤ n := hper.minimalPeriod_le hn
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact absurd (Function.isPeriodicPt_minimalPeriod f x) (hmin _ hpos hlt)
  · exact heq

theorem hpp_of_minimalPeriod {f : ℝ → ℝ} {x : ℝ} {n : ℕ} (hn : 0 < n)
    (h : Function.minimalPeriod f x = n) : HasPrimePeriod f x n := by
  refine ⟨hn, ?_, ?_⟩
  · have := Function.isPeriodicPt_minimalPeriod f x
    rw [h] at this; exact this
  · intro m hm hmn hfx
    have hp : Function.IsPeriodicPt f m x := hfx
    have : Function.minimalPeriod f x ≤ m := hp.minimalPeriod_le hm
    rw [h] at this; omega

end Sark

namespace Sark

/-! ## The orbit of a periodic point, as a `Finset`. -/

open Finset in
/-- The orbit `{x, f x, …, f^[n-1] x}`. -/
noncomputable def orb (f : ℝ → ℝ) (x : ℝ) (n : ℕ) : Finset ℝ :=
  (Finset.range n).image (fun i => f^[i] x)

theorem orb_nonempty {f : ℝ → ℝ} {x : ℝ} {n : ℕ} (hn : 0 < n) : (orb f x n).Nonempty := by
  refine ⟨x, ?_⟩
  simp only [orb, Finset.mem_image, Finset.mem_range]
  exact ⟨0, hn, rfl⟩

theorem orb_maps {f : ℝ → ℝ} {x : ℝ} {n : ℕ} (h : HasPrimePeriod f x n) :
    ∀ b ∈ orb f x n, f b ∈ orb f x n := by
  intro b hb
  simp only [orb, Finset.mem_image, Finset.mem_range] at hb ⊢
  obtain ⟨i, hi, rfl⟩ := hb
  rcases lt_or_eq_of_le (Nat.succ_le_of_lt hi) with hlt | heq
  · exact ⟨i + 1, hlt, by rw [Function.iterate_succ_apply']⟩
  · refine ⟨0, h.1, ?_⟩
    have : f (f^[i] x) = f^[i + 1] x := (Function.iterate_succ_apply' f i x).symm
    have h3 : i + 1 = n := by omega
    rw [this, h3, h.2.1]
    simp

theorem orb_no_fixed {f : ℝ → ℝ} {x : ℝ} {n : ℕ} (hn : 2 ≤ n) (h : HasPrimePeriod f x n) :
    ∀ b ∈ orb f x n, f b ≠ b := by
  intro b hb hfb
  simp only [orb, Finset.mem_image, Finset.mem_range] at hb
  obtain ⟨i, hi, rfl⟩ := hb
  -- a fixed point in the orbit forces `x` itself to be fixed
  have hiter : ∀ j : ℕ, f^[j] (f^[i] x) = f^[i] x := by
    intro j
    induction j with
    | zero => simp
    | succ k ih => rw [Function.iterate_succ_apply', ih, hfb]
  have hx : f^[i] x = x := by
    have h1 := hiter (n - i)
    rw [← Function.iterate_add_apply f (n - i) i x] at h1
    have h2 : n - i + i = n := by omega
    rw [h2, h.2.1] at h1
    exact h1.symm
  have : f x = x := by rw [hx] at hfb; exact hfb
  exact h.2.2 1 (by norm_num) (by omega) (by simpa using this)

/-! ## Main lemma: a periodic point of period `≥ 2` forces a genuine 2-cycle. -/

theorem exists_two_cycle {f : ℝ → ℝ} (hf : Continuous f) {x : ℝ} {n : ℕ}
    (hn : 2 ≤ n) (h : HasPrimePeriod f x n) : ∃ y : ℝ, f (f y) = y ∧ f y ≠ y := by
  classical
  set B := orb f x n with hBdef
  have hne : B.Nonempty := orb_nonempty (by omega)
  have hmaps : ∀ b ∈ B, f b ∈ B := orb_maps h
  have hnofix : ∀ b ∈ B, f b ≠ b := orb_no_fixed hn h
  -- `b0` : the largest orbit point moved to the right
  set S0 := B.filter (fun b => b < f b) with hS0def
  have hS0mem : ∀ b : ℝ, b ∈ S0 ↔ (b ∈ B ∧ b < f b) := by
    intro b; rw [hS0def]; simp [Finset.mem_filter]
  have hminB : B.min' hne ∈ B := B.min'_mem hne
  have hS0ne : S0.Nonempty := by
    refine ⟨B.min' hne, ?_⟩
    rw [hS0mem]
    refine ⟨hminB, ?_⟩
    have h1 : f (B.min' hne) ∈ B := hmaps _ hminB
    have h2 : B.min' hne ≤ f (B.min' hne) := B.min'_le _ h1
    exact lt_of_le_of_ne h2 (Ne.symm (hnofix _ hminB))
  set b0 := S0.max' hS0ne with hb0def
  have hb0S : b0 ∈ S0 := S0.max'_mem hS0ne
  have hb0B : b0 ∈ B := ((hS0mem b0).1 hb0S).1
  have hb0lt : b0 < f b0 := ((hS0mem b0).1 hb0S).2
  have hb1B : f b0 ∈ B := hmaps _ hb0B
  -- every orbit point strictly to the right of `b0` moves left
  have hright : ∀ b ∈ B, b0 < b → f b < b := by
    intro b hbB hlt
    have hnotS0 : b ∉ S0 := by
      intro hbS
      exact absurd (S0.le_max' b hbS) (not_le.2 hlt)
    have : ¬ (b < f b) := by
      intro hc; exact hnotS0 ((hS0mem b).2 ⟨hbB, hc⟩)
    exact lt_of_le_of_ne (not_lt.1 this) (hnofix _ hbB)
  -- some orbit point in `(b0, f b0]` lands at or below `b0`
  set S := B.filter (fun b => b0 < b ∧ b ≤ f b0) with hSdef
  have hSmem : ∀ b : ℝ, b ∈ S ↔ (b ∈ B ∧ b0 < b ∧ b ≤ f b0) := by
    intro b; rw [hSdef]; simp [Finset.mem_filter, and_assoc]
  have hSne : S.Nonempty := ⟨f b0, (hSmem _).2 ⟨hb1B, hb0lt, le_refl _⟩⟩
  have hexj : ∃ bj ∈ S, f bj ≤ b0 := by
    by_contra hcon
    push_neg at hcon
    have hinv : ∀ b ∈ S, f b ∈ S := by
      intro b hbS
      obtain ⟨hbB, hlt, hle⟩ := (hSmem b).1 hbS
      have h1 : f b < b := hright b hbB hlt
      exact (hSmem _).2 ⟨hmaps _ hbB, hcon b hbS, le_trans (le_of_lt h1) hle⟩
    have hm := S.min'_mem hSne
    have h1 : f (S.min' hSne) ∈ S := hinv _ hm
    have h2 : S.min' hSne ≤ f (S.min' hSne) := S.min'_le _ h1
    obtain ⟨hbB, hlt, _⟩ := (hSmem _).1 hm
    exact absurd h2 (not_le.2 (hright _ hbB hlt))
  obtain ⟨bj, hbjS, hbjle⟩ := hexj
  obtain ⟨hbjB, hbjlt, hbjle1⟩ := (hSmem _).1 hbjS
  -- a point `c` in `(b0, f b0]` with `f c = b0`
  have hc0 : b0 ∈ Set.Icc (f bj) (f b0) := ⟨hbjle, le_of_lt hb0lt⟩
  obtain ⟨c, hcmem, hfc⟩ :=
    intermediate_value_Icc' (le_of_lt hbjlt) hf.continuousOn hc0
  have hcne : c ≠ b0 := by
    intro hce
    rw [hce] at hfc
    exact absurd hfc (ne_of_gt hb0lt)
  have hcgt : b0 < c := lt_of_le_of_ne hcmem.1 (Ne.symm hcne)
  have hcle : c ≤ f b0 := le_trans hcmem.2 hbjle1
  rcases eq_or_lt_of_le hcle with hceq | hclt
  · -- `f b0 = c` and `f c = b0` : `b0` itself is a 2-cycle
    refine ⟨b0, ?_, ?_⟩
    · rw [← hceq, hfc]
    · rw [ne_comm]; exact ne_of_lt hb0lt
  · -- a fixed point `δ ∈ (b0, c)`
    have hcont : Continuous fun t => f t - t := hf.sub continuous_id
    have hd0 : (0:ℝ) ∈ Set.Icc (f c - c) (f b0 - b0) := by
      constructor
      · rw [hfc]; linarith
      · linarith
    obtain ⟨d, hdmem, hfd⟩ :=
      intermediate_value_Icc' (le_of_lt hcgt) hcont.continuousOn hd0
    have hfd' : f d = d := by linarith [hfd]
    have hdne0 : d ≠ b0 := by
      intro hh; rw [hh] at hfd'; exact absurd hfd' (ne_of_gt hb0lt)
    have hdnec : d ≠ c := by
      intro hh; rw [hh, hfc] at hfd'; exact absurd hfd'.symm (ne_of_gt hcgt)
    have hdgt : b0 < d := lt_of_le_of_ne hdmem.1 (Ne.symm hdne0)
    have hdlt : d < c := lt_of_le_of_ne hdmem.2 hdnec
    -- the right endpoint `M`
    set M := B.max' hne with hMdef
    have hMB : M ∈ B := B.max'_mem hne
    have hMge : f b0 ≤ M := B.le_max' _ hb1B
    have hcM : c < M := lt_of_lt_of_le hclt hMge
    set psi := fun t => f (f t) - t with hpsidef
    have hpsicont : Continuous psi := ((hf.comp hf).sub continuous_id)
    have hpsic : 0 < psi c := by
      simp only [hpsidef, hfc]; linarith
    by_cases hK : (Set.Icc c M ∩ {t | f t = t}).Nonempty
    · have hKcomp : IsCompact (Set.Icc c M ∩ {t | f t = t}) :=
        (isCompact_Icc).inter_right (isClosed_eq hf continuous_id)
      have hgmem : sInf (Set.Icc c M ∩ {t | f t = t}) ∈ Set.Icc c M ∩ {t | f t = t} :=
        hKcomp.sInf_mem hK
      set g := sInf (Set.Icc c M ∩ {t | f t = t}) with hgdef
      have hfg : f g = g := hgmem.2
      have hgc : c ≤ g := hgmem.1.1
      have hgM : g ≤ M := hgmem.1.2
      -- `ε ∈ [c, g]` with `f ε = d`
      have hemem : d ∈ Set.Icc (f c) (f g) := by
        rw [hfc, hfg]; exact ⟨le_of_lt hdgt, le_of_lt (lt_of_lt_of_le hdlt hgc)⟩
      obtain ⟨e, hemem', hfe⟩ := intermediate_value_Icc hgc hf.continuousOn hemem
      have hene : e ≠ g := by
        intro hh; rw [hh, hfg] at hfe
        exact absurd (hfe ▸ hgc) (not_le.2 hdlt)
      have helt : e < g := lt_of_le_of_ne hemem'.2 hene
      have hce : c ≤ e := hemem'.1
      have hpsie : psi e < 0 := by
        simp only [hpsidef, hfe, hfd']
        linarith [lt_of_lt_of_le hdlt hce]
      obtain ⟨y, hymem, hpsiy⟩ :=
        intermediate_value_Icc' hce hpsicont.continuousOn
          (⟨le_of_lt hpsie, le_of_lt hpsic⟩ : (0:ℝ) ∈ Set.Icc (psi e) (psi c))
      refine ⟨y, by simpa [hpsidef, sub_eq_zero] using hpsiy, ?_⟩
      intro hyfix
      have hymemK : y ∈ Set.Icc c M ∩ {t | f t = t} :=
        ⟨⟨hymem.1, le_trans (le_trans hymem.2 (le_of_lt helt)) hgM⟩, hyfix⟩
      have : g ≤ y := csInf_le hKcomp.bddBelow hymemK
      exact absurd (lt_of_le_of_lt hymem.2 helt) (not_lt.2 this)
    · have hnofix' : ∀ t ∈ Set.Icc c M, f t ≠ t := by
        intro t ht hft
        exact hK ⟨t, ht, hft⟩
      have hpsiM : psi M ≤ 0 := by
        have : f (f M) ∈ B := hmaps _ (hmaps _ hMB)
        simp only [hpsidef]
        linarith [B.le_max' _ this]
      obtain ⟨y, hymem, hpsiy⟩ :=
        intermediate_value_Icc' (le_of_lt hcM) hpsicont.continuousOn
          (⟨hpsiM, le_of_lt hpsic⟩ : (0:ℝ) ∈ Set.Icc (psi M) (psi c))
      exact ⟨y, by simpa [hpsidef, sub_eq_zero] using hpsiy, hnofix' y hymem⟩

end Sark

namespace Sark

/-- From a genuine 2-cycle one extracts a fixed point by the intermediate value theorem. -/
theorem exists_fixed_of_two_cycle {f : ℝ → ℝ} (hf : Continuous f) {y : ℝ}
    (h2 : f (f y) = y) (hne : f y ≠ y) : ∃ z : ℝ, f z = z := by
  have hcont : Continuous fun t => f t - t := hf.sub continuous_id
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- `f y < y`
    have hmem : (0:ℝ) ∈ Set.Icc ((fun t => f t - t) y) ((fun t => f t - t) (f y)) := by
      simp only [h2]
      constructor <;> [linarith; linarith]
    obtain ⟨z, _, hz⟩ := intermediate_value_Icc' (le_of_lt hlt) hcont.continuousOn hmem
    exact ⟨z, by linarith [hz]⟩
  · have hmem : (0:ℝ) ∈ Set.Icc ((fun t => f t - t) (f y)) ((fun t => f t - t) y) := by
      simp only [h2]
      constructor <;> [linarith; linarith]
    obtain ⟨z, _, hz⟩ := intermediate_value_Icc' (le_of_lt hgt) hcont.continuousOn hmem
    exact ⟨z, by linarith [hz]⟩

/-- A point whose `2 ^ a`-th iterate returns but whose `2 ^ (a-1)`-th does not has prime
period exactly `2 ^ a`. -/
theorem hpp_pow_two {f : ℝ → ℝ} {y : ℝ} {a : ℕ} (ha : 1 ≤ a)
    (h1 : f^[2 ^ a] y = y) (h2 : f^[2 ^ (a - 1)] y ≠ y) : HasPrimePeriod f y (2 ^ a) := by
  have hper : Function.IsPeriodicPt f (2 ^ a) y := h1
  have hdvd : Function.minimalPeriod f y ∣ 2 ^ a := hper.minimalPeriod_dvd
  obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hja : j = a := by
    by_contra hne
    have hjlt : j ≤ a - 1 := by omega
    have : Function.minimalPeriod f y ∣ 2 ^ (a - 1) := by
      rw [hjeq]; exact pow_dvd_pow 2 hjlt
    have hp : Function.IsPeriodicPt f (2 ^ (a - 1)) y :=
      (Function.isPeriodicPt_minimalPeriod f y).trans_dvd this
    exact h2 hp
  refine hpp_of_minimalPeriod (Nat.two_pow_pos a) ?_
  rw [hjeq, hja]

theorem sarkovskii_pow_two_aux (f : ℝ → ℝ) (hf : Continuous f) (m : ℕ)
    (h : ∃ x, HasPrimePeriod f x (2 ^ m)) (a : ℕ) (ha : a < m) :
    ∃ x, HasPrimePeriod f x (2 ^ a) := by
  obtain ⟨x, hx⟩ := h
  have hm1 : 1 ≤ m := by omega
  rcases Nat.eq_zero_or_pos a with rfl | ha1
  · -- a fixed point
    have h2m : (2:ℕ) ≤ 2 ^ m := by
      calc (2:ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm1
    obtain ⟨y, hy2, hyne⟩ := exists_two_cycle hf h2m hx
    obtain ⟨z, hz⟩ := exists_fixed_of_two_cycle hf hy2 hyne
    exact ⟨z, by refine ⟨by norm_num, by simpa using hz, ?_⟩; intro k hk hk1; omega⟩
  · -- `g = f^[2^(a-1)]` has a periodic point of prime period at least two
    set g := f^[2 ^ (a - 1)] with hgdef
    have hgc : Continuous g := hf.iterate _
    have hkey : ∀ K : ℕ, g^[K] = f^[2 ^ (a - 1) * K] := by
      intro K; rw [hgdef, ← Function.iterate_mul]
    have hexp : 2 ^ (a - 1) * 2 ^ (m - a + 1) = 2 ^ m := by
      rw [← pow_add]; congr 1; omega
    have hgper : g^[2 ^ (m - a + 1)] x = x := by
      rw [hkey, hexp]; exact hx.2.1
    have hgmem : x ∈ Function.periodicPts g :=
      ⟨2 ^ (m - a + 1), Nat.two_pow_pos _, hgper⟩
    have hgpos : 0 < Function.minimalPeriod g x :=
      Function.minimalPeriod_pos_of_mem_periodicPts hgmem
    have hgx : g x ≠ x := by
      rw [hgdef]
      refine hx.2.2 (2 ^ (a - 1)) (Nat.two_pow_pos _) ?_
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    have hgne1 : Function.minimalPeriod g x ≠ 1 := by
      intro hh
      have := Function.isPeriodicPt_minimalPeriod g x
      rw [hh] at this
      exact hgx (by simpa [Function.IsPeriodicPt, Function.IsFixedPt] using this)
    have hg2 : 2 ≤ Function.minimalPeriod g x := by omega
    obtain ⟨y, hy2, hyne⟩ :=
      exists_two_cycle hgc hg2 (hpp_of_minimalPeriod hgpos rfl)
    refine ⟨y, hpp_pow_two ha1 ?_ ?_⟩
    · have : f^[2 ^ (a - 1)] (f^[2 ^ (a - 1)] y) = y := hy2
      rw [← Function.iterate_add_apply] at this
      have he : 2 ^ (a - 1) + 2 ^ (a - 1) = 2 ^ a := by
        have hh : (2:ℕ) ^ a = 2 ^ (a - 1 + 1) := by congr 1; omega
        rw [hh, pow_succ, Nat.mul_two]
      rwa [he] at this
    · exact hyne

end Sark

namespace Sark

/-- If `f` has a periodic point whose prime period is **not** a power of two, then `f` has a
point of prime period `2 ^ i` for every `i ≥ 1`. -/
theorem exists_pow_two_of_not_pow_two {f : ℝ → ℝ} (hf : Continuous f) {x : ℝ} {n : ℕ}
    (h : HasPrimePeriod f x n) (hn : ∀ m : ℕ, n ≠ 2 ^ m) {i : ℕ} (hi : 1 ≤ i) :
    ∃ y : ℝ, HasPrimePeriod f y (2 ^ i) := by
  classical
  set K := 2 ^ (i - 1) with hKdef
  set g := f^[K] with hgdef
  have hgc : Continuous g := hf.iterate _
  have hmin : Function.minimalPeriod f x = n := hpp_minimalPeriod h
  have hgper : g^[n] x = x := by
    rw [hgdef, ← Function.iterate_mul]
    have hp : Function.IsPeriodicPt f n x := h.2.1
    have := hp.mul_const K
    rw [Nat.mul_comm] at this
    exact this
  have hgmem : x ∈ Function.periodicPts g := ⟨n, h.1, hgper⟩
  have hgpos : 0 < Function.minimalPeriod g x :=
    Function.minimalPeriod_pos_of_mem_periodicPts hgmem
  have hgx : g x ≠ x := by
    intro hc
    have hp : Function.IsPeriodicPt f K x := hc
    have hd : n ∣ K := by rw [← hmin]; exact hp.minimalPeriod_dvd
    rw [hKdef] at hd
    obtain ⟨j, _, hje⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
    exact hn j hje
  have hgne1 : Function.minimalPeriod g x ≠ 1 := by
    intro hh
    have := Function.isPeriodicPt_minimalPeriod g x
    rw [hh] at this
    exact hgx (by simpa [Function.IsPeriodicPt, Function.IsFixedPt] using this)
  have hg2 : 2 ≤ Function.minimalPeriod g x := by omega
  obtain ⟨y, hy2, hyne⟩ := exists_two_cycle hgc hg2 (hpp_of_minimalPeriod hgpos rfl)
  refine ⟨y, hpp_pow_two hi ?_ hyne⟩
  have hthis : f^[K] (f^[K] y) = y := hy2
  rw [← Function.iterate_add_apply] at hthis
  have he : K + K = 2 ^ i := by
    have hh : (2:ℕ) ^ i = 2 ^ (i - 1 + 1) := by congr 1; omega
    rw [hKdef, hh, pow_succ, Nat.mul_two]
  rwa [he] at hthis

/-- A continuous map of the line with a periodic point whose prime period is not a power of two
has infinitely many periodic points. -/
theorem infinite_periodicPoints_aux (f : ℝ → ℝ) (hf : Continuous f) (n : ℕ)
    (h : ∃ x, HasPrimePeriod f x n) (hn : ∀ m : ℕ, n ≠ 2 ^ m) :
    {x : ℝ | ∃ k > 0, f^[k] x = x}.Infinite := by
  classical
  obtain ⟨x, hx⟩ := h
  choose Y hY using fun i : ℕ =>
    exists_pow_two_of_not_pow_two hf hx hn (i := i + 1) (by omega)
  refine Set.infinite_of_injective_forall_mem (f := Y) ?_ ?_
  · intro i j hij
    have h1 := hpp_minimalPeriod (hY i)
    have h2 := hpp_minimalPeriod (hY j)
    rw [hij, h2] at h1
    have := Nat.pow_right_injective (le_refl 2) h1.symm
    omega
  · intro i
    exact ⟨2 ^ (i + 1), Nat.two_pow_pos _, (hY i).2.1⟩

end Sark

open Set Function

namespace Shk

/-! ## Part 1: covering of intervals, fixed points, and the loop lemma -/

/-- `Cov f a b c d` says that the image under `f` of the closed interval with endpoints
`a, b` contains the closed interval with endpoints `c, d`. -/
def Cov (f : ℝ → ℝ) (a b c d : ℝ) : Prop := uIcc c d ⊆ f '' uIcc a b

theorem cov_of_subset {f : ℝ → ℝ} (hf : Continuous f) {a b c d : ℝ}
    (h : uIcc c d ⊆ uIcc (f a) (f b)) : Cov f a b c d :=
  h.trans (intermediate_value_uIcc hf.continuousOn)

/-- The basic covering criterion: if `c` and `d` both lie between `f a` and `f b`, then
`[a,b]` covers `[c,d]`. -/
theorem cov_of_mem {f : ℝ → ℝ} (hf : Continuous f) {a b c d : ℝ}
    (hc : c ∈ uIcc (f a) (f b)) (hd : d ∈ uIcc (f a) (f b)) : Cov f a b c d :=
  cov_of_subset hf (uIcc_subset_uIcc hc hd)

theorem Cov.mono {f : ℝ → ℝ} {a b c d c' d' : ℝ} (h : Cov f a b c d)
    (h' : uIcc c' d' ⊆ uIcc c d) : Cov f a b c' d' := h'.trans h

/-- A closed interval that covers itself contains a fixed point. -/
theorem exists_fixed_of_cov_self {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ}
    (h : Cov f a b a b) : ∃ z ∈ uIcc a b, f z = z := by
  obtain ⟨p, hp, hfp⟩ := h (left_mem_uIcc)
  obtain ⟨q, hq, hfq⟩ := h (right_mem_uIcc)
  have hcont : Continuous (fun x : ℝ => f x - x) := hf.sub continuous_id
  have h0 : (0:ℝ) ∈ uIcc (f p - p) (f q - q) := by
    rw [hfp, hfq, mem_uIcc]
    rcases mem_uIcc.1 hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rcases mem_uIcc.1 hq with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
      first
        | (left; constructor <;> linarith)
        | (right; constructor <;> linarith)
  obtain ⟨z, hz, hz0⟩ := intermediate_value_uIcc (f := fun x : ℝ => f x - x)
    hcont.continuousOn h0
  have hz0' : f z - z = 0 := hz0
  exact ⟨z, uIcc_subset_uIcc hp hq hz, by linarith⟩

/-- Auxiliary form of the exact-subinterval lemma, with the two chosen preimages ordered. -/
private theorem subint_aux {f : ℝ → ℝ} (hf : Continuous f) {p q c d : ℝ} (hpq : p < q)
    (hp : f p = c) (hq : f q = d) (hcd : c ≠ d) :
    ∃ u v : ℝ, p ≤ u ∧ u < v ∧ v ≤ q ∧ f '' uIcc u v = uIcc c d := by
  classical
  obtain ⟨u, hpu, huq, hfu, hmax⟩ :
      ∃ u : ℝ, p ≤ u ∧ u ≤ q ∧ f u = c ∧ ∀ y, p ≤ y → y ≤ q → f y = c → y ≤ u := by
    have hcl : IsClosed (Icc p q ∩ f ⁻¹' {c}) :=
      isClosed_Icc.inter (isClosed_singleton.preimage hf)
    have hne : (Icc p q ∩ f ⁻¹' {c}).Nonempty := ⟨p, ⟨le_refl p, hpq.le⟩, hp⟩
    have hbdd : BddAbove (Icc p q ∩ f ⁻¹' {c}) := ⟨q, fun x hx => hx.1.2⟩
    have hmem := hcl.csSup_mem hne hbdd
    exact ⟨_, hmem.1.1, hmem.1.2, hmem.2, fun y h1 h2 h3 => le_csSup hbdd ⟨⟨h1, h2⟩, h3⟩⟩
  have huq' : u < q := by
    rcases eq_or_lt_of_le huq with h | h
    · exact absurd (by rw [← hfu, h, hq] : c = d) hcd
    · exact h
  obtain ⟨v, huv, hvq, hfv, hmin⟩ :
      ∃ v : ℝ, u ≤ v ∧ v ≤ q ∧ f v = d ∧ ∀ y, u ≤ y → y ≤ q → f y = d → v ≤ y := by
    have hcl : IsClosed (Icc u q ∩ f ⁻¹' {d}) :=
      isClosed_Icc.inter (isClosed_singleton.preimage hf)
    have hne : (Icc u q ∩ f ⁻¹' {d}).Nonempty := ⟨q, ⟨huq, le_refl q⟩, hq⟩
    have hbdd : BddBelow (Icc u q ∩ f ⁻¹' {d}) := ⟨u, fun x hx => hx.1.1⟩
    have hmem := hcl.csInf_mem hne hbdd
    exact ⟨_, hmem.1.1, hmem.1.2, hmem.2, fun y h1 h2 h3 => csInf_le hbdd ⟨⟨h1, h2⟩, h3⟩⟩
  have huv' : u < v := by
    rcases eq_or_lt_of_le huv with h | h
    · exact absurd (by rw [← hfu, h, hfv] : c = d) hcd
    · exact h
  refine ⟨u, v, hpu, huv', hvq, subset_antisymm ?_ ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [uIcc_of_le huv'.le] at hx
    by_contra hfx
    have key : (d ∈ uIcc c (f x) ∧ d ≠ f x) ∨ (c ∈ uIcc (f x) d ∧ c ≠ f x) := by
      rw [mem_uIcc] at hfx
      push_neg at hfx
      rcases le_total c d with hle | hle
      · rcases lt_or_ge (f x) c with h1 | h1
        · exact Or.inr ⟨mem_uIcc.2 (Or.inl ⟨h1.le, hle⟩), by linarith⟩
        · have h2 : d < f x := by
            by_contra h3; push_neg at h3
            exact absurd (hfx.1 h1) (by linarith)
          exact Or.inl ⟨mem_uIcc.2 (Or.inl ⟨hle, h2.le⟩), by linarith⟩
      · rcases lt_or_ge (f x) d with h1 | h1
        · exact Or.inl ⟨mem_uIcc.2 (Or.inr ⟨h1.le, hle⟩), by linarith⟩
        · have h2 : c < f x := by
            by_contra h3; push_neg at h3
            exact absurd (hfx.2 h1) (by linarith)
          exact Or.inr ⟨mem_uIcc.2 (Or.inr ⟨hle, h2.le⟩), by linarith⟩
    rcases key with ⟨hd1, hd2⟩ | ⟨hc1, hc2⟩
    · have himg : d ∈ f '' uIcc u x :=
        intermediate_value_uIcc hf.continuousOn (by rw [hfu]; exact hd1)
      obtain ⟨y, hy, hfy⟩ := himg
      rw [uIcc_of_le hx.1] at hy
      have hvy : v ≤ y := hmin y hy.1 (le_trans (le_trans hy.2 hx.2) hvq) hfy
      have hxv : x = v := le_antisymm hx.2 (le_trans hvy hy.2)
      exact hd2 (by rw [hxv, hfv])
    · have himg : c ∈ f '' uIcc x v :=
        intermediate_value_uIcc hf.continuousOn (by rw [hfv]; exact hc1)
      obtain ⟨y, hy, hfy⟩ := himg
      rw [uIcc_of_le hx.2] at hy
      have hyu : y ≤ u := hmax y (le_trans hpu (le_trans hx.1 hy.1)) (le_trans hy.2 hvq) hfy
      have hxu : x = u := le_antisymm (le_trans hy.1 hyu) hx.1
      exact hc2 (by rw [hxu, hfu])
  · have := intermediate_value_uIcc (f := f) (a := u) (b := v) hf.continuousOn
    rwa [hfu, hfv] at this

/-- **Exact subinterval lemma.**  If `[a,b]` covers `[c,d]`, then `[a,b]` contains a closed
subinterval mapped by `f` exactly *onto* `[c,d]`. -/
theorem exists_exact_subinterval {f : ℝ → ℝ} (hf : Continuous f) {a b c d : ℝ}
    (h : Cov f a b c d) :
    ∃ u v : ℝ, uIcc u v ⊆ uIcc a b ∧ f '' uIcc u v = uIcc c d := by
  obtain ⟨p, hp, hfp⟩ := h (left_mem_uIcc)
  obtain ⟨q, hq, hfq⟩ := h (right_mem_uIcc)
  rcases eq_or_ne c d with rfl | hcd
  · exact ⟨p, p, by simpa using hp, by simp [hfp]⟩
  · have hpq : p ≠ q := by rintro rfl; exact hcd (hfp ▸ hfq ▸ rfl)
    have main : ∀ p' q' : ℝ, p' < q' → p' ∈ uIcc a b → q' ∈ uIcc a b →
        ∀ c' d' : ℝ, f p' = c' → f q' = d' → c' ≠ d' →
        ∃ u v : ℝ, uIcc u v ⊆ uIcc a b ∧ f '' uIcc u v = uIcc c' d' := by
      intro p' q' hlt hp' hq' c' d' h1 h2 h3
      obtain ⟨u, v, hu1, hu2, hu3, hu4⟩ := subint_aux hf hlt h1 h2 h3
      refine ⟨u, v, ?_, hu4⟩
      have hsub : uIcc u v ⊆ uIcc p' q' :=
        uIcc_subset_uIcc (mem_uIcc.2 (Or.inl ⟨hu1, le_trans hu2.le hu3⟩))
          (mem_uIcc.2 (Or.inl ⟨le_trans hu1 hu2.le, hu3⟩))
      exact hsub.trans (uIcc_subset_uIcc hp' hq')
    rcases lt_or_gt_of_ne hpq with hlt | hlt
    · exact main p q hlt hp hq c d hfp hfq hcd
    · obtain ⟨u, v, h1, h2⟩ := main q p hlt hq hp d c hfq hfp (Ne.symm hcd)
      exact ⟨u, v, h1, by rw [h2, uIcc_comm]⟩

/-- Backward construction along a chain of coverings: there is a closed interval inside
`[A 0, B 0]` whose `k+1`-st image is exactly `[c,d]`, and whose `i`-th image stays inside
`[A i, B i]`. -/
theorem chain_pre {f : ℝ → ℝ} (hf : Continuous f) (A B : ℕ → ℝ) :
    ∀ (k : ℕ) (c d : ℝ), (∀ i < k, Cov f (A i) (B i) (A (i+1)) (B (i+1))) →
      Cov f (A k) (B k) c d →
      ∃ u v : ℝ, f^[k+1] '' uIcc u v = uIcc c d ∧
        ∀ i ≤ k, f^[i] '' uIcc u v ⊆ uIcc (A i) (B i) := by
  intro k
  induction k with
  | zero =>
      intro c d _ hcov
      obtain ⟨u, v, h1, h2⟩ := exists_exact_subinterval hf hcov
      refine ⟨u, v, by simpa using h2, ?_⟩
      intro i hi
      have : i = 0 := by omega
      subst this
      simpa using h1
  | succ k ih =>
      intro c d hchain hcov
      obtain ⟨u', v', h1, h2⟩ := exists_exact_subinterval hf hcov
      have hcov' : Cov f (A k) (B k) u' v' := h1.trans (hchain k (by omega))
      obtain ⟨u, v, e1, e2⟩ := ih u' v' (fun i hi => hchain i (by omega)) hcov'
      refine ⟨u, v, ?_, ?_⟩
      · rw [Function.iterate_succ', Set.image_comp, e1, h2]
      · intro i hi
        rcases Nat.lt_or_ge i (k+1) with h | h
        · exact e2 i (by omega)
        · have hik : i = k + 1 := by omega
          subst hik
          rw [e1]; exact h1

/-- **Loop lemma.**  A cycle of closed intervals `[A 0,B 0] → [A 1,B 1] → ⋯ → [A n,B n] =
[A 0,B 0]` contains a point `y` with `f^[n] y = y` which follows the loop. -/
theorem exists_loop_point {f : ℝ → ℝ} (hf : Continuous f) (n : ℕ) (hn : 0 < n)
    (A B : ℕ → ℝ) (hcov : ∀ i < n, Cov f (A i) (B i) (A (i+1)) (B (i+1)))
    (hA : A n = A 0) (hB : B n = B 0) :
    ∃ y, f^[n] y = y ∧ ∀ i < n, f^[i] y ∈ uIcc (A i) (B i) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨u, v, e1, e2⟩ := chain_pre hf A B k (A 0) (B 0) (fun i hi => hcov i (by omega))
    (by rw [← hA, ← hB]; exact hcov k (by omega))
  have hK : uIcc u v ⊆ uIcc (A 0) (B 0) := by simpa using e2 0 (by omega)
  have hself : Cov (f^[k+1]) u v u v := by
    show uIcc u v ⊆ f^[k+1] '' uIcc u v
    rw [e1]; exact hK
  obtain ⟨y, hy, hfy⟩ := exists_fixed_of_cov_self (hf.iterate (k+1)) hself
  exact ⟨y, hfy, fun i hi => e2 i (by omega) ⟨y, hy, rfl⟩⟩

/-! ## Part 2: prime periods and orbits -/

open Devaney

theorem hpp_minimalPeriod {f : ℝ → ℝ} {x : ℝ} {n : ℕ} (h : HasPrimePeriod f x n) :
    Function.minimalPeriod f x = n := by
  obtain ⟨hn, hfix, hmin⟩ := h
  have hper : Function.IsPeriodicPt f n x := hfix
  have hmem : x ∈ Function.periodicPts f := ⟨n, hn, hper⟩
  have hpos : 0 < Function.minimalPeriod f x :=
    Function.minimalPeriod_pos_of_mem_periodicPts hmem
  have hle : Function.minimalPeriod f x ≤ n := hper.minimalPeriod_le hn
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact absurd (Function.isPeriodicPt_minimalPeriod f x) (hmin _ hpos hlt)
  · exact heq

theorem hpp_of_minimalPeriod {f : ℝ → ℝ} {x : ℝ} {n : ℕ} (hn : 0 < n)
    (h : Function.minimalPeriod f x = n) : HasPrimePeriod f x n := by
  refine ⟨hn, ?_, ?_⟩
  · have := Function.isPeriodicPt_minimalPeriod f x
    rw [h] at this; exact this
  · intro k hk hkn hfx
    have hp : Function.IsPeriodicPt f k x := hfx
    have := hp.minimalPeriod_le hk
    rw [h] at this; omega

/-- To have prime period `n` it suffices to be fixed by `f^[n]` and by no `f^[p]` with
`p` a proper divisor of `n`. -/
theorem hpp_of_dvd {f : ℝ → ℝ} {x : ℝ} {n : ℕ} (hn : 0 < n) (hfix : f^[n] x = x)
    (h : ∀ p, p ∣ n → p < n → f^[p] x ≠ x) : HasPrimePeriod f x n := by
  have hper : Function.IsPeriodicPt f n x := hfix
  have hdvd : Function.minimalPeriod f x ∣ n := hper.minimalPeriod_dvd
  refine hpp_of_minimalPeriod hn ?_
  by_contra hne
  exact h _ hdvd (lt_of_le_of_ne (Nat.le_of_dvd hn hdvd) hne)
    (Function.isPeriodicPt_minimalPeriod f x)

/-- The orbit of `x`, as a finite set. -/
noncomputable def orb (f : ℝ → ℝ) (x : ℝ) (n : ℕ) : Finset ℝ :=
  (Finset.range n).image (fun i => f^[i] x)

theorem mem_orb {f : ℝ → ℝ} {x y : ℝ} {n : ℕ} :
    y ∈ orb f x n ↔ ∃ i < n, f^[i] x = y := by
  simp [orb, Finset.mem_image, Finset.mem_range]

theorem self_mem_orb {f : ℝ → ℝ} {x : ℝ} {n : ℕ} (hn : 0 < n) : x ∈ orb f x n :=
  mem_orb.2 ⟨0, hn, rfl⟩

theorem orb_nonempty {f : ℝ → ℝ} {x : ℝ} {n : ℕ} (hn : 0 < n) : (orb f x n).Nonempty :=
  ⟨x, self_mem_orb hn⟩

/-- Iterates at indices below the prime period are pairwise distinct. -/
theorem iterate_inj {f : ℝ → ℝ} {x : ℝ} {n : ℕ} (h : HasPrimePeriod f x n)
    {i j : ℕ} (hi : i < n) (hj : j < n) (hij : f^[i] x = f^[j] x) : i = j := by
  have hmp : Function.minimalPeriod f x = n := hpp_minimalPeriod h
  have aux : ∀ p q : ℕ, p < n → q < n → p < q → f^[p] x = f^[q] x → False := by
    intro p q hp hq hpq hpq'
    have key : f^[n - q + p] x = x := by
      rw [Function.iterate_add_apply, hpq', ← Function.iterate_add_apply,
        show n - q + q = n by omega]
      exact h.2.1
    have hper : Function.IsPeriodicPt f (n - q + p) x := key
    have hd := hper.minimalPeriod_dvd
    rw [hmp] at hd
    have := Nat.le_of_dvd (by omega) hd
    omega
  rcases lt_trichotomy i j with hlt | heq | hlt
  · exact (aux i j hi hj hlt hij).elim
  · exact heq
  · exact (aux j i hj hi hlt hij.symm).elim

theorem orb_card {f : ℝ → ℝ} {x : ℝ} {n : ℕ} (h : HasPrimePeriod f x n) :
    (orb f x n).card = n := by
  rw [orb, Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj hij
  exact iterate_inj h (Finset.mem_range.1 hi) (Finset.mem_range.1 hj) hij

theorem orb_maps {f : ℝ → ℝ} {x : ℝ} {n : ℕ} (h : HasPrimePeriod f x n) {y : ℝ}
    (hy : y ∈ orb f x n) : f y ∈ orb f x n := by
  obtain ⟨i, hi, rfl⟩ := mem_orb.1 hy
  have hstep : f (f^[i] x) = f^[i + 1] x := (Function.iterate_succ_apply' f i x).symm
  rw [hstep]
  rcases Nat.lt_or_ge (i + 1) n with hlt | hge
  · exact mem_orb.2 ⟨i + 1, hlt, rfl⟩
  · have : i + 1 = n := by omega
    rw [this, h.2.1]
    exact self_mem_orb h.1

theorem orb_iterate {f : ℝ → ℝ} {x : ℝ} {n : ℕ} (h : HasPrimePeriod f x n) {y : ℝ}
    (hy : y ∈ orb f x n) (j : ℕ) : f^[j] y ∈ orb f x n := by
  induction j with
  | zero => simpa using hy
  | succ j ih => rw [Function.iterate_succ_apply']; exact orb_maps h ih

theorem orb_hpp {f : ℝ → ℝ} {x : ℝ} {n : ℕ} (h : HasPrimePeriod f x n) {y : ℝ}
    (hy : y ∈ orb f x n) : HasPrimePeriod f y n := by
  obtain ⟨i, hi, rfl⟩ := mem_orb.1 hy
  refine hpp_of_minimalPeriod h.1 ?_
  have hmem : x ∈ Function.periodicPts f := ⟨n, h.1, h.2.1⟩
  rw [Function.minimalPeriod_apply_iterate hmem, hpp_minimalPeriod h]

theorem orb_no_fix {f : ℝ → ℝ} {x : ℝ} {n : ℕ} (h : HasPrimePeriod f x n) (hn : 2 ≤ n)
    {y : ℝ} (hy : y ∈ orb f x n) : f y ≠ y := by
  intro hfy
  exact (orb_hpp h hy).2.2 1 one_pos (by omega) (by simpa using hfy)

/-- Any point of the orbit is reached from any other by a positive number of iterations. -/
theorem orb_reach {f : ℝ → ℝ} {x : ℝ} {n : ℕ} (h : HasPrimePeriod f x n) {y z : ℝ}
    (hy : y ∈ orb f x n) (hz : z ∈ orb f x n) : ∃ k, 0 < k ∧ k ≤ n ∧ f^[k] y = z := by
  obtain ⟨i, hi, rfl⟩ := mem_orb.1 hy
  obtain ⟨j, hj, rfl⟩ := mem_orb.1 hz
  rcases Nat.lt_or_ge i j with hlt | hge
  · refine ⟨j - i, by omega, by omega, ?_⟩
    rw [← Function.iterate_add_apply, show j - i + i = j by omega]
  · refine ⟨j + n - i, by omega, by omega, ?_⟩
    rw [← Function.iterate_add_apply, show j + n - i + i = j + n by omega,
      Function.iterate_add_apply, h.2.1]

/-! ## Part 3: the two-interval graph gives every period -/

/-- If two closed intervals `I₁, I₂` meet in at most the single point `e`, and
`I₂ → I₂`, `I₂ → I₁`, `I₁ → I₂`, then `f` has points of every prime period `n ≥ 2`,
provided `e` itself cannot follow the corresponding loop. -/
theorem all_periods_of_graph {f : ℝ → ℝ} (hf : Continuous f) {c₁ d₁ c₂ d₂ e : ℝ}
    (hinter : uIcc c₁ d₁ ∩ uIcc c₂ d₂ ⊆ {e})
    (h22 : Cov f c₂ d₂ c₂ d₂) (h21 : Cov f c₂ d₂ c₁ d₁) (h12 : Cov f c₁ d₁ c₂ d₂)
    (hesc : ∀ k, 2 ≤ k → f^[k] e = e → ∃ i, 1 ≤ i ∧ i < k ∧ f^[i] e ∉ uIcc c₂ d₂) :
    ∀ n, 2 ≤ n → ∃ y, HasPrimePeriod f y n := by
  classical
  intro n hn
  have hn0 : n ≠ 0 := by omega
  obtain ⟨y, hy, hit⟩ := exists_loop_point hf n (by omega)
    (fun i => if i = 0 then c₁ else if i = n then c₁ else c₂)
    (fun i => if i = 0 then d₁ else if i = n then d₁ else d₂)
    (by
      intro i hi
      by_cases h0 : i = 0
      · subst h0
        have h1 : (0:ℕ) + 1 ≠ 0 := by omega
        have h2 : (0:ℕ) + 1 ≠ n := by omega
        simpa [h1, h2] using h12
      · have hne : i + 1 ≠ 0 := by omega
        have hin : i ≠ n := by omega
        by_cases h2 : i + 1 = n
        · simpa [h0, hin, hne, h2] using h21
        · simpa [h0, hin, hne, h2] using h22)
    (by simp [hn0]) (by simp [hn0])
  have h0mem : y ∈ uIcc c₁ d₁ := by simpa using hit 0 (by omega)
  refine ⟨y, hpp_of_dvd (by omega) hy ?_⟩
  intro p hp hpn hfp
  have hp0 : p ≠ 0 := by
    rintro rfl
    exact hn0 (Nat.eq_zero_of_zero_dvd hp)
  have hpne : p ≠ n := by omega
  have hpI : f^[p] y ∈ uIcc c₂ d₂ := by simpa [hp0, hpne] using hit p hpn
  have hye : y = e := hinter ⟨h0mem, hfp ▸ hpI⟩
  subst hye
  obtain ⟨i, hi1, hi2, hi3⟩ := hesc n hn hy
  have hi0 : i ≠ 0 := by omega
  have hin : i ≠ n := by omega
  exact hi3 (by simpa [hi0, hin] using hit i hi2)

/-! ## Part 4: the distinguished interval of a periodic orbit -/

/-- A discrete intermediate value theorem on a finite set of reals: between a point where
`Q` fails and a point where `Q` holds there is a *consecutive* pair of the finite set
across which `Q` switches. -/
theorem discrete_ivt (P : Finset ℝ) (Q : ℝ → Prop) [DecidablePred Q] {u w : ℝ}
    (hu : u ∈ P) (hw : w ∈ P) (huw : u < w) (hQu : ¬ Q u) (hQw : Q w) :
    ∃ c d : ℝ, c ∈ P ∧ d ∈ P ∧ u ≤ c ∧ c < d ∧ d ≤ w ∧ ¬ Q c ∧ Q d ∧
      ∀ y ∈ P, ¬ (c < y ∧ y < d) := by
  classical
  have hDne : (P.filter (fun y => u < y ∧ Q y)).Nonempty :=
    ⟨w, Finset.mem_filter.2 ⟨hw, huw, hQw⟩⟩
  obtain ⟨hdP, hud, hQd⟩ := Finset.mem_filter.1
    ((P.filter (fun y => u < y ∧ Q y)).min'_mem hDne)
  set d := (P.filter (fun y => u < y ∧ Q y)).min' hDne with hddef
  have hdw : d ≤ w := Finset.min'_le _ _ (Finset.mem_filter.2 ⟨hw, huw, hQw⟩)
  have hCne : (P.filter (fun y => y < d)).Nonempty := ⟨u, Finset.mem_filter.2 ⟨hu, hud⟩⟩
  obtain ⟨hcP, hcd⟩ := Finset.mem_filter.1 ((P.filter (fun y => y < d)).max'_mem hCne)
  set c := (P.filter (fun y => y < d)).max' hCne with hcdef
  have huc : u ≤ c := Finset.le_max' _ _ (Finset.mem_filter.2 ⟨hu, hud⟩)
  have hQc : ¬ Q c := by
    intro hQ
    rcases eq_or_lt_of_le huc with heq | hlt
    · exact hQu (heq ▸ hQ)
    · exact absurd (Finset.min'_le _ _ (Finset.mem_filter.2 ⟨hcP, hlt, hQ⟩)) (not_le.2 hcd)
  refine ⟨c, d, hcP, hdP, huc, hcd, hdw, hQc, hQd, ?_⟩
  rintro y hy ⟨h1, h2⟩
  exact absurd (Finset.le_max' _ _ (Finset.mem_filter.2 ⟨hy, h2⟩)) (not_le.2 h1)

/-- The *distinguished interval* `[a,b]` of a periodic orbit: `a` is the largest orbit
point moved to the right, `b` its successor in the orbit.  Then `[a,b]` covers itself. -/
theorem exists_distinguished {f : ℝ → ℝ} {x : ℝ} {m : ℕ} (hx : HasPrimePeriod f x m)
    (hm : 2 ≤ m) :
    ∃ a b : ℝ, a ∈ orb f x m ∧ b ∈ orb f x m ∧ a < b ∧
      (∀ y ∈ orb f x m, ¬ (a < y ∧ y < b)) ∧ b ≤ f a ∧ f b ≤ a := by
  classical
  set P := orb f x m with hP
  have hPne : P.Nonempty := orb_nonempty (by omega)
  have hSne : (P.filter (fun y => y < f y)).Nonempty := by
    refine ⟨P.min' hPne, Finset.mem_filter.2 ⟨P.min'_mem hPne, ?_⟩⟩
    have h1 : f (P.min' hPne) ∈ P := orb_maps hx (P.min'_mem hPne)
    have h2 : P.min' hPne ≤ f (P.min' hPne) := Finset.min'_le _ _ h1
    exact lt_of_le_of_ne h2 (Ne.symm (orb_no_fix hx hm (P.min'_mem hPne)))
  obtain ⟨haP, hafa⟩ := Finset.mem_filter.1 ((P.filter (fun y => y < f y)).max'_mem hSne)
  set a := (P.filter (fun y => y < f y)).max' hSne with hadef
  have hamax : ∀ y ∈ P, y < f y → y ≤ a :=
    fun y hy h => Finset.le_max' _ _ (Finset.mem_filter.2 ⟨hy, h⟩)
  have hTne : (P.filter (fun y => a < y)).Nonempty :=
    ⟨f a, Finset.mem_filter.2 ⟨orb_maps hx haP, hafa⟩⟩
  obtain ⟨hbP, hab⟩ := Finset.mem_filter.1 ((P.filter (fun y => a < y)).min'_mem hTne)
  set b := (P.filter (fun y => a < y)).min' hTne with hbdef
  have hbmin : ∀ y ∈ P, a < y → b ≤ y :=
    fun y hy h => Finset.min'_le _ _ (Finset.mem_filter.2 ⟨hy, h⟩)
  refine ⟨a, b, haP, hbP, hab, ?_, hbmin _ (orb_maps hx haP) hafa, ?_⟩
  · rintro y hy ⟨h1, h2⟩
    exact absurd (hbmin y hy h1) (not_le.2 h2)
  · have hfbP : f b ∈ P := orb_maps hx hbP
    have hnb : ¬ (b < f b) := fun h => absurd (hamax b hbP h) (not_le.2 hab)
    have hlt : f b < b := lt_of_le_of_ne (not_lt.1 hnb) (orb_no_fix hx hm hbP)
    by_contra hcon
    exact absurd (hbmin _ hfbP (not_le.1 hcon)) (not_le.2 hlt)

/-- The distinguished interval contains a fixed point in its interior. -/
theorem exists_fixed_between {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a < b)
    (hfa : b ≤ f a) (hfb : f b ≤ a) : ∃ z, a < z ∧ z < b ∧ f z = z := by
  have hcont : Continuous (fun t : ℝ => f t - t) := hf.sub continuous_id
  have h0 : (0:ℝ) ∈ uIcc (f a - a) (f b - b) := by
    rw [mem_uIcc]; right; constructor <;> linarith
  obtain ⟨z, hz, hz0⟩ := intermediate_value_uIcc (f := fun t : ℝ => f t - t) hcont.continuousOn h0
  rw [uIcc_of_le hab.le] at hz
  have hz0' : f z - z = 0 := hz0
  refine ⟨z, lt_of_le_of_ne hz.1 ?_, lt_of_le_of_ne hz.2 ?_, by linarith⟩
  · rintro rfl; linarith
  · rintro rfl; linarith

theorem orb_inj {f : ℝ → ℝ} {x : ℝ} {m : ℕ} (hx : HasPrimePeriod f x m) (hm : 1 ≤ m)
    {y y' : ℝ} (hy : y ∈ orb f x m) (hy' : y' ∈ orb f x m) (h : f y = f y') : y = y' := by
  have key : ∀ w ∈ orb f x m, f^[m - 1] (f w) = w := by
    intro w hw
    have hp := (orb_hpp hx hw).2.1
    rw [show m = m - 1 + 1 by omega, Function.iterate_succ_apply] at hp
    exact hp
  rw [← key y hy, ← key y' hy', h]

/-- **Where oddness enters.**  For an orbit of odd prime period there is a consecutive pair
`c < d` of orbit points, *different from the distinguished pair*, across which `f` jumps
over the fixed point `z`. -/
theorem exists_switch {f : ℝ → ℝ} {x : ℝ} {m : ℕ} (hx : HasPrimePeriod f x m) (hm : 3 ≤ m)
    (hodd : Odd m) {a b z : ℝ} (ha : a ∈ orb f x m) (hb : b ∈ orb f x m) (hab : a < b)
    (hgap : ∀ y ∈ orb f x m, ¬ (a < y ∧ y < b))
    (hfa : b ≤ f a) (hfb : f b ≤ a) (haz : a < z) (hzb : z < b) (hfz : f z = z) :
    ∃ c d : ℝ, c ∈ orb f x m ∧ d ∈ orb f x m ∧ c < d ∧
      (∀ y ∈ orb f x m, ¬ (c < y ∧ y < d)) ∧ f c < z ∧ z < f d ∧ (d ≤ a ∨ b ≤ c) := by
  classical
  set P := orb f x m with hPdef
  have hzP : z ∉ P := fun h => orb_no_fix hx (by omega) h hfz
  have hne : ∀ y ∈ P, y ≠ z := fun y hy h => hzP (h ▸ hy)
  have hsplit : ∀ y ∈ P, y ≤ a ∨ b ≤ y := by
    intro y hy
    by_contra hcon
    push_neg at hcon
    exact hgap y hy ⟨hcon.1, hcon.2⟩
  have hQa : z < f a := lt_of_lt_of_le hzb hfa
  have hQb : ¬ (z < f b) := not_lt.2 (le_trans hfb haz.le)
  -- either some point left of `z` maps left of `z`, or some point right of `z` maps right
  have hcase : (∃ y ∈ P, y < z ∧ f y < z) ∨ (∃ y ∈ P, z < y ∧ z < f y) := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hLR : ∀ y ∈ P.filter (fun y => y < z), f y ∈ P.filter (fun y => ¬ (y < z)) := by
      intro y hy
      obtain ⟨hyP, hyz⟩ := Finset.mem_filter.1 hy
      exact Finset.mem_filter.2 ⟨orb_maps hx hyP, not_lt.2 (h1 y hyP hyz)⟩
    have hRL : ∀ y ∈ P.filter (fun y => ¬ (y < z)), f y ∈ P.filter (fun y => y < z) := by
      intro y hy
      obtain ⟨hyP, hyz⟩ := Finset.mem_filter.1 hy
      have hzy : z < y := lt_of_le_of_ne (not_lt.1 hyz) (Ne.symm (hne y hyP))
      have := h2 y hyP hzy
      exact Finset.mem_filter.2 ⟨orb_maps hx hyP,
        lt_of_le_of_ne this (hne _ (orb_maps hx hyP))⟩
    have hinj : ∀ (s : Finset ℝ), s ⊆ P → Set.InjOn f s := by
      intro s hs y hy y' hy' h
      exact orb_inj hx (by omega) (hs hy) (hs hy') h
    have hc1 := Finset.card_le_card_of_injOn f hLR
      (hinj _ (Finset.filter_subset _ _))
    have hc2 := Finset.card_le_card_of_injOn f hRL
      (hinj _ (Finset.filter_subset _ _))
    have hsum : (P.filter (fun y => y < z)).card + (P.filter (fun y => ¬ (y < z))).card
        = P.card := Finset.card_filter_add_card_filter_not _
    rw [orb_card hx] at hsum
    have : m % 2 = 1 := Nat.odd_iff.1 hodd
    omega
  rcases hcase with ⟨y₀, hy₀P, hy₀z, hfy₀⟩ | ⟨y₀, hy₀P, hzy₀, hfy₀⟩
  · have hy₀a : y₀ ≤ a := by
      rcases hsplit y₀ hy₀P with h | h
      · exact h
      · linarith
    have hy₀a' : y₀ < a := lt_of_le_of_ne hy₀a (by rintro rfl; linarith)
    obtain ⟨c, d, hcP, hdP, h1, h2, h3, h4, h5, h6⟩ :=
      discrete_ivt P (fun y => z < f y) hy₀P ha hy₀a' (not_lt.2 hfy₀.le) hQa
    exact ⟨c, d, hcP, hdP, h2, h6,
      lt_of_le_of_ne (not_lt.1 h4) (hne _ (orb_maps hx hcP)), h5, Or.inl h3⟩
  · have hby₀ : b ≤ y₀ := by
      rcases hsplit y₀ hy₀P with h | h
      · linarith
      · exact h
    have hby₀' : b < y₀ := lt_of_le_of_ne hby₀ (by rintro rfl; exact hQb hfy₀)
    obtain ⟨c, d, hcP, hdP, h1, h2, h3, h4, h5, h6⟩ :=
      discrete_ivt P (fun y => z < f y) hb hy₀P hby₀' hQb hfy₀
    exact ⟨c, d, hcP, hdP, h2, h6,
      lt_of_le_of_ne (not_lt.1 h4) (hne _ (orb_maps hx hcP)), h5, Or.inr h1⟩

/-! ## Part 5: Du's case analysis -/

/-- The configuration extracted from an orbit of odd prime period `m ≥ 3`, normalised so
that the switching pair `c < d` lies to the *left* of the distinguished pair `a < b`. -/
structure Data (f : ℝ → ℝ) (x : ℝ) (m : ℕ) (a b z c d : ℝ) : Prop where
  hf : Continuous f
  hx : HasPrimePeriod f x m
  hm : 3 ≤ m
  ha : a ∈ orb f x m
  hb : b ∈ orb f x m
  hab : a < b
  hgap : ∀ y ∈ orb f x m, ¬ (a < y ∧ y < b)
  hfa : b ≤ f a
  hfb : f b ≤ a
  haz : a < z
  hzb : z < b
  hfz : f z = z
  hc : c ∈ orb f x m
  hd : d ∈ orb f x m
  hcd : c < d
  hgap2 : ∀ y ∈ orb f x m, ¬ (c < y ∧ y < d)
  hda : d ≤ a
  hfc : f c < z
  hfd : z < f d

namespace Data

variable {f : ℝ → ℝ} {x : ℝ} {m : ℕ} {a b z c d : ℝ}

theorem split (D : Data f x m a b z c d) {y : ℝ} (hy : y ∈ orb f x m) : y ≤ a ∨ b ≤ y := by
  by_contra hcon; push_neg at hcon; exact D.hgap y hy ⟨hcon.1, hcon.2⟩

theorem split2 (D : Data f x m a b z c d) {y : ℝ} (hy : y ∈ orb f x m) : y ≤ c ∨ d ≤ y := by
  by_contra hcon; push_neg at hcon; exact D.hgap2 y hy ⟨hcon.1, hcon.2⟩

theorem fc_le (D : Data f x m a b z c d) : f c ≤ a := by
  rcases D.split (orb_maps D.hx D.hc) with h | h
  · exact h
  · linarith [D.hfc, D.hzb]

theorem fd_ge (D : Data f x m a b z c d) : b ≤ f d := by
  rcases D.split (orb_maps D.hx D.hd) with h | h
  · linarith [D.hfd, D.haz]
  · exact h

theorem cov_ab (D : Data f x m a b z c d) : Cov f a b a b :=
  cov_of_mem D.hf (mem_uIcc.2 (Or.inr ⟨D.hfb, le_trans D.hab.le D.hfa⟩))
    (mem_uIcc.2 (Or.inr ⟨le_trans D.hfb D.hab.le, D.hfa⟩))

theorem cov_cd_ab (D : Data f x m a b z c d) : Cov f c d a b :=
  cov_of_mem D.hf (mem_uIcc.2 (Or.inl ⟨D.fc_le, le_trans D.hab.le D.fd_ge⟩))
    (mem_uIcc.2 (Or.inl ⟨le_trans D.fc_le D.hab.le, D.fd_ge⟩))

/-- Three consecutive points of the orbit cannot all lie in `[a,b]`. -/
theorem three_in_gap (D : Data f x m a b z c d) {Y : ℝ} (hY : Y ∈ orb f x m)
    (h0 : Y ∈ uIcc a b) (h1 : f Y ∈ uIcc a b) (h2 : f^[2] Y ∈ uIcc a b) : False := by
  have hm3 : 3 ≤ m := D.hm
  have hper : HasPrimePeriod f Y m := orb_hpp D.hx hY
  have pin : ∀ w : ℝ, w ∈ orb f x m → w ∈ uIcc a b → w = a ∨ w = b := by
    intro w hw hwI
    rw [uIcc_of_le D.hab.le, mem_Icc] at hwI
    rcases D.split hw with h | h
    · exact Or.inl (le_antisymm h hwI.1)
    · exact Or.inr (le_antisymm hwI.2 h)
  have e0 := pin Y hY h0
  have e1 := pin (f Y) (orb_maps D.hx hY) h1
  have e2 := pin (f^[2] Y) (orb_iterate D.hx hY 2) h2
  have d01 : Y ≠ f Y := by
    intro h
    exact absurd (iterate_inj hper (by omega : 0 < m) (by omega : 1 < m) (by simpa using h))
      (by omega)
  have d02 : Y ≠ f^[2] Y := by
    intro h
    exact absurd (iterate_inj hper (by omega : 0 < m) (by omega : 2 < m) (by simpa using h))
      (by omega)
  have d12 : f Y ≠ f^[2] Y := by
    intro h
    have : f^[1] Y = f^[2] Y := by simpa using h
    exact absurd (iterate_inj hper (by omega : 1 < m) (by omega : 2 < m) this) (by omega)
  have hne : a ≠ b := ne_of_lt D.hab
  rcases e0 with rfl | rfl <;> rcases e1 with h1' | h1' <;> rcases e2 with h2' | h2' <;>
    simp_all

/-- The first time the orbit of `a` lands at or below `c`. -/
theorem exists_q (D : Data f x m a b z c d) :
    ∃ q : ℕ, 2 ≤ q ∧ q ≤ m - 1 ∧ f^[q] a ≤ c ∧ ∀ i, 1 ≤ i → i < q → d ≤ f^[i] a := by
  classical
  have hex : ∃ i : ℕ, 0 < i ∧ f^[i] a ≤ c := by
    obtain ⟨k, hk0, hkm, hka⟩ := orb_reach D.hx D.ha D.hc
    exact ⟨k, hk0, le_of_eq hka⟩
  obtain ⟨hq0, hqc⟩ := Nat.find_spec hex
  have hqmin : ∀ i, i < Nat.find hex → ¬ (0 < i ∧ f^[i] a ≤ c) := fun i hi => Nat.find_min hex hi
  have hpa : HasPrimePeriod f a m := orb_hpp D.hx D.ha
  have hq2 : 2 ≤ Nat.find hex := by
    rcases Nat.lt_or_ge (Nat.find hex) 2 with h | h
    · exfalso
      have : Nat.find hex = 1 := by omega
      rw [this] at hqc
      simp only [Function.iterate_one] at hqc
      linarith [D.hfa, D.hab, D.hda, D.hcd]
    · exact h
  have hqm : Nat.find hex ≤ m - 1 := by
    obtain ⟨k, hk0, hkm, hka⟩ := orb_reach D.hx D.ha D.hc
    have h1 : Nat.find hex ≤ k := Nat.find_le ⟨hk0, le_of_eq hka⟩
    have h2 : Nat.find hex ≠ m := by
      intro h
      rw [h, hpa.2.1] at hqc
      linarith [D.hda, D.hcd]
    omega
  refine ⟨Nat.find hex, hq2, hqm, hqc, ?_⟩
  intro i hi1 hi2
  have := hqmin i hi2
  push_neg at this
  have hgt : c < f^[i] a := this hi1
  rcases D.split2 (orb_iterate D.hx D.ha i) with h | h
  · linarith
  · exact h

/-- **Case A.** -/
theorem caseA (D : Data f x m a b z c d) {w : ℝ} (hdw : d ≤ w) (hwa : w < a)
    (hfw : f w ≤ c) : ∀ n, 2 ≤ n → ∃ y, HasPrimePeriod f y n := by
  have hcw : c < w := lt_of_lt_of_le D.hcd hdw
  have hwz : w < z := lt_trans hwa D.haz
  have hzfd : z ≤ f d := le_trans D.hzb.le D.fd_ge
  have hfww : f w ≤ w := le_trans hfw hcw.le
  have key : ∀ p q : ℝ, p ∈ uIcc (f w) z → q ∈ uIcc (f w) z → Cov f w z p q := by
    intro p q hp hq
    exact cov_of_mem D.hf (by rw [D.hfz]; exact hp) (by rw [D.hfz]; exact hq)
  refine all_periods_of_graph (c₁ := c) (d₁ := w) (c₂ := w) (d₂ := z) (e := w)
    D.hf ?_ ?_ ?_ ?_ ?_
  · rintro y ⟨h1, h2⟩
    rw [uIcc_of_le hcw.le, mem_Icc] at h1
    rw [uIcc_of_le hwz.le, mem_Icc] at h2
    exact Set.mem_singleton_iff.2 (le_antisymm h1.2 h2.1)
  · exact key w z (mem_uIcc.2 (Or.inl ⟨hfww, hwz.le⟩))
      (mem_uIcc.2 (Or.inl ⟨le_trans hfww hwz.le, le_refl z⟩))
  · exact key c w (mem_uIcc.2 (Or.inl ⟨hfw, le_trans hcw.le hwz.le⟩))
      (mem_uIcc.2 (Or.inl ⟨hfww, hwz.le⟩))
  · have hsub : uIcc d w ⊆ uIcc c w :=
      uIcc_subset_uIcc (mem_uIcc.2 (Or.inl ⟨D.hcd.le, hdw⟩)) right_mem_uIcc
    have h2 : Cov f d w w z :=
      cov_of_mem D.hf
        (mem_uIcc.2 (Or.inr ⟨hfww, le_trans hwz.le hzfd⟩))
        (mem_uIcc.2 (Or.inr ⟨le_trans hfww hwz.le, hzfd⟩))
    exact fun y hy => Set.image_mono hsub (h2 hy)
  · intro k hk _
    refine ⟨1, le_refl 1, by omega, ?_⟩
    rw [Function.iterate_one, uIcc_of_le hwz.le, mem_Icc]
    push_neg
    intro hcon
    linarith

/-- **Case B.** -/
theorem caseB (D : Data f x m a b z c d) (hfbc : f b ≤ c) :
    ∀ n, 2 ≤ n → ∃ y, HasPrimePeriod f y n := by
  have hca : c ≤ a := le_trans D.hcd.le D.hda
  have hafa : a ≤ f a := le_trans D.hab.le D.hfa
  refine all_periods_of_graph (c₁ := c) (d₁ := d) (c₂ := a) (d₂ := b) (e := a)
    D.hf ?_ D.cov_ab ?_ D.cov_cd_ab ?_
  · rintro y ⟨h1, h2⟩
    rw [uIcc_of_le D.hcd.le, mem_Icc] at h1
    rw [uIcc_of_le D.hab.le, mem_Icc] at h2
    exact Set.mem_singleton_iff.2 (le_antisymm (le_trans h1.2 D.hda) h2.1)
  · exact cov_of_mem D.hf (mem_uIcc.2 (Or.inr ⟨hfbc, le_trans hca hafa⟩))
      (mem_uIcc.2 (Or.inr ⟨le_trans hfbc D.hcd.le, le_trans D.hda hafa⟩))
  · intro k hk hfix
    by_contra hcon
    push_neg at hcon
    have hpa : HasPrimePeriod f a m := orb_hpp D.hx D.ha
    have hper : Function.IsPeriodicPt f k a := hfix
    have hdvd : Function.minimalPeriod f a ∣ k := hper.minimalPeriod_dvd
    rw [hpp_minimalPeriod hpa] at hdvd
    have hmk : m ≤ k := Nat.le_of_dvd (by omega) hdvd
    have hm3 : 3 ≤ m := D.hm
    refine D.three_in_gap D.ha left_mem_uIcc ?_ ?_
    · simpa using hcon 1 (by omega) (by omega)
    · exact hcon 2 (by omega) (by omega)

/-- **Case C1.** -/
theorem caseC1 (D : Data f x m a b z c d) {v w : ℝ} (hbv : b ≤ v) (hvw : v < w)
    (hwfv : w ≤ f v) (hfwc : f w ≤ c) : ∀ n, 2 ≤ n → ∃ y, HasPrimePeriod f y n := by
  have hzv : z < v := lt_of_lt_of_le D.hzb hbv
  have hvfv : v ≤ f v := le_trans hvw.le hwfv
  have hfwz : f w ≤ z := le_trans hfwc (le_trans D.hcd.le (le_trans D.hda D.haz.le))
  have key : ∀ p q : ℝ, p ∈ uIcc z (f v) → q ∈ uIcc z (f v) → Cov f z v p q := by
    intro p q hp hq
    exact cov_of_mem D.hf (by rw [D.hfz]; exact hp) (by rw [D.hfz]; exact hq)
  have key2 : ∀ p q : ℝ, p ∈ uIcc (f v) (f w) → q ∈ uIcc (f v) (f w) → Cov f v w p q :=
    fun p q hp hq => cov_of_mem D.hf hp hq
  refine all_periods_of_graph (c₁ := v) (d₁ := w) (c₂ := z) (d₂ := v) (e := v)
    D.hf ?_ ?_ ?_ ?_ ?_
  · rintro y ⟨h1, h2⟩
    rw [uIcc_of_le hvw.le, mem_Icc] at h1
    rw [uIcc_of_le hzv.le, mem_Icc] at h2
    exact Set.mem_singleton_iff.2 (le_antisymm h2.2 h1.1)
  · exact key z v (mem_uIcc.2 (Or.inl ⟨le_refl z, le_trans hzv.le hvfv⟩))
      (mem_uIcc.2 (Or.inl ⟨hzv.le, hvfv⟩))
  · exact key v w (mem_uIcc.2 (Or.inl ⟨hzv.le, hvfv⟩))
      (mem_uIcc.2 (Or.inl ⟨le_trans hzv.le hvw.le, hwfv⟩))
  · exact key2 z v (mem_uIcc.2 (Or.inr ⟨hfwz, le_trans hzv.le hvfv⟩))
      (mem_uIcc.2 (Or.inr ⟨le_trans hfwz hzv.le, hvfv⟩))
  · intro k hk _
    refine ⟨1, le_refl 1, by omega, ?_⟩
    rw [Function.iterate_one, uIcc_of_le hzv.le, mem_Icc]
    push_neg
    intro _
    linarith

/-- The four auxiliary points of case C2. -/
theorem caseC2_points (D : Data f x m a b z c d) {v w : ℝ} (hdv : d ≤ v) (hva : v ≤ a)
    (hbw : b < w) (hwfv : w ≤ f v) (hfwc : f w ≤ c) :
    ∃ u V W : ℝ, u < V ∧ V < z ∧ z < W ∧
      f u = z ∧ f V = W ∧ f W = u := by
  have hud : ∃ u ∈ uIcc c d, f u = z := by
    have : z ∈ f '' uIcc c d :=
      D.cov_cd_ab (mem_uIcc.2 (Or.inl ⟨D.haz.le, D.hzb.le⟩))
    obtain ⟨u, hu, hfu⟩ := this
    exact ⟨u, hu, hfu⟩
  obtain ⟨u, huI, hfu⟩ := hud
  rw [uIcc_of_le D.hcd.le, mem_Icc] at huI
  have huz : u < z := lt_of_le_of_lt (le_trans huI.2 D.hda) D.haz
  have hzw : z < w := lt_trans D.hzb hbw
  have hWex : ∃ W ∈ uIcc z w, f W = u := by
    have hcov : Cov f z w u u := by
      refine cov_of_mem D.hf ?_ ?_ <;>
        · rw [D.hfz]
          exact mem_uIcc.2 (Or.inr ⟨le_trans hfwc huI.1, huz.le⟩)
    obtain ⟨W, hW, hfW⟩ := hcov left_mem_uIcc
    exact ⟨W, hW, hfW⟩
  obtain ⟨W, hWI, hfW⟩ := hWex
  rw [uIcc_of_le hzw.le, mem_Icc] at hWI
  have hzW : z < W := by
    rcases eq_or_lt_of_le hWI.1 with heq | hlt
    · exfalso; rw [← heq, D.hfz] at hfW; linarith
    · exact hlt
  have hvz : v < z := lt_of_le_of_lt hva D.haz
  have hVex : ∃ V ∈ uIcc v z, f V = W := by
    have hcov : Cov f v z W W :=
      cov_of_mem D.hf
        (by rw [D.hfz]; exact mem_uIcc.2 (Or.inr ⟨hzW.le, le_trans hWI.2 hwfv⟩))
        (by rw [D.hfz]; exact mem_uIcc.2 (Or.inr ⟨hzW.le, le_trans hWI.2 hwfv⟩))
    obtain ⟨V, hV, hfV⟩ := hcov left_mem_uIcc
    exact ⟨V, hV, hfV⟩
  obtain ⟨V, hVI, hfV⟩ := hVex
  rw [uIcc_of_le hvz.le, mem_Icc] at hVI
  have hVz : V < z := by
    rcases eq_or_lt_of_le hVI.2 with heq | hlt
    · exfalso; rw [heq, D.hfz] at hfV; linarith
    · exact hlt
  have huV : u < V := by
    have hle : u ≤ V := le_trans huI.2 (le_trans hdv hVI.1)
    rcases eq_or_lt_of_le hle with heq | hlt
    · exfalso; rw [← heq, hfu] at hfV; linarith
    · exact hlt
  exact ⟨u, V, W, huV, hVz, hzW, hfu, hfV, hfW⟩

end Data

/-- The three-interval configuration `u < V < z < W` with `f u = z`, `f V = W`, `f W = u`
and `z` fixed produces a point of prime period `n` for **every even** `n ≥ 2`. -/
theorem even_periods_of_config {f : ℝ → ℝ} (hf : Continuous f) {u V z W : ℝ}
    (huV : u < V) (hVz : V < z) (hzW : z < W)
    (hfz : f z = z) (hfu : f u = z) (hfV : f V = W) (hfW : f W = u) :
    ∀ n, 2 ≤ n → n % 2 = 0 → ∃ y, HasPrimePeriod f y n := by
  classical
  have huz : u < z := lt_trans huV hVz
  have cAB : Cov f u V z W := by
    refine cov_of_mem hf ?_ ?_ <;> rw [hfu, hfV]
    · exact left_mem_uIcc
    · exact right_mem_uIcc
  have cBA : Cov f z W u V := by
    refine cov_of_mem hf ?_ ?_ <;> rw [hfz, hfW]
    · exact mem_uIcc.2 (Or.inr ⟨le_refl u, huz.le⟩)
    · exact mem_uIcc.2 (Or.inr ⟨huV.le, hVz.le⟩)
  have cBC : Cov f z W V z := by
    refine cov_of_mem hf ?_ ?_ <;> rw [hfz, hfW]
    · exact mem_uIcc.2 (Or.inr ⟨huV.le, hVz.le⟩)
    · exact mem_uIcc.2 (Or.inr ⟨huz.le, le_refl z⟩)
  have cCB : Cov f V z z W := by
    refine cov_of_mem hf ?_ ?_ <;> rw [hfz, hfV]
    · exact mem_uIcc.2 (Or.inr ⟨le_refl z, hzW.le⟩)
    · exact mem_uIcc.2 (Or.inr ⟨hzW.le, le_refl W⟩)
  intro n hn hne
  have hn0 : n ≠ 0 := by omega
  obtain ⟨y, hy, hit⟩ := exists_loop_point hf n (by omega)
    (fun i => if i = 0 then u else if i = n then u else if i % 2 = 1 then z else V)
    (fun i => if i = 0 then V else if i = n then V else if i % 2 = 1 then W else z)
    (by
      intro i hi
      by_cases h0 : i = 0
      · subst h0
        have e1 : (0:ℕ) + 1 ≠ 0 := by omega
        have e2 : (0:ℕ) + 1 ≠ n := by omega
        have e3 : ((0:ℕ) + 1) % 2 = 1 := by omega
        simpa [e1, e2, e3] using cAB
      · have hin : i ≠ n := by omega
        have hi1 : i + 1 ≠ 0 := by omega
        by_cases h2 : i + 1 = n
        · have hodd : i % 2 = 1 := by omega
          simpa [h0, hin, hi1, h2, hodd] using cBA
        · by_cases hpar : i % 2 = 1
          · have hnx : (i + 1) % 2 ≠ 1 := by omega
            simpa [h0, hin, hi1, h2, hpar, hnx] using cBC
          · have hnx : (i + 1) % 2 = 1 := by omega
            simpa [h0, hin, hi1, h2, hpar, hnx] using cCB)
    (by simp [hn0]) (by simp [hn0])
  have h0mem : y ∈ uIcc u V := by simpa using hit 0 (by omega)
  rw [uIcc_of_le huV.le, mem_Icc] at h0mem
  refine ⟨y, hpp_of_dvd (by omega) hy ?_⟩
  intro p hp hpn hfp
  have hp0 : p ≠ 0 := by rintro rfl; exact hn0 (Nat.eq_zero_of_zero_dvd hp)
  have hpne : p ≠ n := by omega
  by_cases hpar : p % 2 = 1
  · have : f^[p] y ∈ uIcc z W := by simpa [hp0, hpne, hpar] using hit p hpn
    rw [hfp, uIcc_of_le hzW.le, mem_Icc] at this
    linarith [h0mem.2, this.1]
  · have hp2 : 2 ≤ p := by omega
    have hn4 : 4 ≤ n := by omega
    have : f^[p] y ∈ uIcc V z := by simpa [hp0, hpne, hpar] using hit p hpn
    rw [hfp, uIcc_of_le hVz.le, mem_Icc] at this
    have hyV : y = V := le_antisymm h0mem.2 this.1
    subst hyV
    have h3 : f^[3] y = z := by
      show f (f (f y)) = z
      rw [hfV, hfW, hfu]
    have : f^[n] y = z := by
      rw [show n = n - 3 + 3 by omega, Function.iterate_add_apply, h3,
        Function.iterate_fixed hfz]
    rw [hy] at this
    linarith

namespace Data

variable {f : ℝ → ℝ} {x : ℝ} {m : ℕ} {a b z c d : ℝ}

/-- **Case C2, large periods.**  The loop
`J₀ → ⋯ → J_{k-1} → J_{q-1} → [c,d] → [a,b] → ⋯ → [a,b] → J₀`. -/
theorem caseC2_big (D : Data f x m a b z c d) {q k : ℕ} {v w : ℝ}
    (hq2 : 2 ≤ q) (hqm : q ≤ m - 1) (hqc : f^[q] a ≤ c)
    (hqd : ∀ i, 1 ≤ i → i < q → d ≤ f^[i] a)
    (hw : w = f^[q - 1] a) (hk1 : 1 ≤ k) (hkq : k ≤ q - 1)
    (hkw : w ≤ f^[k] a) (hv : v = f^[k - 1] a)
    (hdv : d ≤ v) (hva : v ≤ a) (hbw : b < w) :
    ∀ n, m + 1 ≤ n → ∃ y, HasPrimePeriod f y n := by
  classical
  have hm3 : 3 ≤ m := D.hm
  have hfsucc : ∀ i : ℕ, f (f^[i] a) = f^[i + 1] a := fun i =>
    (Function.iterate_succ_apply' f i a).symm
  have hfw : f w = f^[q] a := by rw [hw, hfsucc, show q - 1 + 1 = q by omega]
  have hfwc : f w ≤ c := by rw [hfw]; exact hqc
  have hdw : d ≤ w := by rw [hw]; exact hqd _ (by omega) (by omega)
  have hda' : d ≤ a := D.hda
  have hcz : c ≤ z := le_trans D.hcd.le (le_trans D.hda D.haz.le)
  have hdz : d ≤ z := le_trans D.hda D.haz.le
  have hzw : z < w := lt_trans D.hzb hbw
  have hab' : a < b := D.hab
  have haz' : a < z := D.haz
  have hzb' : z < b := D.hzb
  have hcd' : c < d := D.hcd
  have hditer : ∀ i : ℕ, i ≤ k → d ≤ f^[i] a := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · simpa using hda'
    · exact hqd i hpos (by omega)
  intro n hn
  have hnk : k + 3 ≤ n := by omega
  have hn0 : n ≠ 0 := by omega
  obtain ⟨y, hy, hit⟩ := exists_loop_point D.hf n (by omega)
    (fun i => if i ≤ k then z else if i = k + 1 then c else if i < n then a else z)
    (fun i => if i < k then f^[i] a else if i = k then w else if i = k + 1 then d
      else if i < n then b else a)
    (by
      intro i hi
      by_cases hik : i < k
      · have e1 : i ≤ k := hik.le
        have e2 : i + 1 ≤ k := hik
        have hcov : ∀ t : ℝ, t ∈ uIcc z (f^[i + 1] a) → Cov f z (f^[i] a) z t := by
          intro t ht
          refine cov_of_mem D.hf ?_ ?_ <;> rw [D.hfz, hfsucc i]
          · exact left_mem_uIcc
          · exact ht
        by_cases hik2 : i + 1 < k
        · simpa [e1, e2, hik, hik2] using hcov (f^[i + 1] a) right_mem_uIcc
        · have e3 : i + 1 = k := by omega
          have hmem : w ∈ uIcc z (f^[i + 1] a) := by
            rw [e3]; exact mem_uIcc.2 (Or.inl ⟨hzw.le, hkw⟩)
          have e5 : ¬ (i + 1 = k + 1) := by omega
          simpa [e1, e2, hik, hik2, e3, e5] using hcov w hmem
      · by_cases hik0 : i = k
        · subst hik0
          have e1 : ¬ (i + 1 ≤ i) := by omega
          have e2 : ¬ (i + 1 < i) := by omega
          have e3 : ¬ (i + 1 = i) := by omega
          have hcov : Cov f z w c d := by
            refine cov_of_mem D.hf ?_ ?_ <;> rw [D.hfz]
            · exact mem_uIcc.2 (Or.inr ⟨hfwc, hcz⟩)
            · exact mem_uIcc.2 (Or.inr ⟨le_trans hfwc hcd'.le, hdz⟩)
          simpa [hik, e1, e2, e3] using hcov
        · by_cases hik1 : i = k + 1
          · subst hik1
            have e1 : ¬ (k + 1 ≤ k) := by omega
            have e2 : ¬ (k + 1 < k) := by omega
            have e3 : ¬ (k + 1 = k) := by omega
            have e4 : ¬ (k + 1 + 1 ≤ k) := by omega
            have e5 : ¬ (k + 1 + 1 = k + 1) := by omega
            have e6 : k + 1 + 1 < n := by omega
            have e7 : ¬ (k + 1 + 1 < k) := by omega
            have e8 : ¬ (k + 1 + 1 = k) := by omega
            simpa [e1, e2, e3, e4, e5, e6, e7, e8] using D.cov_cd_ab
          · have hige : k + 2 ≤ i := by omega
            have e1 : ¬ (i ≤ k) := by omega
            have e2 : ¬ (i = k + 1) := by omega
            have e3 : ¬ (i < k) := by omega
            have e4 : ¬ (i = k) := by omega
            have hcovz : Cov f a b z a := by
              refine cov_of_mem D.hf ?_ ?_
              · exact mem_uIcc.2 (Or.inr ⟨le_trans D.hfb haz'.le,
                  le_trans hzb'.le D.hfa⟩)
              · exact mem_uIcc.2 (Or.inr ⟨D.hfb, le_trans hab'.le D.hfa⟩)
            by_cases hlast : i + 1 = n
            · have f1 : ¬ (n ≤ k) := by omega
              have f2 : ¬ (n = k + 1) := by omega
              have f3 : ¬ (n < n) := by omega
              have f4 : ¬ (n < k) := by omega
              have f5 : ¬ (n = k) := by omega
              simpa [e1, e2, e3, e4, hi, hlast, f1, f2, f3, f4, f5] using hcovz
            · have f1 : ¬ (i + 1 ≤ k) := by omega
              have f2 : ¬ (i + 1 = k + 1) := by omega
              have f3 : i + 1 < n := by omega
              have f4 : ¬ (i + 1 < k) := by omega
              have f5 : ¬ (i + 1 = k) := by omega
              simpa [e1, e2, e3, e4, hi, f1, f2, f3, f4, f5] using D.cov_ab)
    (by
      have e1 : ¬ (n ≤ k) := by omega
      have e2 : ¬ (n = k + 1) := by omega
      have e3 : ¬ (n < n) := by omega
      simp [e1, e2, e3])
    (by
      have e1 : ¬ (n < k) := by omega
      have e2 : ¬ (n = k) := by omega
      have e3 : ¬ (n = k + 1) := by omega
      have e4 : ¬ (n < n) := by omega
      have e5 : (0:ℕ) < k := hk1
      simp [e1, e2, e3, e4, e5])
  -- read off the itinerary
  have hitL : ∀ i, i < k → f^[i] y ∈ uIcc z (f^[i] a) := by
    intro i hik
    simpa [hik.le, hik] using hit i (by omega)
  have hitK : f^[k] y ∈ uIcc z w := by simpa using hit k (by omega)
  have hitK1 : f^[k + 1] y ∈ uIcc c d := by
    have e1 : ¬ (k + 1 ≤ k) := by omega
    have e2 : ¬ (k + 1 < k) := by omega
    have e3 : ¬ (k + 1 = k) := by omega
    simpa [e1, e2, e3] using hit (k + 1) (by omega)
  have hitR : ∀ i, k + 2 ≤ i → i < n → f^[i] y ∈ uIcc a b := by
    intro i h1 h2
    have e1 : ¬ (i ≤ k) := by omega
    have e2 : ¬ (i = k + 1) := by omega
    have e3 : ¬ (i < k) := by omega
    have e4 : ¬ (i = k) := by omega
    simpa [e1, e2, e3, e4, h2] using hit i h2
  have hyd : ∀ i, i < n → i ≠ k + 1 → d ≤ f^[i] y := by
    intro i hi hik
    rcases Nat.lt_or_ge i k with h1 | h1
    · have h3 : d ≤ f^[i] a := hditer i h1.le
      rcases mem_uIcc.1 (hitL i h1) with ⟨h4, h5⟩ | ⟨h4, h5⟩ <;> linarith
    · rcases Nat.eq_or_lt_of_le h1 with h2 | h2
      · rw [← h2] at *
        rcases mem_uIcc.1 hitK with ⟨h4, h5⟩ | ⟨h4, h5⟩ <;> linarith
      · rcases mem_uIcc.1 (hitR i (by omega) hi) with ⟨h4, h5⟩ | ⟨h4, h5⟩ <;> linarith
  -- the point found is not on the orbit
  have hyP : y ∉ orb f x m := by
    intro hyPmem
    have hper : HasPrimePeriod f y m := orb_hpp D.hx hyPmem
    have hpp : Function.IsPeriodicPt f n y := hy
    have hdvd : Function.minimalPeriod f y ∣ n := hpp.minimalPeriod_dvd
    rw [hpp_minimalPeriod hper] at hdvd
    obtain ⟨t, ht⟩ := hdvd
    have ht2 : 2 ≤ t := by
      by_contra hcon
      push_neg at hcon
      interval_cases t <;> simp at ht <;> omega
    have hn2m : 2 * m ≤ n := by
      calc 2 * m = m * 2 := by ring
        _ ≤ m * t := Nat.mul_le_mul (le_refl m) ht2
        _ = n := ht.symm
    refine D.three_in_gap (Y := f^[k + 2] y) (orb_iterate D.hx hyPmem (k + 2))
      (hitR (k + 2) (by omega) (by omega)) ?_ ?_
    · have e : f (f^[k + 2] y) = f^[k + 3] y := by
        have h := (Function.iterate_add_apply f 1 (k + 2) y).symm
        rw [show 1 + (k + 2) = k + 3 by omega] at h
        simpa using h
      rw [e]; exact hitR (k + 3) (by omega) (by omega)
    · have e : f^[2] (f^[k + 2] y) = f^[k + 4] y := by
        rw [← Function.iterate_add_apply]; congr 1; omega
      rw [e]; exact hitR (k + 4) (by omega) (by omega)
  have hk1lt : f^[k + 1] y < d := by
    rcases mem_uIcc.1 hitK1 with ⟨h4, h5⟩ | ⟨h4, h5⟩
    · rcases eq_or_lt_of_le h5 with heq | hlt
      · exfalso
        apply hyP
        have hback : f^[n - (k + 1)] (f^[k + 1] y) = y := by
          rw [← Function.iterate_add_apply, show n - (k + 1) + (k + 1) = n by omega]
          exact hy
        rw [heq] at hback
        rw [← hback]
        exact orb_iterate D.hx D.hd _
      · exact hlt
    · linarith
  refine ⟨y, hpp_of_dvd (by omega) hy ?_⟩
  intro p hp hpn hfp
  have hp0 : p ≠ 0 := by rintro rfl; exact hn0 (Nat.eq_zero_of_zero_dvd hp)
  have h2p : 2 * p ≤ n := by
    obtain ⟨t, ht⟩ := hp
    have ht2 : 2 ≤ t := by
      by_contra hcon
      push_neg at hcon
      interval_cases t <;> simp at ht <;> omega
    calc 2 * p = p * 2 := by ring
      _ ≤ p * t := Nat.mul_le_mul (le_refl p) ht2
      _ = n := ht.symm
  rcases Nat.lt_or_ge (k + 1 + p) n with hcase | hcase
  · have heq : f^[k + 1 + p] y = f^[k + 1] y := by
      rw [Function.iterate_add_apply, hfp]
    have hge := hyd (k + 1 + p) hcase (by omega)
    rw [heq] at hge
    linarith
  · rcases Nat.lt_or_ge (k + 1) p with hcase2 | hcase2
    · exfalso; omega
    · have heq : f^[k + 1 - p] y = f^[k + 1] y := by
        conv_rhs => rw [show k + 1 = (k + 1 - p) + p by omega]
        rw [Function.iterate_add_apply, hfp]
      have hge := hyd (k + 1 - p) (by omega) (by omega)
      rw [heq] at hge
      linarith

/-- The first time the orbit of `a` reaches or passes `w`. -/
theorem exists_k (D : Data f x m a b z c d) {q : ℕ} (hq2 : 2 ≤ q) {w : ℝ}
    (hw : w = f^[q - 1] a) (haw : a < w) :
    ∃ k, 1 ≤ k ∧ k ≤ q - 1 ∧ w ≤ f^[k] a ∧ f^[k - 1] a < w := by
  classical
  have hex : ∃ i : ℕ, 1 ≤ i ∧ w ≤ f^[i] a := ⟨q - 1, by omega, by rw [hw]⟩
  obtain ⟨hk1, hkw⟩ := Nat.find_spec hex
  have hkq : Nat.find hex ≤ q - 1 := Nat.find_le ⟨by omega, by rw [hw]⟩
  refine ⟨Nat.find hex, hk1, hkq, hkw, ?_⟩
  rcases Nat.eq_or_lt_of_le hk1 with h1 | h1
  · rw [← h1]; simpa using haw
  · have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    push_neg at this
    exact this (by omega)

/-- **Du's Proposition 5** in the normalised case: an orbit of odd prime period `m ≥ 3`
forces all even periods and all periods `> m`. -/
theorem main (D : Data f x m a b z c d) :
    (∀ n, 2 ≤ n → n % 2 = 0 → ∃ y, HasPrimePeriod f y n) ∧
    (∀ n, m + 1 ≤ n → ∃ y, HasPrimePeriod f y n) := by
  have hm3 : 3 ≤ m := D.hm
  have hfsucc : ∀ i : ℕ, f (f^[i] a) = f^[i + 1] a := fun i =>
    (Function.iterate_succ_apply' f i a).symm
  obtain ⟨q, hq2, hqm, hqc, hqd⟩ := D.exists_q
  have hditer : ∀ i : ℕ, i ≤ q - 1 → d ≤ f^[i] a := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · simpa using D.hda
    · exact hqd i hpos (by omega)
  set w := f^[q - 1] a with hw
  have hdw : d ≤ w := hditer _ (le_refl _)
  have hfw : f w = f^[q] a := by rw [hw, hfsucc, show q - 1 + 1 = q by omega]
  have hfwc : f w ≤ c := by rw [hfw]; exact hqc
  have hwP : w ∈ orb f x m := orb_iterate D.hx D.ha _
  have hpa : HasPrimePeriod f a m := orb_hpp D.hx D.ha
  have hwa : w ≠ a := by
    intro h
    have h2 : f^[q - 1] a = f^[0] a := by simpa [hw] using h
    have := iterate_inj hpa (show q - 1 < m by omega) (show 0 < m by omega) h2
    omega
  have hall : ∀ P : Prop, ((∀ n, 2 ≤ n → ∃ y, HasPrimePeriod f y n) → P) →
      (∀ n, 2 ≤ n → ∃ y, HasPrimePeriod f y n) → P := fun _ h => h
  rcases lt_or_gt_of_ne hwa with hlt | hgt
  · have hres := D.caseA hdw hlt hfwc
    exact ⟨fun n h1 _ => hres n h1, fun n h1 => hres n (by omega)⟩
  · have hbw : b ≤ w := by
      rcases D.split hwP with h | h
      · exact absurd hgt (not_lt.2 h)
      · exact h
    rcases eq_or_lt_of_le hbw with heq | hlt2
    · have hres := D.caseB (by rw [heq]; exact hfwc)
      exact ⟨fun n h1 _ => hres n h1, fun n h1 => hres n (by omega)⟩
    · obtain ⟨k, hk1, hkq, hkw, hkv⟩ := D.exists_k hq2 hw (lt_trans D.hab hlt2)
      have hfv : f (f^[k - 1] a) = f^[k] a := by
        rw [hfsucc, show k - 1 + 1 = k by omega]
      have hdv : d ≤ f^[k - 1] a := hditer _ (by omega)
      have hvP : f^[k - 1] a ∈ orb f x m := orb_iterate D.hx D.ha _
      rcases D.split hvP with hva | hbv
      · obtain ⟨u, V, W, huV, hVz, hzW, hfu, hfV, hfW⟩ :=
          D.caseC2_points hdv hva hlt2 (by rw [hfv]; exact hkw) hfwc
        exact ⟨even_periods_of_config D.hf huV hVz hzW D.hfz hfu hfV hfW,
          D.caseC2_big hq2 hqm hqc hqd hw hk1 hkq hkw rfl hdv hva hlt2⟩
      · have hres := D.caseC1 hbv hkv (by rw [hfv]; exact hkw) hfwc
        exact ⟨fun n h1 _ => hres n h1, fun n h1 => hres n (by omega)⟩

end Data

/-! ## Part 6: the reflection `x ↦ -x`, and the odd case in general -/

/-- Conjugation of `f` by `x ↦ -x`. -/
def nf (f : ℝ → ℝ) : ℝ → ℝ := fun t => -f (-t)

theorem nf_continuous {f : ℝ → ℝ} (hf : Continuous f) : Continuous (nf f) :=
  (hf.comp continuous_neg).neg

theorem nf_nf (f : ℝ → ℝ) : nf (nf f) = f := by funext t; simp [nf]

theorem nf_apply (f : ℝ → ℝ) (t : ℝ) : nf f (-t) = -(f t) := by simp [nf]

theorem nf_iterate (f : ℝ → ℝ) (n : ℕ) (y : ℝ) : (nf f)^[n] (-y) = -(f^[n] y) := by
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, nf_apply]
      exact ih (f y)

theorem nf_hpp {f : ℝ → ℝ} {y : ℝ} {n : ℕ} (h : HasPrimePeriod f y n) :
    HasPrimePeriod (nf f) (-y) n := by
  refine ⟨h.1, ?_, ?_⟩
  · rw [nf_iterate, h.2.1]
  · intro k hk hkn hcon
    rw [nf_iterate] at hcon
    exact h.2.2 k hk hkn (neg_injective hcon)

theorem hpp_of_nf {f : ℝ → ℝ} {y : ℝ} {n : ℕ} (h : HasPrimePeriod (nf f) y n) :
    HasPrimePeriod f (-y) n := by
  have := nf_hpp h
  rwa [nf_nf] at this

theorem mem_nf_orb {f : ℝ → ℝ} {x y : ℝ} {m : ℕ} :
    y ∈ orb (nf f) (-x) m ↔ -y ∈ orb f x m := by
  constructor
  · intro h
    obtain ⟨i, hi, hfi⟩ := mem_orb.1 h
    rw [nf_iterate] at hfi
    exact mem_orb.2 ⟨i, hi, by rw [← hfi, neg_neg]⟩
  · intro h
    obtain ⟨i, hi, hfi⟩ := mem_orb.1 h
    exact mem_orb.2 ⟨i, hi, by rw [nf_iterate, hfi, neg_neg]⟩

/-- **Du's Proposition 5.**  A continuous `f : ℝ → ℝ` with a point of odd prime period
`m ≥ 3` has points of every even prime period and of every prime period `> m`. -/
theorem odd_main {f : ℝ → ℝ} (hf : Continuous f) {x : ℝ} {m : ℕ}
    (hx : HasPrimePeriod f x m) (hm : 3 ≤ m) (hodd : Odd m) :
    (∀ n, 2 ≤ n → n % 2 = 0 → ∃ y, HasPrimePeriod f y n) ∧
    (∀ n, m + 1 ≤ n → ∃ y, HasPrimePeriod f y n) := by
  obtain ⟨a, b, ha, hb, hab, hgap, hfa, hfb⟩ := exists_distinguished hx (by omega)
  obtain ⟨z, haz, hzb, hfz⟩ := exists_fixed_between hf hab hfa hfb
  obtain ⟨c, d, hc, hd, hcd, hgap2, hfc, hfd, hside⟩ :=
    exists_switch hx hm hodd ha hb hab hgap hfa hfb haz hzb hfz
  rcases hside with hda | hbc
  · exact Data.main ⟨hf, hx, hm, ha, hb, hab, hgap, hfa, hfb, haz, hzb, hfz, hc, hd, hcd,
      hgap2, hda, hfc, hfd⟩
  · have D : Data (nf f) (-x) m (-b) (-a) (-z) (-d) (-c) := by
      refine ⟨nf_continuous hf, nf_hpp hx, hm, ?_, ?_, by linarith, ?_, ?_, ?_, by linarith,
        by linarith, ?_, ?_, ?_, by linarith, ?_, by linarith, ?_, ?_⟩
      · exact mem_nf_orb.2 (by rwa [neg_neg])
      · exact mem_nf_orb.2 (by rwa [neg_neg])
      · rintro y hy ⟨h1, h2⟩
        exact hgap (-y) (mem_nf_orb.1 hy) ⟨by linarith, by linarith⟩
      · rw [nf_apply]; linarith
      · rw [nf_apply]; linarith
      · rw [nf_apply, hfz]
      · exact mem_nf_orb.2 (by rwa [neg_neg])
      · exact mem_nf_orb.2 (by rwa [neg_neg])
      · rintro y hy ⟨h1, h2⟩
        exact hgap2 (-y) (mem_nf_orb.1 hy) ⟨by linarith, by linarith⟩
      · rw [nf_apply]; linarith
      · rw [nf_apply]; linarith
    obtain ⟨h1, h2⟩ := D.main
    constructor
    · intro n hn hne
      obtain ⟨y, hy⟩ := h1 n hn hne
      exact ⟨-y, hpp_of_nf hy⟩
    · intro n hn
      obtain ⟨y, hy⟩ := h2 n hn
      exact ⟨-y, hpp_of_nf hy⟩

/-! ## Part 7: the Sarkovskii ordering -/

theorem exists_fixed {f : ℝ → ℝ} (hf : Continuous f) {x : ℝ} {m : ℕ}
    (hx : HasPrimePeriod f x m) (hm : 2 ≤ m) : ∃ y, HasPrimePeriod f y 1 := by
  obtain ⟨a, b, ha, hb, hab, hgap, hfa, hfb⟩ := exists_distinguished hx hm
  obtain ⟨z, _, _, hfz⟩ := exists_fixed_between hf hab hfa hfb
  exact ⟨z, one_pos, by simpa using hfz, fun k hk hk1 => absurd hk1 (by omega)⟩

theorem twoAdicVal_odd {n : ℕ} (h : Odd n) : Devaney.twoAdicVal n = 0 := by
  have hnd : ¬ (2 ∣ n) := by
    intro hdvd; rw [Nat.odd_iff] at h; omega
  exact padicValNat.eq_zero_of_not_dvd hnd

theorem oddPart_odd {n : ℕ} (h : Odd n) : Devaney.oddPart n = n := by
  have h0 := twoAdicVal_odd h
  unfold Devaney.twoAdicVal at h0
  unfold Devaney.oddPart
  rw [h0]; simp

theorem two_dvd_of_twoAdicVal_pos {l : ℕ} (h : 0 < Devaney.twoAdicVal l) : 2 ∣ l := by
  by_contra hcon
  have h0 := padicValNat.eq_zero_of_not_dvd (p := 2) hcon
  unfold Devaney.twoAdicVal at h
  omega

theorem odd_of_twoAdicVal_zero {l : ℕ} (hl : l ≠ 0) (h : Devaney.twoAdicVal l = 0) : Odd l := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.odd_iff]
  by_contra hcon
  have hdvd : 2 ∣ l := by omega
  have h1 := one_le_padicValNat_of_dvd hl hdvd
  unfold Devaney.twoAdicVal at h
  omega

theorem eq_pow_of_oddPart_one {l : ℕ} (hl : l ≠ 0) (h : Devaney.oddPart l = 1) :
    l = 2 ^ Devaney.twoAdicVal l := by
  have hdvd : 2 ^ padicValNat 2 l ∣ l := pow_padicValNat_dvd
  unfold Devaney.oddPart at h
  unfold Devaney.twoAdicVal
  have hc := Nat.div_mul_cancel hdvd
  rw [h, one_mul] at hc
  exact hc.symm

/-- **Sarkovskii's theorem, odd case.** -/
theorem sarkovskii_odd_thm (f : ℝ → ℝ) (hf : Continuous f) (n : ℕ) (hodd : Odd n) (hn : 1 < n)
    (h : ∃ x, HasPrimePeriod f x n) (l : ℕ) (hl : Devaney.SarkovskiiPrecedes n l) :
    ∃ x, HasPrimePeriod f x l := by
  obtain ⟨x, hx⟩ := h
  have hpar : n % 2 = 1 := Nat.odd_iff.1 hodd
  have hn3 : 3 ≤ n := by omega
  obtain ⟨heven, hbig⟩ := odd_main hf hx hn3 hodd
  have hop : Devaney.oddPart n = n := oddPart_odd hodd
  have htv : Devaney.twoAdicVal n = 0 := twoAdicVal_odd hodd
  rcases hl with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩
  · have hl0 : l ≠ 0 := by
      rintro rfl
      simp [Devaney.oddPart] at h2
    rcases h3 with hlt | ⟨heq, hlt⟩
    · have hdvd : 2 ∣ l := two_dvd_of_twoAdicVal_pos (by omega)
      exact heven l (by omega) (by omega)
    · have hlodd : Odd l := odd_of_twoAdicVal_zero hl0 (by omega)
      have hll : Devaney.oddPart l = l := oddPart_odd hlodd
      exact hbig l (by omega)
  · by_cases hl1 : l = 1
    · subst hl1
      exact exists_fixed hf hx (by omega)
    · have hl0 : l ≠ 0 := by omega
      have hlpow : l = 2 ^ Devaney.twoAdicVal l := eq_pow_of_oddPart_one hl0 h2
      have hv1 : 0 < Devaney.twoAdicVal l := by
        by_contra hcon
        have hz : Devaney.twoAdicVal l = 0 := by omega
        rw [hz, pow_zero] at hlpow
        exact hl1 hlpow
      have hdvd : 2 ∣ l := two_dvd_of_twoAdicVal_pos hv1
      exact heven l (by omega) (by omega)
  · exact absurd h1 (by omega)

/-! ## Part 8: reduction of the general case to the odd case -/

theorem gcd_eq_of_dvd {N K : ℕ} (h : K ∣ N) : Nat.gcd N K = K :=
  Nat.dvd_antisymm (Nat.gcd_dvd_right N K) (Nat.dvd_gcd h dvd_rfl)

/-- Passing to the iterate `f^[K]` when `K` divides the prime period. -/
theorem hpp_iterate_dvd {f : ℝ → ℝ} {y : ℝ} {N K : ℕ} (hK : K ≠ 0) (hdvd : K ∣ N)
    (h : HasPrimePeriod f y N) : HasPrimePeriod (f^[K]) y (N / K) := by
  have hN : 0 < N := h.1
  have hmp : Function.minimalPeriod f y = N := hpp_minimalPeriod h
  have hdiv := Function.minimalPeriod_iterate_eq_div_gcd (f := f) (x := y) (n := K) hK
  rw [hmp, gcd_eq_of_dvd hdvd] at hdiv
  exact hpp_of_minimalPeriod
    (Nat.div_pos (Nat.le_of_dvd hN hdvd) (Nat.pos_of_ne_zero hK)) hdiv

/-- Going back from `f^[2^M]` to `f` when the period found upstairs is even. -/
theorem hpp_of_iterate_even {f : ℝ → ℝ} {y : ℝ} {M j : ℕ} (hj2 : 2 ∣ j)
    (h : HasPrimePeriod (f^[2 ^ M]) y j) : HasPrimePeriod f y (2 ^ M * j) := by
  have hj0 : 0 < j := h.1
  have hK : (2:ℕ) ^ M ≠ 0 := by positivity
  have hper : Function.IsPeriodicPt f (2 ^ M * j) y := by
    have h1 : Function.IsPeriodicPt (f^[2 ^ M]) j y := h.2.1
    have h2 : (f^[2 ^ M])^[j] y = y := h1
    rw [← Function.iterate_mul] at h2
    exact h2
  have hmem : y ∈ Function.periodicPts f := ⟨2 ^ M * j, by positivity, hper⟩
  have hdiv : j = Function.minimalPeriod f y / Nat.gcd (Function.minimalPeriod f y) (2 ^ M) :=
    (hpp_minimalPeriod h).symm.trans (Function.minimalPeriod_iterate_eq_div_gcd hK)
  have hgN : Nat.gcd (Function.minimalPeriod f y) (2 ^ M) ∣ Function.minimalPeriod f y :=
    Nat.gcd_dvd_left _ _
  have hg2 : Nat.gcd (Function.minimalPeriod f y) (2 ^ M) ∣ 2 ^ M := Nat.gcd_dvd_right _ _
  obtain ⟨e, hle, hge⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hg2
  have hNgj : Function.minimalPeriod f y = Nat.gcd (Function.minimalPeriod f y) (2 ^ M) * j := by
    rw [hdiv]; exact (Nat.mul_div_cancel' hgN).symm
  have heM : e = M := by
    by_contra hne
    have helt : e < M := by omega
    obtain ⟨t, ht⟩ := hj2
    have h1 : (2:ℕ) ^ (e + 1) ∣ Function.minimalPeriod f y := by
      refine ⟨t, ?_⟩
      rw [hNgj, hge, ht, pow_succ]; ring
    have h2 : (2:ℕ) ^ (e + 1) ∣ 2 ^ M := pow_dvd_pow 2 (by omega)
    have h3 := Nat.dvd_gcd h1 h2
    rw [hge] at h3
    have h4 := Nat.le_of_dvd (by positivity) h3
    have h5 : (2:ℕ) ^ e < 2 ^ (e + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  refine hpp_of_minimalPeriod (by positivity) ?_
  rw [hNgj, hge, heM]

theorem eq_pow_mul_oddPart {l : ℕ} (hl : l ≠ 0) :
    l = 2 ^ Devaney.twoAdicVal l * Devaney.oddPart l := by
  unfold Devaney.twoAdicVal Devaney.oddPart
  exact (Nat.mul_div_cancel' pow_padicValNat_dvd).symm

theorem oddPart_is_odd {l : ℕ} (hl : l ≠ 0) : Odd (Devaney.oddPart l) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.odd_iff]
  by_contra hcon
  have h2 : 2 ∣ Devaney.oddPart l := by omega
  obtain ⟨t, ht⟩ := h2
  have hl2 : 2 ^ (Devaney.twoAdicVal l + 1) ∣ l := by
    refine ⟨t, ?_⟩
    conv_lhs => rw [eq_pow_mul_oddPart hl]
    rw [ht, pow_succ]; ring
  rw [padicValNat_dvd_iff_le hl] at hl2
  unfold Devaney.twoAdicVal at hl2
  omega

theorem twoAdicVal_mul_pow {p M : ℕ} (hp : Odd p) :
    Devaney.twoAdicVal (p * 2 ^ M) = M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp0 : p ≠ 0 := by rintro rfl; simp at hp
  have hnd : ¬ (2 ∣ p) := by intro hdvd; rw [Nat.odd_iff] at hp; omega
  unfold Devaney.twoAdicVal
  rw [padicValNat.mul hp0 (by positivity), padicValNat.eq_zero_of_not_dvd hnd,
    padicValNat.prime_pow, zero_add]

theorem oddPart_mul_pow {p M : ℕ} (hp : Odd p) : Devaney.oddPart (p * 2 ^ M) = p := by
  have h := twoAdicVal_mul_pow (p := p) (M := M) hp
  unfold Devaney.twoAdicVal at h
  unfold Devaney.oddPart
  rw [h]
  exact Nat.mul_div_cancel _ (by positivity)

end Shk

namespace Shk

/-! ## Part 9: the general case -/

/-- `p * 2^M` with `p` odd and `> 1` is never a power of two. -/
theorem not_pow_two {p M : ℕ} (hp : Odd p) (hp1 : 1 < p) : ∀ m : ℕ, p * 2 ^ M ≠ 2 ^ m := by
  intro m hm
  have hdvd : p ∣ 2 ^ m := ⟨2 ^ M, hm.symm⟩
  obtain ⟨e, hle, hpe⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have he : e ≠ 0 := by rintro rfl; rw [pow_zero] at hpe; omega
  have h2 : 2 ∣ p := by rw [hpe]; exact dvd_pow_self 2 he
  rw [Nat.odd_iff] at hp; omega

/-- **Sarkovskii's theorem** for a period with odd part `> 1`. -/
theorem sarkovskii_general (f : ℝ → ℝ) (hf : Continuous f) (p M : ℕ) (hp : Odd p)
    (hp1 : 1 < p) (h : ∃ x, HasPrimePeriod f x (p * 2 ^ M)) (l : ℕ)
    (hl : Devaney.SarkovskiiPrecedes (p * 2 ^ M) l) :
    ∃ x, HasPrimePeriod f x l := by
  obtain ⟨x, hx⟩ := h
  have hpodd := Nat.odd_iff.1 hp
  have hp3 : 3 ≤ p := by omega
  rcases Nat.eq_zero_or_pos M with rfl | hM1
  · simp only [pow_zero, mul_one] at hx hl ⊢
    exact sarkovskii_odd_thm f hf p hp hp1 ⟨x, hx⟩ l hl
  have hkbig : 2 ≤ p * 2 ^ M := by
    calc (2:ℕ) ≤ p := by omega
      _ ≤ p * 2 ^ M := Nat.le_mul_of_pos_right p (by positivity)
  have htv : Devaney.twoAdicVal (p * 2 ^ M) = M := twoAdicVal_mul_pow hp
  have hop : Devaney.oddPart (p * 2 ^ M) = p := oddPart_mul_pow hp
  have hdvdM : (2:ℕ) ^ M ∣ p * 2 ^ M := ⟨p, by ring⟩
  have hgp : HasPrimePeriod (f^[2 ^ M]) x p := by
    have h1 := hpp_iterate_dvd (K := 2 ^ M) (by positivity) hdvdM hx
    rwa [Nat.mul_div_cancel _ (show 0 < 2 ^ M by positivity)] at h1
  obtain ⟨geven, gbig⟩ := odd_main (hf.iterate _) hgp hp3 hp
  rcases hl with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩
  · have hl0 : l ≠ 0 := by rintro rfl; simp [Devaney.oddPart] at h2
    rw [htv, hop] at h3
    have hlq := eq_pow_mul_oddPart hl0
    have hqpos : 0 < Devaney.oddPart l := by omega
    rcases h3 with hlt | ⟨heq, hlt⟩
    · have hjdef : l = 2 ^ M * (2 ^ (Devaney.twoAdicVal l - M) * Devaney.oddPart l) := by
        rw [← mul_assoc, ← pow_add,
          show M + (Devaney.twoAdicVal l - M) = Devaney.twoAdicVal l by omega]
        exact hlq
      have hjeven : 2 ∣ 2 ^ (Devaney.twoAdicVal l - M) * Devaney.oddPart l :=
        Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
      have hjpos : 0 < 2 ^ (Devaney.twoAdicVal l - M) * Devaney.oddPart l := by positivity
      obtain ⟨y, hy⟩ := geven (2 ^ (Devaney.twoAdicVal l - M) * Devaney.oddPart l)
        (by omega) (by omega)
      exact ⟨y, by rw [hjdef]; exact hpp_of_iterate_even hjeven hy⟩
    · have hqodd : Odd (Devaney.oddPart l) := oddPart_is_odd hl0
      have hq3 : 3 ≤ Devaney.oddPart l := by omega
      have hlqM : l = 2 ^ M * Devaney.oddPart l := by rw [heq]; exact hlq
      have hpw : (2:ℕ) ^ M = 2 ^ (M - 1) * 2 := by rw [← pow_succ]; congr 1; omega
      have hMM : p * 2 ^ M = 2 * p * 2 ^ (M - 1) := by rw [hpw]; ring
      have hdvd1 : (2:ℕ) ^ (M - 1) ∣ p * 2 ^ M := ⟨2 * p, by rw [hMM]; ring⟩
      have hx1 : HasPrimePeriod (f^[2 ^ (M - 1)]) x (2 * p) := by
        have h5 := hpp_iterate_dvd (K := 2 ^ (M - 1)) (by positivity) hdvd1 hx
        rwa [hMM, Nat.mul_div_cancel _ (show 0 < 2 ^ (M - 1) by positivity)] at h5
      have hx2 : HasPrimePeriod ((f^[2 ^ (M - 1)])^[2]) x p := by
        have h5 := hpp_iterate_dvd (K := 2) (by norm_num) ⟨p, rfl⟩ hx1
        rwa [show 2 * p / 2 = p by omega] at h5
      obtain ⟨_, hbig2⟩ := odd_main ((hf.iterate _).iterate 2) hx2 hp3 hp
      obtain ⟨y, hy⟩ := hbig2 (Devaney.oddPart l) (by omega)
      have h2q : ∃ y', HasPrimePeriod (f^[2 ^ (M - 1)]) y' (2 * Devaney.oddPart l) := by
        have hd := Function.minimalPeriod_iterate_eq_div_gcd
          (f := f^[2 ^ (M - 1)]) (x := y) (n := 2) (by norm_num)
        rw [hpp_minimalPeriod hy] at hd
        have hgd : Nat.gcd (Function.minimalPeriod (f^[2 ^ (M - 1)]) y) 2 ∣ 2 :=
          Nat.gcd_dvd_right _ _
        have hgN : Nat.gcd (Function.minimalPeriod (f^[2 ^ (M - 1)]) y) 2 ∣
            Function.minimalPeriod (f^[2 ^ (M - 1)]) y := Nat.gcd_dvd_left _ _
        have hNq : Function.minimalPeriod (f^[2 ^ (M - 1)]) y =
            Nat.gcd (Function.minimalPeriod (f^[2 ^ (M - 1)]) y) 2 * Devaney.oddPart l := by
          rw [hd]; exact (Nat.mul_div_cancel' hgN).symm
        rcases (Nat.dvd_prime Nat.prime_two).1 hgd with hc | hc
        · rw [hc, one_mul] at hNq
          have hpq : HasPrimePeriod (f^[2 ^ (M - 1)]) y (Devaney.oddPart l) :=
            hpp_of_minimalPeriod (by omega) hNq
          obtain ⟨heven3, _⟩ := odd_main (hf.iterate _) hpq hq3 hqodd
          exact heven3 (2 * Devaney.oddPart l) (by omega) (by omega)
        · rw [hc] at hNq
          exact ⟨y, hpp_of_minimalPeriod (by omega) hNq⟩
      obtain ⟨y', hy'⟩ := h2q
      refine ⟨y', ?_⟩
      have hres := hpp_of_iterate_even (M := M - 1) (j := 2 * Devaney.oddPart l)
        ⟨Devaney.oddPart l, rfl⟩ hy'
      have hfin : 2 ^ (M - 1) * (2 * Devaney.oddPart l) = l := by
        calc 2 ^ (M - 1) * (2 * Devaney.oddPart l)
            = 2 ^ (M - 1) * 2 * Devaney.oddPart l := by ring
          _ = 2 ^ M * Devaney.oddPart l := by rw [hpw]
          _ = l := hlqM.symm
      rwa [hfin] at hres
  · by_cases hl1 : l = 1
    · subst hl1
      exact exists_fixed hf hx hkbig
    · have hl0 : l ≠ 0 := by omega
      have hlpow : l = 2 ^ Devaney.twoAdicVal l := eq_pow_of_oddPart_one hl0 h2
      have hv1 : 1 ≤ Devaney.twoAdicVal l := by
        by_contra hcon
        have hz : Devaney.twoAdicVal l = 0 := by omega
        rw [hz, pow_zero] at hlpow
        exact hl1 hlpow
      obtain ⟨y, hy⟩ := Sark.exists_pow_two_of_not_pow_two hf hx (not_pow_two hp hp1) hv1
      exact ⟨y, by rw [hlpow]; exact hy⟩
  · rw [hop] at h1
    omega

end Shk

theorem solution (f : ℝ → ℝ) (hf : Continuous f) (p m : ℕ) (hp : Odd p) (hp1 : 1 < p)
    (h : ∃ x, Devaney.HasPrimePeriod f x (p * 2 ^ m)) (l : ℕ)
    (hl : Devaney.SarkovskiiPrecedes (p * 2 ^ m) l) :
    ∃ x, Devaney.HasPrimePeriod f x l :=
  Shk.sarkovskii_general f hf p m hp hp1 h l hl
