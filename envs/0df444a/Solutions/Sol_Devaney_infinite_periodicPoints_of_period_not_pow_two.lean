-- Prove2me | solution 1 for Devaney.infinite_periodicPoints_of_period_not_pow_two
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-17T04:00:27.643741+00:00
-- url     : https://prove2.me/submissions/ac88159f-4a37-4cda-8ea6-525fa655f4ad

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

theorem solution (f : ℝ → ℝ) (hf : Continuous f) (n : ℕ)
    (h : ∃ x, Devaney.HasPrimePeriod f x n) (hn : ∀ m : ℕ, n ≠ 2 ^ m) :
    {x : ℝ | ∃ k > 0, f^[k] x = x}.Infinite :=
  Sark.infinite_periodicPoints_aux f hf n h hn
