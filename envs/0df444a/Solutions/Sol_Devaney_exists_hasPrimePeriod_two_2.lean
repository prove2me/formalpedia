-- Prove2me | solution 2 for Devaney.exists_hasPrimePeriod_two
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-17T14:43:17.596648+00:00
-- url     : https://prove2.me/submissions/f9d997a1-d955-4aec-a202-232e87a57d08

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

theorem solution (f : ℝ → ℝ) (hf : Continuous f) (m : ℕ) (hm : 2 < m)
    (h : ∃ x, Devaney.HasPrimePeriod f x m) : ∃ y, Devaney.HasPrimePeriod f y 2 := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨y, h1, h2⟩ := Sark.exists_two_cycle hf (by omega) hx
  refine ⟨y, two_pos, ?_, ?_⟩
  · show f^[2] y = y
    simpa using h1
  · intro k hk hk2
    interval_cases k
    · simpa using h2
