-- Prove2me | solution 1 for Devaney.odd_period_all_even_and_above
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-17T14:50:50.50724+00:00
-- url     : https://prove2.me/submissions/1b373367-3f3a-4707-b0ab-455691279eed

import Mathlib
import Definitions.Def_Devaney_sarkovskii
import Theorems.Thm_Devaney_exists_periodicPt_of_covering_cycle

open Set Function

namespace Shk

def Cov (f : ℝ → ℝ) (a b c d : ℝ) : Prop := uIcc c d ⊆ f '' uIcc a b

theorem cov_of_subset {f : ℝ → ℝ} (hf : Continuous f) {a b c d : ℝ}
    (h : uIcc c d ⊆ uIcc (f a) (f b)) : Cov f a b c d :=
  h.trans (intermediate_value_uIcc hf.continuousOn)

theorem cov_of_mem {f : ℝ → ℝ} (hf : Continuous f) {a b c d : ℝ}
    (hc : c ∈ uIcc (f a) (f b)) (hd : d ∈ uIcc (f a) (f b)) : Cov f a b c d :=
  cov_of_subset hf (uIcc_subset_uIcc hc hd)

theorem exists_loop_point {f : ℝ → ℝ} (hf : Continuous f) (n : ℕ) (hn : 0 < n)
    (A B : ℕ → ℝ) (hcov : ∀ i < n, Cov f (A i) (B i) (A (i + 1)) (B (i + 1)))
    (hA : A n = A 0) (hB : B n = B 0) :
    ∃ y, f^[n] y = y ∧ ∀ i < n, f^[i] y ∈ uIcc (A i) (B i) :=
  Devaney.exists_periodicPt_of_covering_cycle f hf n hn A B hcov hA hB

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

end Shk

theorem solution (f : ℝ → ℝ) (hf : Continuous f) (m : ℕ) (hm : 3 ≤ m) (hodd : Odd m)
    (h : ∃ x, Devaney.HasPrimePeriod f x m) :
    (∀ n : ℕ, 2 ≤ n → n % 2 = 0 → ∃ y, Devaney.HasPrimePeriod f y n) ∧
    (∀ n : ℕ, m + 1 ≤ n → ∃ y, Devaney.HasPrimePeriod f y n) := by
  obtain ⟨x, hx⟩ := h
  exact Shk.odd_main hf hx hm hodd
