-- Prove2me | solution 1 for DiscreteConvex.MConvexFunctionsE.mexchange_iff_perturbed_level_sets_qexcw
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T01:29:15.603898+00:00
-- url     : https://prove2.me/submissions/a4749455-dfd6-4a18-936f-27c89db0b707

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_QEXCw
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_LevelSet
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_LinearWeight

open Classical
open scoped Pointwise
open DiscreteConvex.MConvexFunctionsE

private lemma coe_untopD_of_ne_top {a : WithTop ℝ} (ha : a ≠ ⊤) :
    ((a.untopD 0 : ℝ) : WithTop ℝ) = a := by
  cases a with
  | top => exact absurd rfl ha
  | coe r => rfl

private lemma ne_top_of_add_le {a b c d : WithTop ℝ} (h : a + b ≤ c + d)
    (hc : c ≠ ⊤) (hd : d ≠ ⊤) : a ≠ ⊤ ∧ b ≠ ⊤ := by
  have hcd : c + d ≠ ⊤ := WithTop.add_ne_top.mpr ⟨hc, hd⟩
  have hab : a + b ≠ ⊤ := ne_top_of_le_ne_top hcd h
  exact WithTop.add_ne_top.mp hab

private lemma cancel_middle_le {a b c d e g : WithTop ℝ}
    (h1 : a + b ≤ c + d) (h2 : c + e ≤ a + g)
    (hc : c ≠ ⊤) (hd : d ≠ ⊤) (hg : g ≠ ⊤) :
    e + b ≤ g + d := by
  obtain ⟨ha, hb⟩ := ne_top_of_add_le h1 hc hd
  obtain ⟨_, he⟩ := ne_top_of_add_le h2 ha hg
  rw [← coe_untopD_of_ne_top ha, ← coe_untopD_of_ne_top hb,
      ← coe_untopD_of_ne_top hc, ← coe_untopD_of_ne_top hd] at h1
  rw [← coe_untopD_of_ne_top hc, ← coe_untopD_of_ne_top he,
      ← coe_untopD_of_ne_top ha, ← coe_untopD_of_ne_top hg] at h2
  rw [← coe_untopD_of_ne_top he, ← coe_untopD_of_ne_top hb,
      ← coe_untopD_of_ne_top hg, ← coe_untopD_of_ne_top hd]
  norm_cast at h1 h2 ⊢
  linarith

private lemma two_lt {α : ℝ} {y z : WithTop ℝ} (hy : (α : WithTop ℝ) < y)
    (hz : (α : WithTop ℝ) < z) : ((α + α : ℝ) : WithTop ℝ) < y + z := by
  induction y using WithTop.recTopCoe with
  | top => simp
  | coe c =>
    induction z using WithTop.recTopCoe with
    | top => simp
    | coe d =>
      rw [WithTop.coe_lt_coe] at hy hz
      rw [← WithTop.coe_add, WithTop.coe_lt_coe]; linarith

private lemma approx {r : ℝ} {y z : WithTop ℝ} (h : (r : WithTop ℝ) < y + z) :
    ∃ c d : ℝ, (c : WithTop ℝ) ≤ y ∧ (d : WithTop ℝ) ≤ z ∧ r < c + d := by
  induction y using WithTop.recTopCoe with
  | top =>
    induction z using WithTop.recTopCoe with
    | top => exact ⟨r + 1, 0, le_top, le_top, by linarith⟩
    | coe d => exact ⟨r - d + 1, d, le_top, le_rfl, by linarith⟩
  | coe c =>
    induction z using WithTop.recTopCoe with
    | top => exact ⟨c, r - c + 1, le_rfl, le_top, by linarith⟩
    | coe d =>
      rw [← WithTop.coe_add, WithTop.coe_lt_coe] at h
      exact ⟨c, d, le_rfl, le_rfl, h⟩

private lemma lin_step_sub_add {V : Type*} [Fintype V] [DecidableEq V]
    (p : V → ℝ) (x : V → ℤ) (u v : V) :
    ∑ w : V, p w * (((x w - CharVec u w + CharVec v w : ℤ) : ℝ)) =
      (∑ w : V, p w * (x w : ℝ)) - p u + p v := by
  have h1 : ∀ w : V, p w * (((x w - CharVec u w + CharVec v w : ℤ) : ℝ)) =
      p w * (x w : ℝ) - p w * (CharVec u w : ℝ) + p w * (CharVec v w : ℝ) := by
    intro w; push_cast; ring
  simp_rw [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hu : ∑ w : V, p w * (CharVec u w : ℝ) = p u := by
    simp [CharVec]
  have hv : ∑ w : V, p w * (CharVec v w : ℝ) = p v := by
    simp [CharVec]
  rw [hu, hv]

private lemma lin_step_add_sub {V : Type*} [Fintype V] [DecidableEq V]
    (p : V → ℝ) (y : V → ℤ) (u v : V) :
    ∑ w : V, p w * (((y w + CharVec u w - CharVec v w : ℤ) : ℝ)) =
      (∑ w : V, p w * (y w : ℝ)) + p u - p v := by
  have h1 : ∀ w : V, p w * (((y w + CharVec u w - CharVec v w : ℤ) : ℝ)) =
      p w * (y w : ℝ) + p w * (CharVec u w : ℝ) - p w * (CharVec v w : ℝ) := by
    intro w; push_cast; ring
  simp_rw [h1, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hu : ∑ w : V, p w * (CharVec u w : ℝ) = p u := by
    simp [CharVec]
  have hv : ∑ w : V, p w * (CharVec v w : ℝ) = p v := by
    simp [CharVec]
  rw [hu, hv]

private lemma mexchange_imp_qexcw {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f) :
    ∀ p : V → ℝ, ∀ alpha : ℝ, QEXCw (LevelSet (LinearWeight f p) alpha) := by
  intro p alpha x hx y hy hxy
  simp only [LevelSet, Set.mem_setOf_eq, LinearWeight] at hx hy ⊢
  have hxd : x ∈ DomZ f := by
    intro htop; simp [htop] at hx
  have hyd : y ∈ DomZ f := by
    intro htop; simp [htop] at hy
  have hpos_ne : (SuppPos x y).Nonempty := by
    by_contra h_empty
    rw [Finset.not_nonempty_iff_eq_empty] at h_empty
    have hneg_ne : (SuppPos y x).Nonempty := by
      by_contra h_empty2
      rw [Finset.not_nonempty_iff_eq_empty] at h_empty2
      apply hxy
      ext w
      have h1 : ¬ (y w < x w) := by
        intro hlt
        have : w ∈ SuppPos x y := by simpa [SuppPos] using hlt
        rw [h_empty] at this
        exact Finset.notMem_empty w this
      have h2 : ¬ (x w < y w) := by
        intro hlt
        have : w ∈ SuppPos y x := by simpa [SuppPos] using hlt
        rw [h_empty2] at this
        exact Finset.notMem_empty w this
      omega
    obtain ⟨u', hu'⟩ := hneg_ne
    obtain ⟨v', hv', _⟩ := hf y hyd x hxd u' hu'
    have hv'_pos : v' ∈ SuppPos x y := by simpa [SuppPos, SuppNeg] using hv'
    rw [h_empty] at hv'_pos
    exact Finset.notMem_empty v' hv'_pos
  obtain ⟨u, hu⟩ := hpos_ne
  obtain ⟨v, hv, hex⟩ := hf x hxd y hyd u hu
  refine ⟨u, hu, v, hv, ?_⟩
  by_contra hc
  rw [not_or, not_le, not_le] at hc
  have h1 := two_lt hc.1 hc.2
  set px := -(∑ w : V, p w * (x w : ℝ))
  set py := -(∑ w : V, p w * (y w : ℝ))
  set px' := -(∑ w : V, p w * (((x w - CharVec u w + CharVec v w : ℤ) : ℝ)))
  set py' := -(∑ w : V, p w * (((y w + CharVec u w - CharVec v w : ℤ) : ℝ)))
  have hlin : px' + py' = px + py := by
    simp only [px', py', px, py, lin_step_sub_add, lin_step_add_sub]
    ring
  have h2 :
      (f (fun w => x w - CharVec u w + CharVec v w) + (px' : WithTop ℝ)) +
        (f (fun w => y w + CharVec u w - CharVec v w) + (py' : WithTop ℝ)) ≤
      (f x + (px : WithTop ℝ)) + (f y + (py : WithTop ℝ)) := by
    calc (f (fun w => x w - CharVec u w + CharVec v w) + (px' : WithTop ℝ)) +
          (f (fun w => y w + CharVec u w - CharVec v w) + (py' : WithTop ℝ))
        = (f (fun w => x w - CharVec u w + CharVec v w) +
            f (fun w => y w + CharVec u w - CharVec v w)) + ((px' + py' : ℝ) : WithTop ℝ) := by
          rw [WithTop.coe_add]; abel
      _ ≤ (f x + f y) + ((px + py : ℝ) : WithTop ℝ) := by
          rw [hlin]; exact add_le_add hex le_rfl
      _ = (f x + (px : WithTop ℝ)) + (f y + (py : WithTop ℝ)) := by
          rw [WithTop.coe_add]; abel
  have h3 : (f x + (px : WithTop ℝ)) + (f y + (py : WithTop ℝ)) ≤
      ((alpha + alpha : ℝ) : WithTop ℝ) := by
    rw [WithTop.coe_add]; exact add_le_add hx hy
  exact lt_irrefl _ (h1.trans_le (h2.trans h3))

private def d1 {V : Type*} [Fintype V] (x y : V → ℤ) : ℤ :=
  ∑ w : V, |x w - y w|

private lemma d1_nonneg {V : Type*} [Fintype V] (x y : V → ℤ) : 0 ≤ d1 x y :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

private lemma step_dist {V : Type*} [Fintype V] [DecidableEq V]
    (x y : V → ℤ) (u v : V) (hu : y u < x u) (hv : x v < y v) :
    d1 x (fun w => y w + CharVec u w - CharVec v w) < d1 x y := by
  have huv : u ≠ v := by rintro rfl; omega
  apply Finset.sum_lt_sum
  · intro w _
    simp only [CharVec]
    by_cases h1 : w = u
    · subst h1
      simp only [if_true, if_neg huv]
      rcases abs_cases (x w - y w) with ⟨h, _⟩ | ⟨h, _⟩ <;>
        rcases abs_cases (x w - (y w + 1 - 0)) with ⟨h', _⟩ | ⟨h', _⟩ <;> omega
    · by_cases h2 : w = v
      · subst h2
        simp only [if_neg h1, if_true]
        rcases abs_cases (x w - y w) with ⟨h, _⟩ | ⟨h, _⟩ <;>
          rcases abs_cases (x w - (y w + 0 - 1)) with ⟨h', _⟩ | ⟨h', _⟩ <;> omega
      · simp [h1, h2]
  · refine ⟨u, Finset.mem_univ _, ?_⟩
    simp only [CharVec, if_true, if_neg huv]
    rcases abs_cases (x u - y u) with ⟨h, _⟩ | ⟨h, _⟩ <;>
      rcases abs_cases (x u - (y u + 1 - 0)) with ⟨h', _⟩ | ⟨h', _⟩ <;> omega

private lemma shift_pos {V : Type*} [Fintype V] [DecidableEq V]
    {x y : V → ℤ} {u v u' : V} (hv : x v < y v)
    (h : u' ∈ SuppPos x (fun w => y w + CharVec u w - CharVec v w)) : u' ∈ SuppPos x y := by
  rw [SuppPos, Finset.mem_filter] at h ⊢
  rcases h with ⟨_, h⟩
  refine ⟨Finset.mem_univ _, ?_⟩
  simp only [CharVec] at h
  split_ifs at h <;> subst_vars <;> omega

private lemma shift_neg {V : Type*} [Fintype V] [DecidableEq V]
    {x y : V → ℤ} {u v v' : V} (hu : y u < x u)
    (h : v' ∈ SuppNeg x (fun w => y w + CharVec u w - CharVec v w)) : v' ∈ SuppNeg x y := by
  rw [SuppNeg, Finset.mem_filter] at h ⊢
  rcases h with ⟨_, h⟩
  refine ⟨Finset.mem_univ _, ?_⟩
  simp only [CharVec] at h
  split_ifs at h <;> subst_vars <;> omega

private lemma qexcw_one_sided_aux {V : Type*} [Fintype V] [DecidableEq V]
    {B : Set (V → ℤ)} (hB : QEXCw B) (x : V → ℤ) (hx : x ∈ B) :
    ∀ n : ℕ, ∀ y ∈ B, d1 x y < n → x ≠ y →
      ∃ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
        (fun w => x w - CharVec u w + CharVec v w) ∈ B := by
  intro n
  induction n with
  | zero =>
    intro y _ hd
    exact absurd hd (by have := d1_nonneg x y; omega)
  | succ n ih =>
    intro y hy hd hxy
    obtain ⟨u, hu, v, hv, hstep⟩ := hB x hx y hy hxy
    rcases hstep with hx' | hy'
    · exact ⟨u, hu, v, hv, hx'⟩
    · set y' : V → ℤ := fun w => y w + CharVec u w - CharVec v w with hy'_def
      by_cases hxy' : x = y'
      · refine ⟨u, hu, v, hv, ?_⟩
        have heq : (fun w => x w - CharVec u w + CharVec v w) = y := by
          ext w; rw [hxy']; dsimp only [y']; ring
        rw [heq]; exact hy
      · have hu_lt : y u < x u := by simpa [SuppPos] using hu
        have hv_lt : x v < y v := by simpa [SuppNeg] using hv
        have hd' : d1 x y' < n := by
          have := step_dist x y u v hu_lt hv_lt
          rw [← hy'_def] at this
          omega
        obtain ⟨u', hu'', v', hv'', hmem⟩ := ih y' hy' hd' hxy'
        exact ⟨u', shift_pos hv_lt hu'', v', shift_neg hu_lt hv'', hmem⟩

private lemma qexcw_one_sided {V : Type*} [Fintype V] [DecidableEq V]
    {B : Set (V → ℤ)} (hB : QEXCw B) {x y : V → ℤ} (hx : x ∈ B) (hy : y ∈ B) (hxy : x ≠ y) :
    ∃ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
      (fun w => x w - CharVec u w + CharVec v w) ∈ B :=
  qexcw_one_sided_aux hB x hx ((d1 x y).toNat + 1) y hy
    (by have := d1_nonneg x y; omega) hxy

private lemma down_of_level_qexcw {V : Type*} [Fintype V] [DecidableEq V]
    {f : (V → ℤ) → WithTop ℝ}
    (h : ∀ p : V → ℝ, ∀ alpha : ℝ, QEXCw (LevelSet (LinearWeight f p) alpha))
    (p : V → ℝ) {x y : V → ℤ} (hx : x ∈ DomZ f) (hy : y ∈ DomZ f) (hxy : x ≠ y)
    (hle : LinearWeight f p y ≤ LinearWeight f p x) :
    ∃ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
      LinearWeight f p (fun w => x w - CharVec u w + CharVec v w) ≤ LinearWeight f p x := by
  set α : ℝ := (f x).untopD 0 - ∑ w : V, p w * (x w : ℝ)
  have hgx : LinearWeight f p x = (α : WithTop ℝ) := by
    rw [LinearWeight, ← coe_untopD_of_ne_top hx, ← WithTop.coe_add]
    rfl
  have hxL : x ∈ LevelSet (LinearWeight f p) α := by
    simp [LevelSet, hgx]
  have hyL : y ∈ LevelSet (LinearWeight f p) α := by
    simp only [LevelSet, Set.mem_setOf_eq]
    rwa [← hgx]
  obtain ⟨u, hu, v, hv, hmem⟩ := qexcw_one_sided (h p α) hxL hyL hxy
  simp only [LevelSet, Set.mem_setOf_eq, ← hgx] at hmem
  exact ⟨u, hu, v, hv, hmem⟩

private lemma singleton_suppPos_exchange {V : Type*} [Fintype V] [DecidableEq V]
    {f : (V → ℤ) → WithTop ℝ}
    (h : ∀ p : V → ℝ, ∀ alpha : ℝ, QEXCw (LevelSet (LinearWeight f p) alpha))
    {x y : V → ℤ} (hx : x ∈ DomZ f) (hy : y ∈ DomZ f)
    {u₀ : V} (hu₀ : u₀ ∈ SuppPos x y) (huniq : ∀ u ∈ SuppPos x y, u = u₀) :
    ∃ v ∈ SuppNeg x y,
      f (fun w => x w - CharVec u₀ w + CharVec v w) +
        f (fun w => y w + CharVec u₀ w - CharVec v w) ≤ f x + f y := by
  by_contra! hlt_all
  set a : ℝ := (f x).untopD 0
  set b : ℝ := (f y).untopD 0
  have ha : ((a : ℝ) : WithTop ℝ) = f x := coe_untopD_of_ne_top hx
  have hb : ((b : ℝ) : WithTop ℝ) = f y := coe_untopD_of_ne_top hy
  have hcd : ∀ v : V, ∃ c d : ℝ,
      (v ∈ SuppNeg x y →
        (c : WithTop ℝ) ≤ f (fun w => x w - CharVec u₀ w + CharVec v w) ∧
        (d : WithTop ℝ) ≤ f (fun w => y w + CharVec u₀ w - CharVec v w) ∧
        a + b < c + d) := by
    intro v
    by_cases hv : v ∈ SuppNeg x y
    · have hlt := hlt_all v hv
      rw [← ha, ← hb, ← WithTop.coe_add] at hlt
      obtain ⟨c, d, hc, hd, hcd_lt⟩ := approx hlt
      exact ⟨c, d, fun _ => ⟨hc, hd, hcd_lt⟩⟩
    · exact ⟨0, 0, fun h' => absurd h' hv⟩
  choose c d hcd_spec using hcd
  let p : V → ℝ := fun v => if v ∈ SuppNeg x y then ((c v - a) + (b - d v)) / 2 else 0
  have hpu₀ : p u₀ = 0 := by
    have hu_not_neg : u₀ ∉ SuppNeg x y := by
      have hu₀_lt : y u₀ < x u₀ := by simpa [SuppPos] using hu₀
      simp only [SuppNeg, Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
      omega
    simp [p, hu_not_neg]
  have hxy : x ≠ y := by
    have hu₀_lt : y u₀ < x u₀ := by simpa [SuppPos] using hu₀
    intro heq; subst heq; omega
  rcases le_total (LinearWeight f p y) (LinearWeight f p x) with hle | hle
  · obtain ⟨u, hu, v, hv, hstep⟩ := down_of_level_qexcw h p hx hy hxy hle
    have hu_eq : u = u₀ := huniq u hu
    rw [hu_eq] at hstep
    obtain ⟨hc_le, hd_le, hcd_lt⟩ := hcd_spec v hv
    have hpv : p v = ((c v - a) + (b - d v)) / 2 := by simp [p, hv]
    simp only [LinearWeight, lin_step_sub_add, hpu₀, ← ha] at hstep
    have hle_c :
        ((c v : WithTop ℝ) + ((-((∑ w : V, p w * (x w : ℝ)) - 0 + p v) : ℝ) : WithTop ℝ)) ≤
          ((a : WithTop ℝ) + ((-(∑ w : V, p w * (x w : ℝ)) : ℝ) : WithTop ℝ)) :=
      (add_le_add hc_le le_rfl).trans hstep
    rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe] at hle_c
    linarith
  · obtain ⟨v, hv_pos, u, hu_neg, hstep⟩ := down_of_level_qexcw h p hy hx hxy.symm hle
    have hv : v ∈ SuppNeg x y := by simpa [SuppPos, SuppNeg] using hv_pos
    have hu : u ∈ SuppPos x y := by simpa [SuppPos, SuppNeg] using hu_neg
    have hu_eq : u = u₀ := huniq u hu
    rw [hu_eq] at hstep
    obtain ⟨hc_le, hd_le, hcd_lt⟩ := hcd_spec v hv
    have hpv : p v = ((c v - a) + (b - d v)) / 2 := by simp [p, hv]
    have heq_y : (fun w => y w - CharVec v w + CharVec u₀ w) =
        (fun w => y w + CharVec u₀ w - CharVec v w) := by ext w; ring
    rw [heq_y] at hstep
    simp only [LinearWeight, lin_step_add_sub, hpu₀, ← hb] at hstep
    have hle_d :
        ((d v : WithTop ℝ) + ((-((∑ w : V, p w * (y w : ℝ)) + 0 - p v) : ℝ) : WithTop ℝ)) ≤
          ((b : WithTop ℝ) + ((-(∑ w : V, p w * (y w : ℝ)) : ℝ) : WithTop ℝ)) :=
      (add_le_add hd_le le_rfl).trans hstep
    rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe] at hle_d
    linarith

private lemma exists_domZ_step {V : Type*} [Fintype V] [DecidableEq V]
    {f : (V → ℤ) → WithTop ℝ}
    (h : ∀ p : V → ℝ, ∀ alpha : ℝ, QEXCw (LevelSet (LinearWeight f p) alpha))
    {x y : V → ℤ} (hx : x ∈ DomZ f) (hy : y ∈ DomZ f)
    {u₀ : V} (hu₀ : u₀ ∈ SuppPos x y) :
    ∃ v ∈ SuppNeg x y, (fun w => x w - CharVec u₀ w + CharVec v w) ∈ DomZ f := by
  set a : ℝ := (f x).untopD 0
  set b : ℝ := (f y).untopD 0
  have ha : ((a : ℝ) : WithTop ℝ) = f x := coe_untopD_of_ne_top hx
  have hb : ((b : ℝ) : WithTop ℝ) = f y := coe_untopD_of_ne_top hy
  have huniv_ne : (Finset.univ : Finset (V × V)).Nonempty := by
    exact ⟨(u₀, u₀), Finset.mem_univ _⟩
  let val : V × V → ℝ := fun uv =>
    |a - (f (fun w => x w - CharVec uv.1 w + CharVec uv.2 w)).untopD 0|
  set M : ℝ := Finset.univ.sup' huniv_ne val + 1
  have hM_gt : ∀ u' v : V,
      a - (f (fun w => x w - CharVec u' w + CharVec v w)).untopD 0 < M := by
    intro u' v
    have hle : val (u', v) ≤ Finset.univ.sup' huniv_ne val :=
      Finset.le_sup' val (Finset.mem_univ (u', v))
    have habs : a - (f (fun w => x w - CharVec u' w + CharVec v w)).untopD 0 ≤ val (u', v) :=
      le_abs_self _
    linarith
  let q : V → ℝ := fun w => if w ∈ SuppPos x y ∧ w ≠ u₀ then M else 0
  set R : ℝ := ∑ w ∈ Finset.univ.erase u₀, q w * ((x w : ℝ) - (y w : ℝ))
  have hu₀_lt : y u₀ < x u₀ := by simpa [SuppPos] using hu₀
  have hdiff_pos : (0 : ℝ) < (x u₀ : ℝ) - (y u₀ : ℝ) := by
    have : (y u₀ : ℝ) < (x u₀ : ℝ) := by exact_mod_cast hu₀_lt
    linarith
  set pu₀ : ℝ := ((a - b) - R) / ((x u₀ : ℝ) - (y u₀ : ℝ))
  let p : V → ℝ := fun w => if w = u₀ then pu₀ else q w
  have hp_sum : ∑ w : V, p w * ((x w : ℝ) - (y w : ℝ)) = a - b := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ u₀)]
    have h1 : p u₀ * ((x u₀ : ℝ) - (y u₀ : ℝ)) = (a - b) - R := by
      simp only [p, ↓reduceIte, pu₀]
      exact div_mul_cancel₀ ((a - b) - R) hdiff_pos.ne'
    have h2 : ∑ w ∈ Finset.univ.erase u₀, p w * ((x w : ℝ) - (y w : ℝ)) = R := by
      refine Finset.sum_congr rfl (fun w hw => ?_)
      have hne : w ≠ u₀ := (Finset.mem_erase.mp hw).1
      simp [p, hne]
    linarith
  have hle_xy : LinearWeight f p y ≤ LinearWeight f p x := by
    simp only [LinearWeight, ← ha, ← hb, ← WithTop.coe_add, WithTop.coe_le_coe]
    have : (∑ w : V, p w * (x w : ℝ)) - (∑ w : V, p w * (y w : ℝ)) =
        ∑ w : V, p w * ((x w : ℝ) - (y w : ℝ)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun w _ => by ring)
    linarith
  have hxy : x ≠ y := by intro heq; subst heq; omega
  obtain ⟨u', hu', v, hv, hstep⟩ := down_of_level_qexcw h p hx hy hxy hle_xy
  have hgx_ne : LinearWeight f p x ≠ ⊤ :=
    WithTop.add_ne_top.mpr ⟨hx, WithTop.coe_ne_top⟩
  have hstep_ne : LinearWeight f p (fun w => x w - CharVec u' w + CharVec v w) ≠ ⊤ :=
    ne_top_of_le_ne_top hgx_ne hstep
  have hdom : (fun w => x w - CharVec u' w + CharVec v w) ∈ DomZ f :=
    (WithTop.add_ne_top.mp hstep_ne).1
  have hu'_eq : u' = u₀ := by
    by_contra hu'_ne
    have hpu' : p u' = M := by simp [p, q, hu', hu'_ne]
    have hpv : p v = 0 := by
      have hv_lt : x v < y v := by simpa [SuppNeg] using hv
      have hv_ne_u₀ : v ≠ u₀ := by intro h'; subst h'; omega
      have hv_not_pos : v ∉ SuppPos x y := by
        simp only [SuppPos, Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
        omega
      simp [p, q, hv_ne_u₀, hv_not_pos]
    rw [LinearWeight, LinearWeight, lin_step_sub_add, hpu', hpv, ← ha,
      ← coe_untopD_of_ne_top hdom, ← WithTop.coe_add, ← WithTop.coe_add,
      WithTop.coe_le_coe] at hstep
    have := hM_gt u' v
    linarith
  rw [hu'_eq] at hdom
  exact ⟨v, hv, hdom⟩

private lemma four_point_exchange {V : Type*} [Fintype V] [DecidableEq V]
    {f : (V → ℤ) → WithTop ℝ}
    (h : ∀ p : V → ℝ, ∀ alpha : ℝ, QEXCw (LevelSet (LinearWeight f p) alpha))
    {x : V → ℤ} (hx : x ∈ DomZ f)
    {u₀ u₁ v₁ v₂ : V} (hu₀₁ : u₀ ≠ u₁)
    (hu₀v₁ : u₀ ≠ v₁) (hu₀v₂ : u₀ ≠ v₂) (hu₁v₁ : u₁ ≠ v₁) (hu₁v₂ : u₁ ≠ v₂)
    (ha : (fun w => x w - CharVec u₀ w - CharVec u₁ w + CharVec v₁ w + CharVec v₂ w) ∈ DomZ f) :
    f (fun w => x w - CharVec u₀ w + CharVec v₁ w) +
      f (fun w => x w - CharVec u₁ w + CharVec v₂ w) ≤
        f (fun w => x w - CharVec u₀ w - CharVec u₁ w + CharVec v₁ w + CharVec v₂ w) + f x ∨
    f (fun w => x w - CharVec u₀ w + CharVec v₂ w) +
      f (fun w => x w - CharVec u₁ w + CharVec v₁ w) ≤
        f (fun w => x w - CharVec u₀ w - CharVec u₁ w + CharVec v₁ w + CharVec v₂ w) + f x := by
  let a : V → ℤ := fun w => x w - CharVec u₀ w - CharVec u₁ w + CharVec v₁ w + CharVec v₂ w
  by_cases hv₁₂ : v₁ = v₂
  · subst hv₁₂
    have hv₁_pos : v₁ ∈ SuppPos a x := by
      rw [SuppPos, Finset.mem_filter]
      refine ⟨Finset.mem_univ v₁, ?_⟩
      simp only [a, CharVec, hu₀v₁.symm, hu₁v₁.symm, ↓reduceIte]
      omega
    have huniq_v₁ : ∀ v ∈ SuppPos a x, v = v₁ := by
      intro v hv
      simp only [SuppPos, Finset.mem_filter, Finset.mem_univ, true_and, a] at hv
      by_contra hne
      have h1 : 0 ≤ CharVec u₀ v := by simp [CharVec]; split_ifs <;> omega
      have h2 : 0 ≤ CharVec u₁ v := by simp [CharVec]; split_ifs <;> omega
      have h3 : CharVec v₁ v = 0 := by simp [CharVec, hne]
      omega
    obtain ⟨u, hu_neg, hle⟩ := singleton_suppPos_exchange h ha hx hv₁_pos huniq_v₁
    have hu_cases : u = u₀ ∨ u = u₁ := by
      simp only [SuppNeg, Finset.mem_filter, Finset.mem_univ, true_and, a] at hu_neg
      by_contra! hne
      have h1 : CharVec u₀ u = 0 := by simp [CharVec, hne.1]
      have h2 : CharVec u₁ u = 0 := by simp [CharVec, hne.2]
      have h3 : 0 ≤ CharVec v₁ u := by simp [CharVec]; split_ifs <;> omega
      omega
    rcases hu_cases with hu_eq | hu_eq
    · left
      rw [hu_eq] at hle
      have heq1 : (fun w => a w - CharVec v₁ w + CharVec u₀ w) =
          (fun w => x w - CharVec u₁ w + CharVec v₁ w) := by ext w; dsimp [a]; ring
      have heq2 : (fun w => x w + CharVec v₁ w - CharVec u₀ w) =
          (fun w => x w - CharVec u₀ w + CharVec v₁ w) := by ext w; ring
      rw [heq1, heq2, add_comm] at hle
      exact hle
    · left
      rw [hu_eq] at hle
      have heq1 : (fun w => a w - CharVec v₁ w + CharVec u₁ w) =
          (fun w => x w - CharVec u₀ w + CharVec v₁ w) := by ext w; dsimp [a]; ring
      have heq2 : (fun w => x w + CharVec v₁ w - CharVec u₁ w) =
          (fun w => x w - CharVec u₁ w + CharVec v₁ w) := by ext w; ring
      rw [heq1, heq2] at hle
      exact hle
  · by_contra! hlt_both
    obtain ⟨hlt1, hlt2⟩ := hlt_both
    set fx : ℝ := (f x).untopD 0
    set fa : ℝ := (f a).untopD 0
    have hfx : ((fx : ℝ) : WithTop ℝ) = f x := coe_untopD_of_ne_top hx
    have hfa : ((fa : ℝ) : WithTop ℝ) = f a := coe_untopD_of_ne_top ha
    rw [← hfa, ← hfx, ← WithTop.coe_add] at hlt1 hlt2
    obtain ⟨c₁, d₁, hc₁, hd₁, hcd₁⟩ := approx hlt1
    obtain ⟨c₂, d₂, hc₂, hd₂, hcd₂⟩ := approx hlt2
    set δ₁ : ℝ := ((fx - c₁) + (d₁ - fa)) / 2
    set δ₂ : ℝ := ((fx - c₂) + (d₂ - fa)) / 2
    let p : V → ℝ := fun w =>
      if w = u₀ then 0
      else if w = v₁ then -δ₁
      else if w = v₂ then -δ₂
      else if w = u₁ then (fx - fa) - δ₁ - δ₂
      else 0
    have hpu₀ : p u₀ = 0 := by simp [p]
    have hpv₁ : p v₁ = -δ₁ := by simp [p, hu₀v₁.symm]
    have hpv₂ : p v₂ = -δ₂ := by simp [p, hu₀v₂.symm, Ne.symm hv₁₂]
    have hpu₁ : p u₁ = (fx - fa) - δ₁ - δ₂ := by
      simp [p, hu₀₁.symm, hu₁v₁, hu₁v₂]
    set px : ℝ := ∑ w : V, p w * (x w : ℝ)
    have ha_decomp : a = fun w =>
        (x w - CharVec u₀ w + CharVec v₁ w) - CharVec u₁ w + CharVec v₂ w := by
      ext w; dsimp [a]; ring
    have hpa : ∑ w : V, p w * (a w : ℝ) = px - p u₀ + p v₁ - p u₁ + p v₂ := by
      rw [ha_decomp, lin_step_sub_add, lin_step_sub_add]
    set α : ℝ := fx - px
    have hgx : LinearWeight f p x = (α : WithTop ℝ) := by
      rw [LinearWeight, ← hfx, ← WithTop.coe_add]
      rfl
    have hga : LinearWeight f p a = (α : WithTop ℝ) := by
      rw [LinearWeight, ← hfa, ← WithTop.coe_add, hpa, hpu₀, hpv₁, hpv₂, hpu₁]
      congr 1; dsimp [α]; ring
    have hxL : x ∈ LevelSet (LinearWeight f p) α := by simp [LevelSet, hgx]
    have haL : a ∈ LevelSet (LinearWeight f p) α := by simp [LevelSet, hga]
    have hxa : x ≠ a := by
      intro heq
      have : x u₀ = a u₀ := congrFun heq u₀
      simp only [a, CharVec, ↓reduceIte, hu₀₁, hu₀v₁, hu₀v₂] at this
      omega
    obtain ⟨u, hu_pos, v, hv_neg, hstep⟩ := h p α x hxL a haL hxa
    have hu_cases : u = u₀ ∨ u = u₁ := by
      simp only [SuppPos, Finset.mem_filter, Finset.mem_univ, true_and, a] at hu_pos
      by_contra! hne
      have h1 : CharVec u₀ u = 0 := by simp [CharVec, hne.1]
      have h2 : CharVec u₁ u = 0 := by simp [CharVec, hne.2]
      have h3 : 0 ≤ CharVec v₁ u := by simp [CharVec]; split_ifs <;> omega
      have h4 : 0 ≤ CharVec v₂ u := by simp [CharVec]; split_ifs <;> omega
      omega
    have hv_cases : v = v₁ ∨ v = v₂ := by
      simp only [SuppNeg, Finset.mem_filter, Finset.mem_univ, true_and, a] at hv_neg
      by_contra! hne
      have h1 : 0 ≤ CharVec u₀ v := by simp [CharVec]; split_ifs <;> omega
      have h2 : 0 ≤ CharVec u₁ v := by simp [CharVec]; split_ifs <;> omega
      have h3 : CharVec v₁ v = 0 := by simp [CharVec, hne.1]
      have h4 : CharVec v₂ v = 0 := by simp [CharVec, hne.2]
      omega
    -- Check that all 4 combinations of (u, v) and both disjuncts yield a contradiction!
    have hz1_gt : ¬ (fun w => x w - CharVec u₀ w + CharVec v₁ w) ∈ LevelSet (LinearWeight f p) α := by
      intro hmem
      simp only [LevelSet, Set.mem_setOf_eq, LinearWeight, lin_step_sub_add, hpu₀, hpv₁] at hmem
      have hle : ((c₁ : WithTop ℝ) + ((-(px - 0 + -δ₁) : ℝ) : WithTop ℝ)) ≤ (α : WithTop ℝ) :=
        (add_le_add hc₁ le_rfl).trans hmem
      rw [← WithTop.coe_add, WithTop.coe_le_coe] at hle
      dsimp only [δ₁, α] at hle
      linarith
    have hw1_gt : ¬ (fun w => x w - CharVec u₁ w + CharVec v₂ w) ∈ LevelSet (LinearWeight f p) α := by
      intro hmem
      simp only [LevelSet, Set.mem_setOf_eq, LinearWeight, lin_step_sub_add, hpu₁, hpv₂] at hmem
      have hle : ((d₁ : WithTop ℝ) + ((-(px - ((fx - fa) - δ₁ - δ₂) + -δ₂) : ℝ) : WithTop ℝ)) ≤
          (α : WithTop ℝ) :=
        (add_le_add hd₁ le_rfl).trans hmem
      rw [← WithTop.coe_add, WithTop.coe_le_coe] at hle
      dsimp only [δ₁, δ₂, α] at hle
      linarith
    have hz2_gt : ¬ (fun w => x w - CharVec u₀ w + CharVec v₂ w) ∈ LevelSet (LinearWeight f p) α := by
      intro hmem
      simp only [LevelSet, Set.mem_setOf_eq, LinearWeight, lin_step_sub_add, hpu₀, hpv₂] at hmem
      have hle : ((c₂ : WithTop ℝ) + ((-(px - 0 + -δ₂) : ℝ) : WithTop ℝ)) ≤ (α : WithTop ℝ) :=
        (add_le_add hc₂ le_rfl).trans hmem
      rw [← WithTop.coe_add, WithTop.coe_le_coe] at hle
      dsimp only [δ₂, α] at hle
      linarith
    have hw2_gt : ¬ (fun w => x w - CharVec u₁ w + CharVec v₁ w) ∈ LevelSet (LinearWeight f p) α := by
      intro hmem
      simp only [LevelSet, Set.mem_setOf_eq, LinearWeight, lin_step_sub_add, hpu₁, hpv₁] at hmem
      have hle : ((d₂ : WithTop ℝ) + ((-(px - ((fx - fa) - δ₁ - δ₂) + -δ₁) : ℝ) : WithTop ℝ)) ≤
          (α : WithTop ℝ) :=
        (add_le_add hd₂ le_rfl).trans hmem
      rw [← WithTop.coe_add, WithTop.coe_le_coe] at hle
      dsimp only [δ₁, δ₂, α] at hle
      linarith
    rcases hu_cases with hu_eq | hu_eq <;> rcases hv_cases with hv_eq | hv_eq
    · rw [hu_eq, hv_eq] at hstep
      rcases hstep with hl | hr
      · exact hz1_gt hl
      · have heq : (fun w => a w + CharVec u₀ w - CharVec v₁ w) =
            (fun w => x w - CharVec u₁ w + CharVec v₂ w) := by ext w; dsimp [a]; ring
        rw [heq] at hr; exact hw1_gt hr
    · rw [hu_eq, hv_eq] at hstep
      rcases hstep with hl | hr
      · exact hz2_gt hl
      · have heq : (fun w => a w + CharVec u₀ w - CharVec v₂ w) =
            (fun w => x w - CharVec u₁ w + CharVec v₁ w) := by ext w; dsimp [a]; ring
        rw [heq] at hr; exact hw2_gt hr
    · rw [hu_eq, hv_eq] at hstep
      rcases hstep with hl | hr
      · exact hw2_gt hl
      · have heq : (fun w => a w + CharVec u₁ w - CharVec v₁ w) =
            (fun w => x w - CharVec u₀ w + CharVec v₂ w) := by ext w; dsimp [a]; ring
        rw [heq] at hr; exact hz2_gt hr
    · rw [hu_eq, hv_eq] at hstep
      rcases hstep with hl | hr
      · exact hw1_gt hl
      · have heq : (fun w => a w + CharVec u₁ w - CharVec v₂ w) =
            (fun w => x w - CharVec u₀ w + CharVec v₁ w) := by ext w; dsimp [a]; ring
        rw [heq] at hr; exact hz1_gt hr

private def posDist {V : Type*} [Fintype V] (x y : V → ℤ) : ℕ :=
  ∑ w : V, (x w - y w).toNat

private lemma posDist_sub_add_lt {V : Type*} [Fintype V] [DecidableEq V]
    {x y : V → ℤ} {u v : V} (hu : u ∈ SuppPos x y) (hv : v ∈ SuppNeg x y) :
    posDist (fun w => x w - CharVec u w + CharVec v w) y < posDist x y := by
  simp only [SuppPos, SuppNeg, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
  have huv : v ≠ u := by intro h; subst h; omega
  apply Finset.sum_lt_sum
  · intro w _
    by_cases hwu : w = u
    · subst hwu
      simp only [CharVec, ↓reduceIte, huv.symm, add_zero]
      omega
    · by_cases hwv : w = v
      · subst hwv
        simp only [CharVec, hwu, ↓reduceIte, sub_zero]
        omega
      · simp only [CharVec, hwu, hwv, ↓reduceIte, sub_zero, add_zero, le_refl]
  · refine ⟨u, Finset.mem_univ u, ?_⟩
    simp only [CharVec, ↓reduceIte, huv.symm, add_zero]
    omega

private lemma qexcw_imp_mexchange_aux {V : Type*} [Fintype V] [DecidableEq V]
    {f : (V → ℤ) → WithTop ℝ}
    (h : ∀ p : V → ℝ, ∀ alpha : ℝ, QEXCw (LevelSet (LinearWeight f p) alpha)) :
    ∀ (n : ℕ) (x y : V → ℤ), posDist x y = n → x ∈ DomZ f → y ∈ DomZ f →
      ∀ u₀ ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
        f (fun w => x w - CharVec u₀ w + CharVec v w) +
          f (fun w => y w + CharVec u₀ w - CharVec v w) ≤ f x + f y := by
  intro n
  induction' n using Nat.strong_induction_on with n ih
  intro x y hn hx hy u₀ hu₀
  by_cases huniq : ∀ u ∈ SuppPos x y, u = u₀
  · exact singleton_suppPos_exchange h hx hy hu₀ huniq
  · push_neg at huniq
    obtain ⟨u₁, hu₁, hu₁_ne⟩ := huniq
    have hu₀₁ : u₀ ≠ u₁ := hu₁_ne.symm
    let S : Finset V := (SuppNeg x y).filter (fun v =>
      (fun w => x w - CharVec u₁ w + CharVec v w) ∈ DomZ f)
    have hS_ne : S.Nonempty := by
      obtain ⟨v, hv, hdom⟩ := exists_domZ_step h hx hy hu₁
      exact ⟨v, Finset.mem_filter.mpr ⟨hv, hdom⟩⟩
    let score : V → WithTop ℝ := fun v =>
      f (fun w => x w - CharVec u₀ w + CharVec v w) +
        ((-((f (fun w => x w - CharVec u₁ w + CharVec v w)).untopD 0) : ℝ) : WithTop ℝ)
    obtain ⟨v₁, hv₁S, hv₁_max⟩ := Finset.exists_max_image S score hS_ne
    have hv₁_neg : v₁ ∈ SuppNeg x y := (Finset.mem_filter.mp hv₁S).1
    have hx1 : (fun w => x w - CharVec u₁ w + CharVec v₁ w) ∈ DomZ f :=
      (Finset.mem_filter.mp hv₁S).2
    let x1 : V → ℤ := fun w => x w - CharVec u₁ w + CharVec v₁ w
    have hlt1 : posDist x1 y < n := by
      rw [← hn]
      exact posDist_sub_add_lt hu₁ hv₁_neg
    have hu₀_lt : y u₀ < x u₀ := by simpa [SuppPos] using hu₀
    have hu₁_lt : y u₁ < x u₁ := by simpa [SuppPos] using hu₁
    have hv₁_lt : x v₁ < y v₁ := by simpa [SuppNeg] using hv₁_neg
    have hu₀v₁ : u₀ ≠ v₁ := by intro h'; subst h'; omega
    have hu₁v₁ : u₁ ≠ v₁ := by intro h'; subst h'; omega
    have hu₀_pos1 : u₀ ∈ SuppPos x1 y := by
      rw [SuppPos, Finset.mem_filter]
      refine ⟨Finset.mem_univ u₀, ?_⟩
      simp only [x1, CharVec, hu₀₁, hu₀v₁, ↓reduceIte, sub_zero, add_zero]
      exact hu₀_lt
    obtain ⟨v₂, hv₂_neg1, hIH⟩ := ih _ hlt1 x1 y rfl hx1 hy u₀ hu₀_pos1
    have hv₂_ne_u₁ : v₂ ≠ u₁ := by
      simp only [SuppNeg, Finset.mem_filter, Finset.mem_univ, true_and] at hv₂_neg1
      intro hvu
      subst hvu
      simp only [x1, CharVec, ↓reduceIte, hu₁v₁, add_zero] at hv₂_neg1
      omega
    have hv₂_neg : v₂ ∈ SuppNeg x y := by
      simp only [SuppNeg, Finset.mem_filter, Finset.mem_univ, true_and] at hv₂_neg1 ⊢
      by_cases hv₂v₁ : v₂ = v₁
      · subst hv₂v₁
        exact hv₁_lt
      · simp only [x1, CharVec, hv₂_ne_u₁, hv₂v₁, ↓reduceIte, sub_zero, add_zero] at hv₂_neg1
        exact hv₂_neg1
    have hv₂_lt : x v₂ < y v₂ := by simpa [SuppNeg] using hv₂_neg
    have hu₀v₂ : u₀ ≠ v₂ := by intro h'; subst h'; omega
    have hu₁v₂ : u₁ ≠ v₂ := hv₂_ne_u₁.symm
    let a : V → ℤ := fun w => x w - CharVec u₀ w - CharVec u₁ w + CharVec v₁ w + CharVec v₂ w
    have ha_eq : (fun w => x1 w - CharVec u₀ w + CharVec v₂ w) = a := by
      ext w; simp [x1, a]; ring
    rw [ha_eq] at hIH
    obtain ⟨ha, _⟩ := ne_top_of_add_le hIH hx1 hy
    have hstep : f x1 + f (fun w => x w - CharVec u₀ w + CharVec v₂ w) ≤ f a + f x := by
      rcases four_point_exchange h hx hu₀₁ hu₀v₁ hu₀v₂ hu₁v₁ hu₁v₂ ha with hbr1 | hbr2
      · obtain ⟨_, hx2⟩ := ne_top_of_add_le hbr1 ha hx
        have hv₂S : v₂ ∈ S := Finset.mem_filter.mpr ⟨hv₂_neg, hx2⟩
        have hsc : score v₂ ≤ score v₁ := hv₁_max v₂ hv₂S
        obtain ⟨hxu₀v₁, _⟩ := ne_top_of_add_le hbr1 ha hx
        have hxu₀v₂ : f (fun w => x w - CharVec u₀ w + CharVec v₂ w) ≠ ⊤ := by
          intro htop
          have hsc2 : score v₂ = ⊤ := by simp [score, htop]
          rw [hsc2, top_le_iff] at hsc
          have hsc1 : score v₁ ≠ ⊤ :=
            WithTop.add_ne_top.mpr ⟨hxu₀v₁, WithTop.coe_ne_top⟩
          exact hsc1 hsc
        have hscore_le :
            f x1 + f (fun w => x w - CharVec u₀ w + CharVec v₂ w) ≤
              f (fun w => x w - CharVec u₀ w + CharVec v₁ w) +
                f (fun w => x w - CharVec u₁ w + CharVec v₂ w) := by
          dsimp only [score] at hsc
          rw [← coe_untopD_of_ne_top hxu₀v₂, ← coe_untopD_of_ne_top hxu₀v₁] at hsc
          rw [← coe_untopD_of_ne_top hx1, ← coe_untopD_of_ne_top hxu₀v₂,
              ← coe_untopD_of_ne_top hxu₀v₁, ← coe_untopD_of_ne_top hx2]
          norm_cast at hsc ⊢
          linarith
        exact le_trans hscore_le hbr1
      · rw [add_comm] at hbr2
        exact hbr2
    exact ⟨v₂, hv₂_neg, cancel_middle_le hIH hstep hx1 hy hx⟩

theorem solution {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ) :
    MExchangeAxiom f ↔ ∀ p : V → ℝ, ∀ alpha : ℝ, QEXCw (LevelSet (LinearWeight f p) alpha) := by
  refine ⟨mexchange_imp_qexcw f, ?_⟩
  intro h x hx y hy u₀ hu₀
  exact qexcw_imp_mexchange_aux h (posDist x y) x y rfl hx hy u₀ hu₀
