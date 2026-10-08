-- Prove2me | solution 1 for CostScaling.StrongPoly.lemma_4_4_fixedArcs_strict
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T20:14:44.886879+00:00
-- url     : https://prove2.me/submissions/1b58999c-f3b9-44e3-9d60-6c4331b96de5

import Mathlib
import Definitions.Def_CostScaling_StrongPoly_IsEpsTight
import Definitions.Def_CostScaling_StrongPoly_fixedArcs



namespace CostScaling.StrongPoly

open CycleCanceling.MinMean

variable {V : Type*} [Fintype V] [DecidableEq V]

open Classical in
noncomputable def reachSet (E : Finset (V × V)) (g : V → V → ℝ) (w : V) : ℕ → Finset V
  | 0 => {w}
  | k + 1 => reachSet E g w k ∪ Finset.univ.filter
      (fun y => ∃ x ∈ reachSet E g w k, (x, y) ∈ E ∧ 0 < g x y)

lemma mem_reachSet_succ (E : Finset (V × V)) (g : V → V → ℝ) (w : V) (k : ℕ) (y : V) :
    y ∈ reachSet E g w (k + 1) ↔
      y ∈ reachSet E g w k ∨ ∃ x ∈ reachSet E g w k, (x, y) ∈ E ∧ 0 < g x y := by
  rw [reachSet]
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]

lemma reachSet_mono (E : Finset (V × V)) (g : V → V → ℝ) (w : V) (k : ℕ) :
    reachSet E g w k ⊆ reachSet E g w (k + 1) := by
  intro x hx
  simp only [reachSet]
  exact Finset.mem_union_left _ hx

lemma reachSet_stable (E : Finset (V × V)) (g : V → V → ℝ) (w : V) (k : ℕ)
    (h : reachSet E g w k = reachSet E g w (k + 1)) :
    reachSet E g w (k + 1) = reachSet E g w (k + 1 + 1) := by
  apply le_antisymm
  · exact reachSet_mono E g w (k + 1)
  · intro y hy
    rw [mem_reachSet_succ] at hy
    rcases hy with hy | ⟨x, hx, hxy⟩
    · exact hy
    · rw [mem_reachSet_succ]; right; rw [h]; exact ⟨x, hx, hxy⟩

lemma reachSet_dich (E : Finset (V × V)) (g : V → V → ℝ) (w : V) (k : ℕ) :
    k + 1 ≤ (reachSet E g w k).card ∨ reachSet E g w k = reachSet E g w (k + 1) := by
  induction k with
  | zero => left; simp [reachSet]
  | succ k ih =>
    by_cases h : reachSet E g w k = reachSet E g w (k + 1)
    · exact Or.inr (reachSet_stable E g w k h)
    · left
      have h1 : k + 1 ≤ (reachSet E g w k).card := by tauto
      have hs : reachSet E g w k ⊂ reachSet E g w (k + 1) :=
        lt_of_le_of_ne (reachSet_mono E g w k) h
      have := Finset.card_lt_card hs
      omega

lemma reachSet_bound (E : Finset (V × V)) (g : V → V → ℝ) (w : V) (D : ℝ) (q : V → ℝ)
    (hD : 0 ≤ D) (hstep : ∀ x y, (x, y) ∈ E → 0 < g x y → q y ≤ q x + D) (k : ℕ) :
    ∀ x ∈ reachSet E g w k, q x ≤ q w + k * D := by
  induction k with
  | zero => intro x hx; simp [reachSet] at hx; subst hx; simp
  | succ k ih =>
    intro y hy
    rw [mem_reachSet_succ] at hy
    rcases hy with hy | ⟨x, hx, hxy, hg⟩
    · have := ih y hy; push_cast; nlinarith
    · have := ih x hx; have := hstep x y hxy hg; push_cast; nlinarith

lemma cut_zero (N : CircNetwork V) (g : V → V → ℝ)
    (hanti : ∀ x y, (x, y) ∈ N.E → g x y = -g y x)
    (hcons : ∀ w, ∑ v ∈ Finset.univ.filter (fun v => (w, v) ∈ N.E), g v w = 0)
    (S : Finset V) (hclosed : ∀ x ∈ S, ∀ y, (x, y) ∈ N.E → 0 < g x y → y ∈ S) :
    ∀ x ∈ S, ∀ y, y ∉ S → (x, y) ∈ N.E → g x y = 0 := by
  classical
  set F : V → V → ℝ := fun x v => if (x, v) ∈ N.E then g v x else 0 with hF
  have h0 : ∑ x ∈ S, ∑ v, F x v = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    rw [← hcons x, Finset.sum_filter]
  have hsplit : ∑ x ∈ S, ∑ v, F x v = ∑ x ∈ S, ∑ v ∈ S, F x v + ∑ x ∈ S, ∑ v ∈ Sᶜ, F x v := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_add_sum_compl]
  have hanF : ∀ x v, F v x = -F x v := by
    intro x v
    simp only [hF]
    by_cases h : (x, v) ∈ N.E
    · have h' : (v, x) ∈ N.E := (N.symm x v).1 h
      rw [if_pos h, if_pos h', hanti x v h]; try ring
    · have h' : (v, x) ∉ N.E := fun h' => h ((N.symm v x).1 h')
      rw [if_neg h, if_neg h']; try ring
  have hT1 : ∑ x ∈ S, ∑ v ∈ S, F x v = 0 := by
    have : ∑ x ∈ S, ∑ v ∈ S, F x v = -∑ x ∈ S, ∑ v ∈ S, F x v := by
      conv_lhs => rw [Finset.sum_comm]
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl; intro x _
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl; intro v _
      exact hanF x v
    linarith
  have hT2 : ∑ x ∈ S, ∑ v ∈ Sᶜ, F x v = 0 := by linarith
  have hnn : ∀ x ∈ S, ∀ v ∈ Sᶜ, 0 ≤ F x v := by
    intro x hx v hv
    simp only [hF]
    split_ifs with h
    · have h1 : g x v ≤ 0 := by
        by_contra hc
        push_neg at hc
        exact (Finset.mem_compl.1 hv) (hclosed x hx v h hc)
      have := hanti x v h
      have h2 := hanti v x ((N.symm x v).1 h)
      linarith
    · exact le_rfl
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun x hx => Finset.sum_nonneg (hnn x hx))] at hT2
  intro x hx y hy hxy
  have h1 := hT2 x hx
  rw [Finset.sum_eq_zero_iff_of_nonneg (hnn x hx)] at h1
  have h2 := h1 y (Finset.mem_compl.2 hy)
  simp only [hF, if_pos hxy] at h2
  have := hanti x y hxy
  linarith

lemma w_mem_reachSet (E : Finset (V × V)) (g : V → V → ℝ) (w : V) (k : ℕ) :
    w ∈ reachSet E g w k := by
  induction k with
  | zero => simp [reachSet]
  | succ k ih => exact reachSet_mono E g w k ih

lemma rc_anti (N : CircNetwork V) (p : V → ℝ) (x y : V) (h : (x, y) ∈ N.E) :
    reducedCost N p y x = -reducedCost N p x y := by
  have := N.cost_antisymm x y h
  have h2 := N.cost_antisymm y x ((N.symm x y).1 h)
  unfold reducedCost; linarith

lemma step_bounds (N : CircNetwork V) (ε ε' : ℝ) (f : V → V → ℝ) (hf : IsCirculation N f)
    (p : V → ℝ) (hfp : IsEpsOptimalWrt N f ε p)
    (f' : V → V → ℝ) (hf' : IsCirculation N f') (p' : V → ℝ) (hp' : IsEpsOptimalWrt N f' ε' p')
    (x y : V) (hxy : (x, y) ∈ N.E) (hlt : f x y < f' x y) :
    -ε ≤ reducedCost N p x y ∧ reducedCost N p' x y ≤ ε' := by
  have hyx : (y, x) ∈ N.E := (N.symm x y).1 hxy
  constructor
  · apply hfp x y hxy
    have := hf'.1 x y hxy
    unfold resCap; linarith
  · have h1 := hf.2.1 x y hxy
    have h2 := hf'.2.1 x y hxy
    have h3 := hf.1 y x hyx
    have : 0 < resCap N f' y x := by unfold resCap; linarith
    have := hp' y x hyx this
    rw [rc_anti N p' x y hxy] at this
    linarith

lemma pos_case (N : CircNetwork V) (hvertices : 2 ≤ Fintype.card V)
    (ε ε' : ℝ) (hε : 0 < ε) (hε' : 0 ≤ ε')
    (f : V → V → ℝ) (hf : IsCirculation N f)
    (p : V → ℝ) (hfp : IsEpsOptimalWrt N f ε p)
    (f' : V → V → ℝ) (hf' : IsCirculation N f') (p' : V → ℝ) (hp' : IsEpsOptimalWrt N f' ε' p')
    (v w : V) (hvw : (v, w) ∈ N.E)
    (hcost : (Fintype.card V : ℝ) * (ε + ε') ≤ reducedCost N p v w) :
    f v w = f' v w := by
  have hwv : (w, v) ∈ N.E := (N.symm v w).1 hvw
  have hn2 : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hvertices
  rcases lt_trichotomy (f v w) (f' v w) with hlt | heq | hgt
  · exfalso
    obtain ⟨k, hk⟩ : ∃ k, Fintype.card V = k + 1 := ⟨Fintype.card V - 1, by omega⟩
    have hkR : (Fintype.card V : ℝ) = k + 1 := by exact_mod_cast hk
    set g : V → V → ℝ := fun x y => f' x y - f x y with hg
    have hanti : ∀ x y, (x, y) ∈ N.E → g x y = -g y x := by
      intro x y h
      simp only [hg]
      have := hf.2.1 x y h
      have := hf'.2.1 x y h
      linarith
    have hcons : ∀ w, ∑ v ∈ Finset.univ.filter (fun v => (w, v) ∈ N.E), g v w = 0 := by
      intro w
      simp only [hg]
      rw [Finset.sum_sub_distrib, hf.2.2 w, hf'.2.2 w]; ring
    set q : V → ℝ := fun x => p x - p' x with hq
    have hD : 0 ≤ ε + ε' := by linarith
    have hstep : ∀ x y, (x, y) ∈ N.E → 0 < g x y → q y ≤ q x + (ε + ε') := by
      intro x y hxy hpos
      have hlt' : f x y < f' x y := by simp only [hg] at hpos; linarith
      obtain ⟨h1, h2⟩ := step_bounds N ε ε' f hf p hfp f' hf' p' hp' x y hxy hlt'
      simp only [hq]
      unfold reducedCost at h1 h2
      linarith
    have hvS : v ∈ reachSet N.E g w k := by
      rcases reachSet_dich N.E g w k with h | h
      · have : reachSet N.E g w k = Finset.univ :=
          Finset.eq_univ_of_card _ (by have := Finset.card_le_univ (reachSet N.E g w k); omega)
        rw [this]; exact Finset.mem_univ _
      · by_contra hv
        have hclosed : ∀ x ∈ reachSet N.E g w k, ∀ y, (x, y) ∈ N.E → 0 < g x y →
            y ∈ reachSet N.E g w k := by
          intro x hx y hxy hpos
          rw [h, mem_reachSet_succ]
          right; exact ⟨x, hx, hxy, hpos⟩
        have := cut_zero N g hanti hcons _ hclosed w (w_mem_reachSet _ _ _ _) v hv hwv
        have h2 := hanti w v hwv
        simp only [hg] at this h2
        linarith
    have hb := reachSet_bound N.E g w (ε + ε') q hD hstep k v hvS
    have hpos : 0 < g v w := by simp only [hg]; linarith
    obtain ⟨h1, h2⟩ := step_bounds N ε ε' f hf p hfp f' hf' p' hp' v w hvw hlt
    simp only [hq] at hb
    unfold reducedCost at hcost h2
    rw [hkR] at hcost
    nlinarith
  · exact heq
  · exfalso
    have hlt : f w v < f' w v := by
      have := hf.2.1 v w hvw
      have := hf'.2.1 v w hvw
      linarith
    obtain ⟨h1, _⟩ := step_bounds N ε ε' f hf p hfp f' hf' p' hp' w v hwv hlt
    rw [rc_anti N p v w hvw] at h1
    nlinarith

theorem arc_fixed_core (N : CircNetwork V)
    (hvertices : 2 ≤ Fintype.card V)
    (harcs : Fintype.card V - 1 ≤ N.E.card)
    (ε ε' : ℝ) (hε : 0 < ε) (hε' : 0 ≤ ε')
    (f : V → V → ℝ) (hf : IsCirculation N f)
    (p : V → ℝ) (hfp : IsEpsOptimalWrt N f ε p)
    (v w : V) (hvw : (v, w) ∈ N.E)
    (hcost : (Fintype.card V : ℝ) * (ε + ε') ≤ |reducedCost N p v w|) :
    ∀ f' : V → V → ℝ, IsEpsOptimal N f' ε' → f v w = f' v w := by
  intro f' ⟨hf', _, p', hp'⟩
  have hwv : (w, v) ∈ N.E := (N.symm v w).1 hvw
  rcases le_abs'.1 hcost with h | h
  · have h' : (Fintype.card V : ℝ) * (ε + ε') ≤ reducedCost N p w v := by
      rw [rc_anti N p v w hvw]; linarith
    have := pos_case N hvertices ε ε' hε hε' f hf p hfp f' hf' p' hp' w v hwv h'
    have h1 := hf.2.1 v w hvw
    have h2 := hf'.2.1 v w hvw
    linarith
  · exact pos_case N hvertices ε ε' hε hε' f hf p hfp f' hf' p' hp' v w hvw h


lemma exists_pos_le {ι : Type*} (s : Finset ι) (φ : ι → ℝ) (h : ∀ i ∈ s, 0 < φ i) :
    ∃ d : ℝ, 0 < d ∧ ∀ i ∈ s, d ≤ φ i := by
  by_cases hne : s.Nonempty
  · obtain ⟨i0, hi0, hmin⟩ := Finset.exists_min_image s φ hne
    exact ⟨φ i0, h i0 hi0, hmin⟩
  · refine ⟨1, one_pos, ?_⟩
    intro i hi; exact absurd ⟨i, hi⟩ hne

lemma cycle_or_rank (R : V → V → Prop) :
    (∃ Z : Finset V, Z.Nonempty ∧ ∃ σ : V → V, (∀ z ∈ Z, σ z ∈ Z ∧ R z (σ z)) ∧ Set.InjOn σ Z) ∨
    (∃ h : V → ℕ, (∀ x, h x ≤ Fintype.card V) ∧ ∀ x y, R x y → h y < h x) := by
  classical
  by_cases hX : ∃ x, Relation.TransGen R x x
  · left
    obtain ⟨x0, hx0⟩ := hX
    have hsucc : ∀ x, ∃ y, (Relation.TransGen R x x → Relation.TransGen R y y ∧ R x y) := by
      intro x
      by_cases hx : Relation.TransGen R x x
      · obtain ⟨b, hb, hbx⟩ := Relation.TransGen.head'_iff.1 hx
        refine ⟨b, fun _ => ⟨?_, hb⟩⟩
        exact Relation.TransGen.tail'_iff.2 ⟨x, hbx, hb⟩
      · exact ⟨x, fun h => absurd h hx⟩
    choose s hs using hsucc
    have hit : ∀ k : ℕ, Relation.TransGen R (s^[k] x0) (s^[k] x0) := by
      intro k
      induction k with
      | zero => simpa using hx0
      | succ k ih => rw [Function.iterate_succ_apply']; exact (hs _ ih).1
    have hit2 : ∀ (x : V), Relation.TransGen R x x → ∀ k : ℕ, Relation.TransGen R (s^[k] x) (s^[k] x) := by
      intro x hx k
      induction k with
      | zero => simpa using hx
      | succ k ih => rw [Function.iterate_succ_apply']; exact (hs _ ih).1
    have hper : ∃ i m : ℕ, 0 < m ∧ s^[m] (s^[i] x0) = s^[i] x0 := by
      obtain ⟨i, j, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite (fun k : ℕ => s^[k] x0)
      rcases lt_or_gt_of_ne hne with h | h
      · refine ⟨i, j - i, by omega, ?_⟩
        rw [← Function.iterate_add_apply, show j - i + i = j by omega]
        exact heq.symm
      · refine ⟨j, i - j, by omega, ?_⟩
        rw [← Function.iterate_add_apply, show i - j + j = i by omega]
        exact heq
    obtain ⟨i, m, hm, hperiod⟩ := hper
    set x1 := s^[i] x0 with hx1
    have hT1 : Relation.TransGen R x1 x1 := hit i
    set Z : Finset V := (Finset.range m).image (fun k => s^[k] x1) with hZ
    have hmemZ : ∀ k, k < m → s^[k] x1 ∈ Z := fun k hk =>
      Finset.mem_image.2 ⟨k, Finset.mem_range.2 hk, rfl⟩
    have hmaps : ∀ z ∈ Z, s z ∈ Z := by
      intro z hz
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hz
      rw [Finset.mem_range] at hk
      rw [← Function.iterate_succ_apply' s k x1]
      by_cases hk1 : k + 1 < m
      · exact hmemZ _ hk1
      · have : k + 1 = m := by omega
        rw [Nat.succ_eq_add_one, this, hperiod]
        simpa using hmemZ 0 hm
    have himg : Z.image s = Z := by
      apply le_antisymm
      · intro y hy
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy
        exact hmaps z hz
      · intro y hy
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hy
        rw [Finset.mem_range] at hk
        rw [Finset.mem_image]
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · subst h0
          refine ⟨s^[m - 1] x1, hmemZ _ (by omega), ?_⟩
          rw [← Function.iterate_succ_apply' s (m - 1) x1, show (m - 1).succ = m by omega, hperiod]
          rfl
        · refine ⟨s^[k - 1] x1, hmemZ _ (by omega), ?_⟩
          rw [← Function.iterate_succ_apply' s (k - 1) x1, show (k - 1).succ = k by omega]
    refine ⟨Z, ⟨x1, by simpa using hmemZ 0 hm⟩, s, ?_, ?_⟩
    · intro z hz
      refine ⟨hmaps z hz, ?_⟩
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hz
      exact (hs _ (hit2 x1 hT1 k)).2
    · apply Finset.injOn_of_card_image_eq
      rw [himg]
  · right
    push_neg at hX
    refine ⟨fun x => (Finset.univ.filter (fun z => Relation.TransGen R x z)).card,
      fun x => Finset.card_le_univ _, ?_⟩
    intro x y hxy
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨y, ?_, ?_⟩
      · simp [Relation.TransGen.single hxy]
      · simp [hX y]
    · intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      exact Relation.TransGen.head hxy hz


lemma opt_mono (N : CircNetwork V) (f : V → V → ℝ) (a b : ℝ) (hab : a ≤ b)
    (h : IsEpsOptimal N f a) : IsEpsOptimal N f b := by
  obtain ⟨hf, ha, p, hp⟩ := h
  exact ⟨hf, le_trans ha hab, p, fun x y hxy hr => by have := hp x y hxy hr; linarith⟩

lemma mem_fixedArcs (N : CircNetwork V) (ε : ℝ) (a : V × V) :
    a ∈ fixedArcs N ε ↔ a ∈ N.E ∧ IsEpsFixed N ε a.1 a.2 := by
  simp only [fixedArcs, Finset.mem_filter]

lemma acyclic_not_tight (N : CircNetwork V) (ε : ℝ) (hε : 0 < ε)
    (f : V → V → ℝ) (hf : IsCirculation N f) (p : V → ℝ) (hfp : IsEpsOptimalWrt N f ε p)
    (h : V → ℕ) (hbd : ∀ x, h x ≤ Fintype.card V)
    (hh : ∀ x y, (x, y) ∈ N.E ∧ 0 < resCap N f x y ∧ reducedCost N p x y = -ε → h y < h x) :
    ∃ ε2, ε2 < ε ∧ IsEpsOptimal N f ε2 := by
  classical
  set B := N.E.filter (fun a => 0 < resCap N f a.1 a.2 ∧ reducedCost N p a.1 a.2 ≠ -ε) with hB
  obtain ⟨s, hs0, hs⟩ := exists_pos_le B (fun a => reducedCost N p a.1 a.2 + ε) (by
    intro a ha
    simp only [hB, Finset.mem_filter] at ha
    obtain ⟨hE, hres, hne⟩ := ha
    have := hfp a.1 a.2 hE hres
    have h2 : reducedCost N p a.1 a.2 + ε ≠ 0 := fun h0 => hne (by linarith)
    exact lt_of_le_of_ne (by linarith) (Ne.symm h2))
  set n : ℝ := (Fintype.card V : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  set θ : ℝ := min ε (s / (2 * (n + 1))) with hθ
  have hθ0 : 0 < θ := lt_min hε (by positivity)
  have hθε : θ ≤ ε := min_le_left _ _
  have hθs : θ * (2 * (n + 1)) ≤ s := (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
  refine ⟨ε - θ, by linarith, hf, by linarith, fun x => p x + θ * (h x : ℝ), ?_⟩
  intro x y hxy hres
  have hrc : reducedCost N (fun x => p x + θ * (h x : ℝ)) x y
      = reducedCost N p x y + θ * ((h x : ℝ) - h y) := by
    unfold reducedCost; ring
  rw [hrc]
  by_cases hA : reducedCost N p x y = -ε
  · have h1 := hh x y ⟨hxy, hres, hA⟩
    have h2 : (h y : ℝ) + 1 ≤ h x := by exact_mod_cast h1
    nlinarith
  · have hmem : (x, y) ∈ B := by
      simp only [hB, Finset.mem_filter]; exact ⟨hxy, hres, hA⟩
    have h1 := hs (x, y) hmem
    simp only at h1
    have hy : (h y : ℝ) ≤ n := by rw [hn]; exact_mod_cast hbd y
    have hx0 : (0 : ℝ) ≤ h x := Nat.cast_nonneg _
    have : θ * ((h x : ℝ) - h y) ≥ -(θ * n) := by
      nlinarith [mul_le_mul_of_nonneg_left hy hθ0.le, mul_nonneg hθ0.le hx0]
    nlinarith

lemma cycle_sum (N : CircNetwork V) (ε : ℝ) (f : V → V → ℝ) (p : V → ℝ)
    (Z : Finset V) (hne : Z.Nonempty) (σ : V → V)
    (hZσ : ∀ z ∈ Z, σ z ∈ Z ∧ reducedCost N p z (σ z) = -ε) (hinj : Set.InjOn σ Z)
    (p' : V → ℝ) : ∃ z ∈ Z, reducedCost N p' z (σ z) ≤ -ε := by
  have himg : Z.image σ = Z := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy
      exact (hZσ z hz).1
    · rw [Finset.card_image_of_injOn hinj]
  have hsum : ∀ F : V → ℝ, ∑ z ∈ Z, F (σ z) = ∑ z ∈ Z, F z := by
    intro F
    rw [← Finset.sum_image hinj, himg]
  apply Finset.exists_le_of_sum_le hne
  have e1 : ∑ z ∈ Z, reducedCost N p' z (σ z) = ∑ z ∈ Z, reducedCost N p z (σ z) := by
    have : ∀ z, reducedCost N p' z (σ z) = reducedCost N p z (σ z)
        + ((p' z - p z) - ((p' - p) (σ z))) := by
      intro z; unfold reducedCost; simp only [Pi.sub_apply]; ring
    simp only [this]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have h3 := hsum (p' - p)
    simp only [Pi.sub_apply] at h3 ⊢
    rw [h3]; simp
  rw [e1]
  exact le_of_eq (Finset.sum_congr rfl (fun z hz => (hZσ z hz).2))


lemma cycle_not_fixed (N : CircNetwork V) (ε : ℝ) (hε : 0 < ε)
    (f : V → V → ℝ) (hf : IsCirculation N f) (p : V → ℝ) (hfp : IsEpsOptimalWrt N f ε p)
    (Z : Finset V) (σ : V → V)
    (hZσ : ∀ z ∈ Z, σ z ∈ Z ∧ (z, σ z) ∈ N.E ∧ 0 < resCap N f z (σ z) ∧
      reducedCost N p z (σ z) = -ε)
    (hinj : Set.InjOn σ Z) :
    ∀ z ∈ Z, ∃ f2 : V → V → ℝ, IsEpsOptimal N f2 ε ∧ f2 z (σ z) ≠ f z (σ z) := by
  classical
  have himg : Z.image σ = Z := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy
      exact (hZσ z hz).1
    · rw [Finset.card_image_of_injOn hinj]
  have hsum : ∀ F : V → ℝ, ∑ z ∈ Z, F (σ z) = ∑ z ∈ Z, F z := by
    intro F
    rw [← Finset.sum_image hinj, himg]
  obtain ⟨δ, hδ0, hδ⟩ := exists_pos_le Z (fun z => resCap N f z (σ z))
    (fun z hz => (hZσ z hz).2.2.1)
  obtain ⟨H, hH⟩ : ∃ H : V → V → ℝ, ∀ x y, H x y =
      (if x ∈ Z ∧ y = σ x then (1 : ℝ) else 0) - (if y ∈ Z ∧ x = σ y then (1 : ℝ) else 0) :=
    ⟨_, fun _ _ => rfl⟩
  have hHanti : ∀ x y, H y x = -H x y := by
    intro x y; rw [hH, hH]; ring
  have hHle : ∀ x y, H x y ≤ 1 := by
    intro x y; rw [hH]; split_ifs <;> norm_num
  have hHpos : ∀ x y, 0 < H x y → x ∈ Z ∧ y = σ x := by
    intro x y h
    by_contra hc
    rw [hH, if_neg hc] at h
    split_ifs at h <;> linarith
  have hHneg : ∀ x y, H x y < 0 → y ∈ Z ∧ x = σ y := by
    intro x y h
    by_contra hc
    rw [hH, if_neg hc] at h
    split_ifs at h <;> linarith
  have hHE : ∀ x y, H x y ≠ 0 → (y, x) ∈ N.E := by
    intro x y h
    rcases lt_or_gt_of_ne h with h1 | h1
    · obtain ⟨hy, rfl⟩ := hHneg x y h1
      exact (hZσ y hy).2.1
    · obtain ⟨hx, rfl⟩ := hHpos x y h1
      exact (N.symm _ _).1 (hZσ x hx).2.1
  have hHsum : ∀ w, ∑ v, H v w = 0 := by
    intro w
    simp only [hH]
    rw [Finset.sum_sub_distrib]
    have e1 : ∑ v, (if v ∈ Z ∧ w = σ v then (1 : ℝ) else 0)
        = ∑ v ∈ Z, (if w = σ v then (1 : ℝ) else 0) := by
      rw [← Finset.sum_subset (Finset.subset_univ Z) (fun v _ hv => by simp [hv])]
      apply Finset.sum_congr rfl
      intro v hv; simp [hv]
    have e2 : ∑ v ∈ Z, (if w = σ v then (1 : ℝ) else 0)
        = if w ∈ Z then (1 : ℝ) else 0 := by
      have := hsum (fun y => if w = y then (1 : ℝ) else 0)
      rw [this]
      simp [Finset.sum_ite_eq]
    have e3 : ∑ v, (if w ∈ Z ∧ v = σ w then (1 : ℝ) else 0) = if w ∈ Z then (1 : ℝ) else 0 := by
      by_cases hw : w ∈ Z
      · simp [hw]
      · simp [hw]
    rw [e1, e2, e3]; ring
  have hHself : ∀ z ∈ Z, H z (σ z) = 1 := by
    intro z hz
    rw [hH, if_pos ⟨hz, rfl⟩]
    have : ¬ (σ z ∈ Z ∧ z = σ (σ z)) := by
      rintro ⟨h1, h2⟩
      obtain ⟨_, hE1, _, hr1⟩ := hZσ z hz
      obtain ⟨_, hE2, _, hr2⟩ := hZσ (σ z) h1
      rw [← h2] at hr2
      rw [rc_anti N p z (σ z) hE1] at hr2
      linarith
    rw [if_neg this]; ring
  intro z0 hz0
  refine ⟨fun x y => f x y + δ * H x y, ?_, ?_⟩
  · refine ⟨⟨?_, ?_, ?_⟩, hε.le, p, ?_⟩
    · intro x y hxy
      by_cases ha : x ∈ Z ∧ y = σ x
      · obtain ⟨hx, rfl⟩ := ha
        have h1 := hδ x hx
        have h2 := hHle x (σ x)
        unfold resCap at h1
        nlinarith
      · have : H x y ≤ 0 := by
          by_contra hc
          push_neg at hc
          exact ha (hHpos x y hc)
        have := hf.1 x y hxy
        nlinarith
    · intro x y hxy
      have := hf.2.1 x y hxy
      have := hHanti x y
      simp only
      rw [hHanti x y]; linarith
    · intro w
      have hfilter : ∑ v ∈ Finset.univ.filter (fun v => (w, v) ∈ N.E), H v w = 0 := by
        rw [Finset.sum_filter]
        refine Eq.trans (Finset.sum_congr rfl ?_) (hHsum w)
        intro v _
        by_cases hv : (w, v) ∈ N.E
        · rw [if_pos hv]
        · rw [if_neg hv]
          by_contra hne
          exact hv (hHE v w (Ne.symm hne))
      simp only
      rw [Finset.sum_add_distrib, hf.2.2 w, ← Finset.mul_sum, hfilter]; ring
    · intro x y hxy hres
      by_cases hr : 0 < resCap N f x y
      · exact hfp x y hxy hr
      · have hneg : H x y < 0 := by
          by_contra hc
          push_neg at hc
          unfold resCap at hres hr
          have := mul_nonneg hδ0.le hc
          simp only at hres
          apply hr
          linarith
        obtain ⟨hy, rfl⟩ := hHneg x y hneg
        obtain ⟨_, hE, _, hrc⟩ := hZσ y hy
        rw [rc_anti N p y (σ y) hE, hrc]
        linarith
  · simp only
    rw [hHself z0 hz0]
    intro h
    linarith


theorem fixedArcs_strict_core (N : CircNetwork V)
    (hvertices : 2 ≤ Fintype.card V)
    (harcs : Fintype.card V - 1 ≤ N.E.card)
    (ε ε' : ℝ) (hε : 0 < ε) (hε' : 0 ≤ ε')
    (hscale : ε' ≤ ε / (2 * (Fintype.card V : ℝ)))
    (htight : ∃ f : V → V → ℝ, IsEpsTight N f ε) :
    fixedArcs N ε ⊂ fixedArcs N ε' := by
  obtain ⟨f, ⟨hf, _, p, hfp⟩, hnot⟩ := htight
  have hn2 : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hvertices
  have hε'ε : ε' ≤ ε := by
    have : ε / (2 * (Fintype.card V : ℝ)) ≤ ε := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have hsub : fixedArcs N ε ⊆ fixedArcs N ε' := by
    intro a ha
    rw [mem_fixedArcs] at ha ⊢
    refine ⟨ha.1, fun g g' hg hg' => ha.2 g g' ?_ ?_⟩
    · exact opt_mono N g ε' ε hε'ε hg
    · exact opt_mono N g' ε' ε hε'ε hg'
  rw [Finset.ssubset_iff_of_subset hsub]
  rcases cycle_or_rank (fun x y => (x, y) ∈ N.E ∧ 0 < resCap N f x y ∧
      reducedCost N p x y = -ε) with ⟨Z, hne, σ, hσ, hinj⟩ | ⟨h, hbd, hh⟩
  · have hZσ : ∀ z ∈ Z, σ z ∈ Z ∧ (z, σ z) ∈ N.E ∧ 0 < resCap N f z (σ z) ∧
        reducedCost N p z (σ z) = -ε := fun z hz => ⟨(hσ z hz).1, (hσ z hz).2⟩
    have hnf := cycle_not_fixed N ε hε f hf p hfp Z σ hZσ hinj
    have hex : ∃ z ∈ Z, IsEpsFixed N ε' z (σ z) := by
      by_cases hex : ∃ f', IsEpsOptimal N f' ε'
      · obtain ⟨f', hf'opt⟩ := hex
        obtain ⟨hf', _, p', hp'⟩ := hf'opt
        obtain ⟨z, hz, hle⟩ := cycle_sum N ε f p Z hne σ
          (fun z hz => ⟨(hZσ z hz).1, (hZσ z hz).2.2.2⟩) hinj p'
        refine ⟨z, hz, ?_⟩
        have hε'' : 0 < ε / (2 * (Fintype.card V : ℝ)) := by positivity
        have hp'' : IsEpsOptimalWrt N f' (ε / (2 * (Fintype.card V : ℝ))) p' := by
          intro x y hxy hr
          have := hp' x y hxy hr
          linarith
        have hcost : (Fintype.card V : ℝ) * (ε / (2 * (Fintype.card V : ℝ)) + ε')
            ≤ |reducedCost N p' z (σ z)| := by
          have h1 : (Fintype.card V : ℝ) * (ε / (2 * (Fintype.card V : ℝ)))= ε / 2 := by
            field_simp
          have h2 : (Fintype.card V : ℝ) * ε' ≤ ε / 2 := by
            have := mul_le_mul_of_nonneg_left hscale (by positivity : (0:ℝ) ≤ Fintype.card V)
            have h3 : (Fintype.card V : ℝ) * (ε / (2 * (Fintype.card V : ℝ))) = ε / 2 := h1
            linarith
          have h4 := neg_le_abs (reducedCost N p' z (σ z))
          nlinarith
        have key := arc_fixed_core N hvertices harcs _ ε' hε'' hε' f' hf' p' hp'' z (σ z)
          (hZσ z hz).2.1 hcost
        intro g g' hg hg'
        exact (key g hg).symm.trans (key g' hg')
      · push_neg at hex
        obtain ⟨z, hz⟩ := hne
        exact ⟨z, hz, fun g g' hg _ => absurd hg (hex g)⟩
    obtain ⟨z, hz, hfix⟩ := hex
    refine ⟨(z, σ z), ?_, ?_⟩
    · rw [mem_fixedArcs]; exact ⟨(hZσ z hz).2.1, hfix⟩
    · rw [mem_fixedArcs]
      rintro ⟨_, hfx⟩
      obtain ⟨f2, hf2, hne2⟩ := cycle_not_fixed N ε hε f hf p hfp Z σ hZσ hinj z hz
      exact hne2 (hfx f2 f hf2 ⟨hf, ‹_›, p, hfp⟩)
  · exfalso
    obtain ⟨ε2, hlt, hopt2⟩ := acyclic_not_tight N ε hε f hf p hfp h hbd hh
    exact hnot ε2 hlt hopt2

end CostScaling.StrongPoly

open CostScaling.StrongPoly
open CycleCanceling.MinMean
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem solution (N : CircNetwork V)
    (hvertices : 2 ≤ Fintype.card V)
    (harcs : Fintype.card V - 1 ≤ N.E.card)
    (ε ε' : ℝ) (hε : 0 < ε) (hε' : 0 ≤ ε')
    (hscale : ε' ≤ ε / (2 * (Fintype.card V : ℝ)))
    (htight : ∃ f : V → V → ℝ, IsEpsTight N f ε) :
    fixedArcs N ε ⊂ fixedArcs N ε' := by
  exact fixedArcs_strict_core N hvertices harcs ε ε' hε hε' hscale htight
