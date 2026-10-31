-- Prove2me | solution 1 for FairRentFPTAS.Approx.ineq_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T12:34:32.86977+00:00
-- url     : https://prove2.me/submissions/41cbffde-95a0-437c-8557-0e9d18b29ace

import Mathlib
import Definitions.Def_FairRentFPTAS_Approx_Model
import Theorems.Thm_FairRentFPTAS_Approx_lemma_4

open FairRentFPTAS.Approx

namespace FRFI3Aux

/-- `drop` vanishes at a point below every start of a sorted list. -/
lemma drop_eq_zero (x : ℝ) : ∀ (l : List (ℝ × ℝ)), (l.map Prod.fst).Pairwise (· < ·) →
    (∀ e ∈ l, x ≤ e.1) → PLFun.drop l x = 0 := by
  intro l
  induction l with
  | nil => intro _ _; simp [PLFun.drop]
  | cons e t ih =>
    intro hs hx
    cases t with
    | nil =>
      have := hx e (by simp)
      simp [PLFun.drop, max_eq_right this]
    | cons e' t' =>
      have hs' : ((e' :: t').map Prod.fst).Pairwise (· < ·) := (List.pairwise_cons.mp hs).2
      have hee' : e.1 < e'.1 := (List.pairwise_cons.mp hs).1 e'.1 (by simp)
      have := hx e (by simp)
      simp only [PLFun.drop]
      rw [ih hs' (fun y hy => hx y (List.mem_cons_of_mem _ hy)), max_eq_right this,
        min_eq_left hee'.le]
      ring

lemma starts_nonneg (f : PLFun) (hf : f.WF) : ∀ e ∈ f.pieces, 0 ≤ e.1 := by
  obtain ⟨hne, hhead, hsort, _⟩ := hf
  cases h : f.pieces with
  | nil => exact absurd h hne
  | cons e t =>
    rw [h] at hhead hsort
    simp at hhead
    intro y hy
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · rw [hhead]
    · have := (List.pairwise_cons.mp (by simpa using hsort)).1 y.1 (List.mem_map_of_mem hy)
      rw [hhead] at this; exact this.le

lemma eval_zero (f : PLFun) (hf : f.WF) : f.eval 0 = f.base := by
  unfold PLFun.eval
  simp only [lt_irrefl, if_false]
  rw [drop_eq_zero 0 _ hf.2.2.1 (starts_nonneg f hf)]; ring

lemma firstSlope_pos (f : PLFun) (hf : f.WF) : 0 < f.firstSlope := by
  unfold PLFun.firstSlope
  cases h : f.pieces with
  | nil => exact absurd h hf.1
  | cons e t =>
    simp only [List.headD_cons]
    exact hf.2.2.2 e (by rw [h]; simp)

lemma M_pos {n : ℕ} (hn : 1 ≤ n) (J : Instance n) (hJ : Standing J) (M : ℝ)
    (hM : IsThreshold J M) : 0 < M := by
  have a0 : Fin n := ⟨0, by omega⟩
  have h := hM a0 a0 a0
  rw [eval_zero _ (hJ a0 a0)] at h
  by_contra hle
  push_neg at hle
  rcases hle.lt_or_eq with hlt | heq
  · unfold PLFun.eval at h
    rw [if_pos hlt] at h
    have := firstSlope_pos _ (hJ a0 a0)
    nlinarith
  · subst heq
    rw [eval_zero _ (hJ a0 a0)] at h
    exact lt_irrefl _ h

/-- last slope strictly below `x`, defaulting to the head slope. -/
noncomputable def gS (l : List (ℝ × ℝ)) (x : ℝ) : ℝ :=
  (((l.filter (fun e => decide (e.1 < x))).getLast?).map Prod.snd).getD (l.headD (0, 0)).2

lemma getLast?_cons_ne (e : ℝ × ℝ) (L : List (ℝ × ℝ)) (h : L ≠ []) :
    (e :: L).getLast? = L.getLast? := by
  cases L with
  | nil => exact absurd rfl h
  | cons b l => simp

lemma getD_indep (L : List (ℝ × ℝ)) (h : L ≠ []) (d d' : ℝ) :
    (Option.map Prod.snd L.getLast?).getD d = (Option.map Prod.snd L.getLast?).getD d' := by
  cases hL : L.getLast? with
  | none => exact absurd (List.getLast?_eq_none_iff.mp hL) h
  | some z => rfl

lemma filter_nil_of_le (l : List (ℝ × ℝ)) (x : ℝ) (h : ∀ e ∈ l, x ≤ e.1) :
    l.filter (fun e => decide (e.1 < x)) = [] := by
  rw [List.filter_eq_nil_iff]
  intro e he
  simpa using h e he

lemma gS_const (x y : ℝ) (hxy : x < y) : ∀ l : List (ℝ × ℝ), (l.map Prod.fst).Pairwise (· < ·) →
    (∀ e e', [e, e'] <:+: l → x ≤ e'.1 → e'.1 < y → e.2 = e'.2) → gS l x = gS l y := by
  intro l
  induction l with
  | nil => intro _ _; rfl
  | cons e t ih =>
    intro hs hc
    have hs' : (t.map Prod.fst).Pairwise (· < ·) := (List.pairwise_cons.mp hs).2
    have hlt : ∀ z ∈ t, e.1 < z.1 := fun z hz =>
      (List.pairwise_cons.mp hs).1 z.1 (List.mem_map_of_mem hz)
    have hc' : ∀ a b, [a, b] <:+: t → x ≤ b.1 → b.1 < y → a.2 = b.2 := fun a b hab =>
      hc a b (hab.trans (List.infix_cons (List.infix_refl t)))
    have IH := ih hs' hc'
    unfold gS at IH ⊢
    simp only [List.headD_cons] at IH ⊢
    by_cases hey : y ≤ e.1
    · rw [filter_nil_of_le (e :: t) x, filter_nil_of_le (e :: t) y]
      · intro z hz; rcases List.mem_cons.mp hz with rfl | hz
        · exact hey
        · linarith [hlt z hz]
      · intro z hz; rcases List.mem_cons.mp hz with rfl | hz
        · linarith
        · linarith [hlt z hz]
    push_neg at hey
    have hFyE : (e :: t).filter (fun e => decide (e.1 < y)) = e :: t.filter (fun e => decide (e.1 < y)) :=
      List.filter_cons_of_pos (by simpa using hey)
    rw [hFyE]
    cases t with
    | nil =>
      by_cases hex : e.1 < x
      · have hFxE : [e].filter (fun e => decide (e.1 < x)) = [e] :=
          List.filter_cons_of_pos (by simpa using hex)
        rw [hFxE]; simp
      · have hFxE : [e].filter (fun e => decide (e.1 < x)) = [] :=
          List.filter_cons_of_neg (by simpa using hex)
        rw [hFxE]; simp
    | cons e' t' =>
      have hee' := hlt e' (by simp)
      have hcee' : x ≤ e'.1 → e'.1 < y → e.2 = e'.2 := hc e e' (List.prefix_iff_eq_take.mpr
        (by simp)).isInfix
      simp only [List.headD_cons] at IH
      set Fx := (e' :: t').filter (fun e => decide (e.1 < x)) with hFx_def
      set Fy := (e' :: t').filter (fun e => decide (e.1 < y)) with hFy_def
      -- Fy empty iff e' ≥ y
      have hFy_nil : Fy = [] → y ≤ e'.1 := by
        intro h
        by_contra h'; push_neg at h'
        have : e' ∈ Fy := List.mem_filter.mpr ⟨by simp, by simpa using h'⟩
        rw [h] at this; simp at this
      have hFx_nil : Fx = [] → x ≤ e'.1 := by
        intro h
        by_contra h'; push_neg at h'
        have : e' ∈ Fx := List.mem_filter.mpr ⟨by simp, by simpa using h'⟩
        rw [h] at this; simp at this
      have hFx_of : x ≤ e'.1 → Fx = [] := by
        intro h
        apply filter_nil_of_le
        intro z hz; rcases List.mem_cons.mp hz with rfl | hz
        · exact h
        · linarith [(List.pairwise_cons.mp hs').1 z.1 (List.mem_map_of_mem hz)]
      have hFy_of : y ≤ e'.1 → Fy = [] := by
        intro h
        apply filter_nil_of_le
        intro z hz; rcases List.mem_cons.mp hz with rfl | hz
        · exact h
        · linarith [(List.pairwise_cons.mp hs').1 z.1 (List.mem_map_of_mem hz)]
      by_cases hex : e.1 < x
      · have hFxE : (e :: e' :: t').filter (fun e => decide (e.1 < x)) = e :: Fx :=
          List.filter_cons_of_pos (by simpa using hex)
        rw [hFxE]
        by_cases hFx : Fx = []
        · by_cases hFy : Fy = []
          · rw [hFx, hFy]
          · rw [hFx, getLast?_cons_ne _ _ hFy]
            rw [hFx] at IH
            simp only [List.getLast?_nil, Option.map_none, Option.getD_none] at IH
            rw [getD_indep Fy hFy e.2 e'.2, ← IH]
            simp only [List.getLast?_singleton, Option.map_some, Option.getD_some]
            apply hcee' (hFx_nil hFx)
            by_contra h; push_neg at h
            exact hFy (hFy_of h)
        · have hFy : Fy ≠ [] := by
            intro hFy; apply hFx; apply hFx_of; linarith [hFy_nil hFy]
          rw [getLast?_cons_ne _ _ hFx, getLast?_cons_ne _ _ hFy]
          rw [getD_indep Fx hFx e.2 e'.2, getD_indep Fy hFy e.2 e'.2]
          exact IH
      · have hFxE : (e :: e' :: t').filter (fun e => decide (e.1 < x)) = Fx :=
          List.filter_cons_of_neg (by simpa using hex)
        rw [hFxE]
        push_neg at hex
        have hFx : Fx = [] := hFx_of (by linarith)
        rw [hFx]
        by_cases hFy : Fy = []
        · rw [hFy]; simp
        · rw [getLast?_cons_ne _ _ hFy]
          rw [hFx] at IH
          simp only [List.getLast?_nil, Option.map_none, Option.getD_none] at IH
          rw [getD_indep Fy hFy e.2 e'.2, ← IH]
          simp only [List.getLast?_nil, Option.map_none, Option.getD_none]
          apply hcee' (by linarith)
          by_contra h; push_neg at h
          exact hFy (hFy_of h)

lemma mem_zip_of_infix (e e' : ℝ × ℝ) : ∀ l : List (ℝ × ℝ), [e, e'] <:+: l →
    (e, e') ∈ l.zip l.tail := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons a l ih =>
    intro h
    rcases List.infix_cons_iff.mp h with h | h
    · obtain ⟨rest, hrest⟩ := h
      simp only [List.cons_append] at hrest
      rw [← hrest]; simp
    · have := ih h
      cases l with
      | nil => simp at this
      | cons b l' => simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons]; right; exact this

lemma kink_mem (f : PLFun) (e e' : ℝ × ℝ) (h : [e, e'] <:+: f.pieces) (hne : e.2 ≠ e'.2) :
    e'.1 ∈ f.kinks := by
  unfold PLFun.kinks
  rw [List.mem_filterMap]
  exact ⟨(e, e'), mem_zip_of_infix e e' _ h, by simp [hne]⟩

lemma hat_sorted (M : ℝ) (f : PLFun) (hf : f.WF) :
    ((extendQL M f).pieces.map Prod.fst).Pairwise (· < ·) := by
  unfold extendQL
  simp only [List.map_append, List.map_cons, List.map_nil]
  rw [List.pairwise_append]
  refine ⟨?_, by simp, ?_⟩
  · exact hf.2.2.1.sublist ((List.filter_sublist).map _)
  · intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst hb
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp ha
    have := (List.mem_filter.mp hz).2
    simpa using this

lemma leftSlope_eq_gS (f : PLFun) (x : ℝ) : f.leftSlope x = gS f.pieces x := rfl

lemma leftSlope_mem (M : ℝ) (f : PLFun) (x : ℝ) :
    ∃ e ∈ (extendQL M f).pieces, (extendQL M f).leftSlope x = e.2 := by
  unfold PLFun.leftSlope
  cases h : ((extendQL M f).pieces.filter (fun e => decide (e.1 < x))).getLast? with
  | some e =>
    refine ⟨e, ?_, by simp⟩
    have := List.mem_of_getLast? h
    exact (List.mem_filter.mp this).1
  | none =>
    simp only [Option.map_none, Option.getD_none, PLFun.firstSlope]
    cases hp : (extendQL M f).pieces with
    | nil => unfold extendQL at hp; simp at hp
    | cons e t => exact ⟨e, by simp, by simp⟩

/-- equal linear domains give equal left slopes. -/
lemma leftSlope_same {n : ℕ} (M : ℝ) (J : Instance n) (hJ : Standing J) (q q' : Fin n → ℝ)
    (hL : domL (hatInst M J) q = domL (hatInst M J) q')
    (hU : domU (hatInst M J) q = domU (hatInst M J) q') (a r : Fin n) :
    ((hatInst M J).v a r).leftSlope (q r) = ((hatInst M J).v a r).leftSlope (q' r) := by
  classical
  set Ĵ := hatInst M J
  -- no boundary point lies between `q r` and `q' r`
  have key : ∀ x y : ℝ, x < y → domU Ĵ q r = domU Ĵ q' r → x = q r ∨ x = q' r →
      y = q r ∨ y = q' r → (domL Ĵ q r = domL Ĵ q' r) → ∀ b ∈ bd Ĵ r, ¬ (x ≤ b ∧ b < y) := by
    intro x y hxy hU' hx hy hL' b hb ⟨h1, h2⟩
    -- domU at x is ≤ b, domU at y is ≥ y > b
    have hUx : domU Ĵ (fun s => if s = r then x else q r) r ≤ (b : WithTop ℝ) := by
      unfold domU; simp only [if_pos rfl]
      exact Finset.min_le (Finset.mem_filter.mpr ⟨hb, h1⟩)
    have hUy : ((y : ℝ) : WithTop ℝ) ≤ domU Ĵ (fun s => if s = r then y else q r) r := by
      unfold domU; simp only [if_pos rfl]
      apply Finset.le_min
      intro c hc; exact WithTop.coe_le_coe.mpr (Finset.mem_filter.mp hc).2
    have eU : ∀ z, z = q r ∨ z = q' r → domU Ĵ (fun s => if s = r then z else q r) r = domU Ĵ q r := by
      intro z hz
      rcases hz with rfl | rfl
      · unfold domU; simp
      · rw [hU']; unfold domU; simp
    rw [eU x hx] at hUx
    rw [eU y hy] at hUy
    have := le_trans hUy hUx
    have := WithTop.coe_le_coe.mp this
    linarith
  have hLr : domL Ĵ q r = domL Ĵ q' r := by rw [hL]
  have hUr : domU Ĵ q r = domU Ĵ q' r := by rw [hU]
  show (extendQL M (J.v a r)).leftSlope (q r) = (extendQL M (J.v a r)).leftSlope (q' r)
  rw [leftSlope_eq_gS, leftSlope_eq_gS]
  have hs := hat_sorted M (J.v a r) (hJ a r)
  have hcond : ∀ x y, x < y → (x = q r ∨ x = q' r) → (y = q r ∨ y = q' r) →
      ∀ e e', [e, e'] <:+: (extendQL M (J.v a r)).pieces → x ≤ e'.1 → e'.1 < y → e.2 = e'.2 := by
    intro x y hxy hx hy e e' hin h1 h2
    by_contra hne
    have hk := kink_mem _ e e' hin hne
    have hb : e'.1 ∈ bd Ĵ r := by
      unfold bd
      apply Finset.mem_insert_of_mem
      rw [Finset.mem_biUnion]
      exact ⟨a, Finset.mem_univ _, List.mem_toFinset.mpr hk⟩
    exact key x y hxy hUr hx hy hLr _ hb ⟨h1, h2⟩
  rcases lt_trichotomy (q r) (q' r) with h | h | h
  · exact gS_const _ _ h _ hs (hcond _ _ h (Or.inl rfl) (Or.inr rfl))
  · rw [h]
  · exact (gS_const _ _ h _ hs (hcond _ _ h (Or.inr rfl) (Or.inl rfl))).symm

end FRFI3Aux

open FRFI3Aux in
theorem solution {n : ℕ} (hn : 1 ≤ n) (J : Instance n) (ε β M : ℝ) (hJ : Standing J)
    (hε : 0 < ε) (hε1 : ε < 1) (hpow : PowersProp ε J)
    (hβ : ∀ a r, ∀ e ∈ (J.v a r).pieces, |Real.log e.2| ≤ β) (hM : IsThreshold J M)
    (T : ℕ) (π : ℕ → Equiv.Perm (Fin n)) (p : ℕ → Fin n → ℝ) (hrun : IsRun J M T π p)
    (i j : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) (hjT : j + 1 ≤ T)
    (hdom : ∀ k, i ≤ k → k ≤ j →
      domL (hatInst M J) (p k) = domL (hatInst M J) (p (i - 1)) ∧
        domU (hatInst M J) (p k) = domU (hatInst M J) (p (i - 1))) :
    ((j + 1 - i : ℕ) : ℝ) ≤ 6 * β * n / ε := by
  classical
  set Ĵ := hatInst M J
  have hβ0 : 0 ≤ β := by
    have a0 : Fin n := ⟨0, by omega⟩
    obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ (hJ a0 a0).1
    exact le_trans (abs_nonneg _) (hβ a0 a0 e he)
  set Lg := Real.log (1 + ε) with hLg
  have hLg0 : 0 < Lg := Real.log_pos (by linarith)
  -- every left slope of `Ĵ` is a power of `1+ε` with bounded logarithm
  have hslope : ∀ a r x, ∃ k : ℤ, (Ĵ.v a r).leftSlope x = (1 + ε) ^ k ∧
      |Real.log ((Ĵ.v a r).leftSlope x)| ≤ β := by
    intro a r x
    obtain ⟨e, he, hel⟩ := leftSlope_mem M (J.v a r) x
    change (extendQL M (J.v a r)).leftSlope x = _ at hel
    show ∃ k : ℤ, (extendQL M (J.v a r)).leftSlope x = (1 + ε) ^ k ∧
      |Real.log ((extendQL M (J.v a r)).leftSlope x)| ≤ β
    rw [hel]
    unfold extendQL at he
    simp only [List.mem_append, List.mem_filter, List.mem_singleton] at he
    rcases he with ⟨he, _⟩ | rfl
    · obtain ⟨k, hk⟩ := hpow a r e he
      exact ⟨k, hk, hβ a r e he⟩
    · exact ⟨0, by simp, by simpa using hβ0⟩
  choose kk hkk hkb using hslope
  -- the reference price vector `p i`
  have hdom' : ∀ k, i - 1 ≤ k → k ≤ j →
      domL Ĵ (p k) = domL Ĵ (p i) ∧ domU Ĵ (p k) = domU Ĵ (p i) := by
    intro k hk1 hk2
    have hi' := hdom i le_rfl hij
    rcases Nat.eq_or_lt_of_le hk1 with h | h
    · subst h; exact ⟨hi'.1.symm, hi'.2.symm⟩
    · have hk := hdom k (by omega) hk2
      exact ⟨hk.1.trans hi'.1.symm, hk.2.trans hi'.2.symm⟩
  have hw : ∀ k, i - 1 ≤ k → k ≤ j → ∀ σ : Equiv.Perm (Fin n),
      weight Ĵ (p k) σ = weight Ĵ (p i) σ := by
    intro k hk1 hk2 σ
    unfold weight
    apply Finset.sum_congr rfl
    intro a _
    have h := hdom' k hk1 hk2
    rw [leftSlope_same M J hJ (p k) (p i) h.1 h.2 a (σ a)]
  -- integer exponent of a weight at `p i`
  set N : Equiv.Perm (Fin n) → ℤ := fun σ => ∑ a, kk a (σ a) (p i (σ a)) with hN
  have hWN : ∀ σ, weight Ĵ (p i) σ = (N σ : ℝ) * Lg := by
    intro σ
    unfold weight
    simp only [hN]
    push_cast
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [hkk, Real.log_zpow]
  have hWb : ∀ σ, |weight Ĵ (p i) σ| ≤ n * β := by
    intro σ
    unfold weight
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have : ∑ a : Fin n, |Real.log ((Ĵ.v a (σ a)).leftSlope (p i (σ a)))| ≤ ∑ _a : Fin n, β :=
      Finset.sum_le_sum (fun a _ => hkb _ _ _)
    simpa using this
  -- strict increase along the stretch (Lemma 4)
  have hinc : ∀ k, i ≤ k → k ≤ j → N (π k) < N (π (k + 1)) := by
    intro k hk1 hk2
    have h4 := lemma_4 hn J M hJ hM T π p hrun k (by omega) (by omega)
      (by
        have a1 := hdom' (k - 1) (by omega) (by omega)
        have a2 := hdom' k (by omega) hk2
        exact ⟨a1.1.trans a2.1.symm, a1.2.trans a2.2.symm⟩)
    rw [hw k (by omega) hk2, hw k (by omega) hk2, hWN, hWN] at h4
    have := lt_of_mul_lt_mul_right h4 hLg0.le
    exact_mod_cast this
  have hchain : ∀ m, i + m ≤ j + 1 → N (π i) + m ≤ N (π (i + m)) := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have := ih (by omega)
      have h2 := hinc (i + m) (by omega) (by omega)
      rw [show i + (m + 1) = i + m + 1 by ring]
      push_cast
      omega
  have hfin := hchain (j + 1 - i) (by omega)
  rw [show i + (j + 1 - i) = j + 1 by omega] at hfin
  have hr : ((j + 1 - i : ℕ) : ℝ) * Lg ≤ weight Ĵ (p i) (π (j + 1)) - weight Ĵ (p i) (π i) := by
    rw [hWN, hWN]
    have : ((N (π i) : ℤ) : ℝ) + ((j + 1 - i : ℕ) : ℝ) ≤ ((N (π (j + 1)) : ℤ) : ℝ) := by
      exact_mod_cast hfin
    nlinarith
  have hb1 := abs_le.mp (hWb (π (j + 1)))
  have hb2 := abs_le.mp (hWb (π i))
  have hLlow : ε / 2 ≤ Lg := by
    have := Real.one_sub_inv_le_log_of_pos (show 0 < 1 + ε by linarith)
    have h2 : ε / 2 ≤ 1 - (1 + ε)⁻¹ := by
      rw [show 1 - (1 + ε)⁻¹ = ε / (1 + ε) by field_simp; ring]
      rw [div_le_div_iff₀ (by norm_num) (by linarith)]
      nlinarith
    linarith
  have hfinal : ((j + 1 - i : ℕ) : ℝ) * (ε / 2) ≤ 2 * (n * β) := by
    have h0 : (0 : ℝ) ≤ ((j + 1 - i : ℕ) : ℝ) := by positivity
    nlinarith
  rw [le_div_iff₀ hε]
  have : (0 : ℝ) ≤ n * β := by positivity
  nlinarith
