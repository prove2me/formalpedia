-- Prove2me | solution 1 for FairRentFPTAS.Approx.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T12:39:15.274297+00:00
-- url     : https://prove2.me/submissions/b2173df2-b7f8-4394-a3d1-15a2ee3d27fe

import Mathlib
import Definitions.Def_FairRentFPTAS_Approx_Model
import Theorems.Thm_FairRentFPTAS_Approx_lemma_16

open FairRentFPTAS.Approx

namespace FRFL2Aux

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

/-- last slope among pieces starting at or below `x`, default `0`. -/
noncomputable def gL (l : List (ℝ × ℝ)) (x : ℝ) : ℝ :=
  (((l.filter (fun e => decide (e.1 ≤ x))).getLast?).map Prod.snd).getD 0

lemma getD_indep (L : List (ℝ × ℝ)) (h : L ≠ []) (d d' : ℝ) :
    (Option.map Prod.snd L.getLast?).getD d = (Option.map Prod.snd L.getLast?).getD d' := by
  cases hL : L.getLast? with
  | none => exact absurd (List.getLast?_eq_none_iff.mp hL) h
  | some z => rfl

lemma getLast?_cons_ne (e : ℝ × ℝ) (L : List (ℝ × ℝ)) (h : L ≠ []) :
    (e :: L).getLast? = L.getLast? := by
  cases L with
  | nil => exact absurd rfl h
  | cons b l => simp

lemma drop_diff (x y : ℝ) (hxy : x ≤ y) : ∀ l : List (ℝ × ℝ), (l.map Prod.fst).Pairwise (· < ·) →
    (∀ e ∈ l, e.1 ≤ x ∨ y ≤ e.1) → PLFun.drop l y - PLFun.drop l x = gL l x * (y - x) := by
  intro l
  induction l with
  | nil => intro _ _; simp [PLFun.drop, gL]
  | cons e t ih =>
    intro hs hd
    have hs' : (t.map Prod.fst).Pairwise (· < ·) := (List.pairwise_cons.mp hs).2
    have hlt : ∀ z ∈ t, e.1 < z.1 := fun z hz =>
      (List.pairwise_cons.mp hs).1 z.1 (List.mem_map_of_mem hz)
    have IH := ih hs' (fun z hz => hd z (List.mem_cons_of_mem _ hz))
    cases t with
    | nil =>
      simp only [PLFun.drop, gL]
      by_cases hex : e.1 ≤ x
      · have hf : [e].filter (fun e => decide (e.1 ≤ x)) = [e] :=
          List.filter_cons_of_pos (by simpa using hex)
        rw [hf, max_eq_left (le_trans hex hxy), max_eq_left hex]; simp; ring
      · have hey : y ≤ e.1 := (hd e (by simp)).resolve_left hex
        have hf : [e].filter (fun e => decide (e.1 ≤ x)) = [] :=
          List.filter_cons_of_neg (by simpa using hex)
        rw [hf, max_eq_right hey, max_eq_right (le_trans hxy hey)]; simp
    | cons e' t' =>
      have hee' := hlt e' (by simp)
      simp only [PLFun.drop]
      by_cases he'x : e'.1 ≤ x
      · have h1 : min (max y e.1) e'.1 = e'.1 := min_eq_right (le_trans (le_trans he'x hxy) (le_max_left _ _))
        have h2 : min (max x e.1) e'.1 = e'.1 := min_eq_right (le_trans he'x (le_max_left _ _))
        rw [h1, h2]
        have hgl : gL (e :: e' :: t') x = gL (e' :: t') x := by
          unfold gL
          have hne : (e' :: t').filter (fun e => decide (e.1 ≤ x)) ≠ [] := by
            intro h
            have : e' ∈ (e' :: t').filter (fun e => decide (e.1 ≤ x)) :=
              List.mem_filter.mpr ⟨by simp, by simpa using he'x⟩
            rw [h] at this; simp at this
          have hf : (e :: e' :: t').filter (fun e => decide (e.1 ≤ x)) =
              e :: (e' :: t').filter (fun e => decide (e.1 ≤ x)) :=
            List.filter_cons_of_pos (by simp; linarith)
          rw [hf, getLast?_cons_ne _ _ hne]
        rw [hgl, ← IH]; ring
      · push_neg at he'x
        have hye' : y ≤ e'.1 := (hd e' (by simp)).resolve_left (not_le.mpr he'x)
        have hnil : (e' :: t').filter (fun e => decide (e.1 ≤ x)) = [] := by
          rw [List.filter_eq_nil_iff]
          intro z hz
          simp only [decide_eq_true_eq, not_le]
          rcases List.mem_cons.mp hz with rfl | hz
          · exact he'x
          · linarith [(List.pairwise_cons.mp hs').1 z.1 (List.mem_map_of_mem hz)]
        have hIH0 : gL (e' :: t') x = 0 := by unfold gL; rw [hnil]; simp
        rw [hIH0, zero_mul] at IH
        have h1 : min (max y e.1) e'.1 = max y e.1 := min_eq_left (max_le hye' hee'.le)
        have h2 : min (max x e.1) e'.1 = max x e.1 :=
          min_eq_left (max_le (le_trans hxy hye') hee'.le)
        rw [h1, h2]
        by_cases hex : e.1 ≤ x
        · have hf : (e :: e' :: t').filter (fun e => decide (e.1 ≤ x)) = [e] := by
            rw [List.filter_cons_of_pos (by simpa using hex), hnil]
          have : gL (e :: e' :: t') x = e.2 := by unfold gL; rw [hf]; simp
          rw [this, max_eq_left (le_trans hex hxy), max_eq_left hex]
          linarith
        · have hey : y ≤ e.1 := (hd e (by simp)).resolve_left hex
          have hf : (e :: e' :: t').filter (fun e => decide (e.1 ≤ x)) = [] := by
            rw [List.filter_cons_of_neg (by simpa using hex), hnil]
          have : gL (e :: e' :: t') x = 0 := by unfold gL; rw [hf]; simp
          rw [this, max_eq_right hey, max_eq_right (le_trans hxy hey)]
          linarith

lemma getLast_max (L : List (ℝ × ℝ)) (hs : (L.map Prod.fst).Pairwise (· < ·)) (h : L ≠ []) :
    ∀ e ∈ L, e.1 ≤ (L.getLast h).1 := by
  intro e he
  have hsplit := List.dropLast_append_getLast h
  rw [← hsplit] at he hs
  rw [List.map_append, List.pairwise_append] at hs
  rcases List.mem_append.mp he with he | he
  · have := hs.2.2 e.1 (List.mem_map_of_mem he) (L.getLast h).1 (by simp)
    exact this.le
  · simp at he; rw [he]

lemma leftSlope_pos (f : PLFun) (hf : f.WF) (x : ℝ) : 0 < f.leftSlope x := by
  unfold PLFun.leftSlope
  cases h : (f.pieces.filter (fun e => decide (e.1 < x))).getLast? with
  | none => simpa using firstSlope_pos f hf
  | some e =>
    simp only [Option.map_some, Option.getD_some]
    exact hf.2.2.2 e (List.mem_filter.mp (List.mem_of_getLast? h)).1

/-- local left-linearity of a piecewise-linear utility. -/
lemma local_linear (f : PLFun) (hf : f.WF) (x : ℝ) :
    ∃ η > 0, ∀ t, 0 ≤ t → t ≤ η → f.eval (x - t) = f.eval x + f.leftSlope x * t := by
  have hs := hf.2.2.1
  have hst := starts_nonneg f hf
  by_cases hx : x ≤ 0
  · refine ⟨1, one_pos, fun t ht0 _ => ?_⟩
    have hnil : f.pieces.filter (fun e => decide (e.1 < x)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro e he; simp only [decide_eq_true_eq, not_lt]; linarith [hst e he]
    have hls : f.leftSlope x = f.firstSlope := by
      unfold PLFun.leftSlope; rw [hnil]; simp
    rw [hls]
    rcases ht0.lt_or_eq with ht | rfl
    · have h1 : x - t < 0 := by linarith
      unfold PLFun.eval
      rw [if_pos h1]
      rcases hx.lt_or_eq with hx' | rfl
      · rw [if_pos hx']; ring
      · rw [if_neg (lt_irrefl 0), drop_eq_zero 0 _ hs hst]; ring
    · simp
  push_neg at hx
  set F := f.pieces.filter (fun e => decide (e.1 < x)) with hF
  have hFne : F ≠ [] := by
    obtain ⟨hne, hhead, _, _⟩ := hf
    cases h : f.pieces with
    | nil => exact absurd h hne
    | cons e t =>
      rw [h] at hhead; simp at hhead
      intro hF0
      have : e ∈ F := List.mem_filter.mpr ⟨by rw [h]; simp, by simp [hhead, hx]⟩
      rw [hF0] at this; simp at this
  have hFs : (F.map Prod.fst).Pairwise (· < ·) := hs.sublist ((List.filter_sublist).map _)
  set s := (F.getLast hFne).1 with hsdef
  have hsx : s < x := by
    have := (List.mem_filter.mp (List.getLast_mem hFne)).2
    simpa using this
  have hls : f.leftSlope x = (F.getLast hFne).2 := by
    unfold PLFun.leftSlope
    rw [← hF, List.getLast?_eq_getLast hFne]; simp
  refine ⟨x - s, by linarith, fun t ht0 htη => ?_⟩
  rcases ht0.lt_or_eq with ht | rfl
  swap
  · simp
  have hxt0 : 0 ≤ x - t := by
    have : 0 ≤ s := hst _ (List.mem_filter.mp (List.getLast_mem hFne)).1
    linarith
  unfold PLFun.eval
  rw [if_neg (not_lt.mpr hxt0), if_neg (not_lt.mpr hx.le)]
  have hdich : ∀ e ∈ f.pieces, e.1 ≤ x - t ∨ x ≤ e.1 := by
    intro e he
    by_cases hex : e.1 < x
    · left
      have := getLast_max F hFs hFne e (List.mem_filter.mpr ⟨he, by simpa using hex⟩)
      linarith
    · right; linarith
  have hd := drop_diff (x - t) x (by linarith) f.pieces hs hdich
  have hgl : gL f.pieces (x - t) = f.leftSlope x := by
    unfold gL
    have hfe : f.pieces.filter (fun e => decide (e.1 ≤ x - t)) = F := by
      rw [hF]
      apply List.filter_congr
      intro e he
      simp only [decide_eq_decide]
      constructor
      · intro h; linarith
      · intro h
        have := getLast_max F hFs hFne e (List.mem_filter.mpr ⟨he, by simpa using h⟩)
        linarith
    rw [hfe, hls, List.getLast?_eq_getLast hFne]; simp
  rw [hgl] at hd
  have : x - (x - t) = t := by ring
  rw [this] at hd
  linarith

end FRFL2Aux

open FRFL2Aux in
theorem solution {n : ℕ} (J : Instance n) (hJ : Standing J) (π σ : Equiv.Perm (Fin n))
    (p : Fin n → ℝ) (hEF : IsEF J π p) (hσ : IsMaxWeightPM J p σ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∃ q : Fin n → ℝ, IsEF J σ q ∧ ∀ r, p r - δ ≤ q r ∧ q r < p r := by
  classical
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    refine ⟨1, one_pos, fun δ _ _ => ⟨p, fun a => a.elim0, fun r => r.elim0⟩⟩
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hnpos⟩, Finset.mem_univ _⟩
  have hne2 : (Finset.univ : Finset (Fin n × Fin n)).Nonempty :=
    ⟨(⟨0, hnpos⟩, ⟨0, hnpos⟩), Finset.mem_univ _⟩
  -- notation
  set v : Fin n → Fin n → ℝ := fun a r => (J.v a r).eval (p r) with hv
  set lam : Fin n → Fin n → ℝ := fun a r => (J.v a r).leftSlope (p r) with hlam
  have hlam0 : ∀ a r, 0 < lam a r := fun a r => leftSlope_pos _ (hJ a r) _
  -- `σ a` is a first choice
  have hσfc : ∀ a r, v a r ≤ v a (σ a) := fun a r => hσ.1 a r
  -- potentials on the first-choice graph
  set E : Fin n → Fin n → Prop := fun a r => FirstChoice J p a r with hE
  set w : Fin n → Fin n → ℝ := fun a r => Real.log (lam a r) with hw
  set S : ℝ := ∑ a, ∑ r, |w a r| with hS
  set B : Fin n → Fin n → ℝ := fun a r => if E a r then w a r else -(2 * S + 1) with hB
  have hwS : ∀ a r, |w a r| ≤ ∑ r', |w a r'| := fun a r =>
    Finset.single_le_sum (f := fun r' => |w a r'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ r)
  have hS0 : 0 ≤ S := by positivity
  have hEσ : ∀ a, E a (σ a) := fun a => hσ.1 a
  have hBmax : ∀ τ : Equiv.Perm (Fin n), ∑ a, B a (τ a) ≤ ∑ a, B a (σ a) := by
    intro τ
    have hBσ : ∑ a, B a (σ a) = ∑ a, w a (σ a) := by
      apply Finset.sum_congr rfl; intro a _; simp only [hB]; rw [if_pos (hEσ a)]
    rw [hBσ]
    by_cases hτ : ∀ a, E a (τ a)
    · have : ∑ a, B a (τ a) = ∑ a, w a (τ a) := by
        apply Finset.sum_congr rfl; intro a _; simp only [hB, if_pos (hτ a)]
      rw [this]
      exact hσ.2 τ hτ
    · push_neg at hτ
      obtain ⟨a0, ha0⟩ := hτ
      have h1 : ∀ a, B a (τ a) + (if E a (τ a) then 0 else 2 * S + 1) ≤ ∑ r', |w a r'| := by
        intro a
        by_cases h : E a (τ a)
        · simp only [hB, if_pos h, add_zero]; exact le_trans (le_abs_self _) (hwS a _)
        · simp only [hB, if_neg h]; linarith [Finset.sum_nonneg (fun r' (_ : r' ∈ Finset.univ) => abs_nonneg (w a r'))]
      have h2 := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => h1 a)
      rw [Finset.sum_add_distrib] at h2
      have h3 : 2 * S + 1 ≤ ∑ a, (if E a (τ a) then (0 : ℝ) else 2 * S + 1) := by
        have := Finset.single_le_sum (f := fun a => if E a (τ a) then (0 : ℝ) else 2 * S + 1)
          (fun a _ => by split_ifs <;> linarith) (Finset.mem_univ a0)
        simp only [if_neg ha0] at this
        exact this
      have h4 : -S ≤ ∑ a, w a (σ a) := by
        have : ∑ a, -|w a (σ a)| ≤ ∑ a, w a (σ a) :=
          Finset.sum_le_sum (fun a _ => neg_abs_le _)
        have h5 : ∑ a, |w a (σ a)| ≤ S := Finset.sum_le_sum (fun a _ => hwS a (σ a))
        rw [Finset.sum_neg_distrib] at this
        linarith
      linarith
  obtain ⟨u, hu⟩ := (lemma_16 B σ).mpr hBmax
  set d : Fin n → ℝ := fun r => Real.exp (-u r) with hd
  have hd0 : ∀ r, 0 < d r := fun r => Real.exp_pos _
  have hdE : ∀ a r, E a r → lam a r * d r ≤ lam a (σ a) * d (σ a) := by
    intro a r hEar
    have h := hu a r
    simp only [hB] at h
    rw [if_pos hEar, if_pos (hEσ a)] at h
    have h' := Real.exp_le_exp.mpr h
    rw [Real.exp_sub, Real.exp_sub, Real.exp_log (hlam0 a r), Real.exp_log (hlam0 a (σ a))] at h'
    simp only [hd, Real.exp_neg]
    rw [div_eq_mul_inv, div_eq_mul_inv] at h'
    exact h'
  -- local linearity
  have hloc : ∀ a r, ∃ η > 0, ∀ t, 0 ≤ t → t ≤ η →
      (J.v a r).eval (p r - t) = v a r + lam a r * t := fun a r =>
    local_linear (J.v a r) (hJ a r) (p r)
  choose η hη0 hη using hloc
  -- the per-pair step bound
  have hc : ∀ ar : Fin n × Fin n, ∃ c > 0, c ≤ η ar.1 ar.2 ∧
      (¬ E ar.1 ar.2 → lam ar.1 ar.2 * c ≤ v ar.1 (σ ar.1) - v ar.1 ar.2) := by
    rintro ⟨a, r⟩
    by_cases hEar : E a r
    · exact ⟨η a r, hη0 a r, le_rfl, fun h => absurd hEar h⟩
    · have hgap : v a r < v a (σ a) := by
        simp only [hE, FirstChoice] at hEar
        push_neg at hEar
        obtain ⟨r', hr'⟩ := hEar
        exact lt_of_lt_of_le hr' (hσfc a r')
      refine ⟨min (η a r) ((v a (σ a) - v a r) / lam a r),
        lt_min (hη0 a r) (div_pos (by linarith) (hlam0 a r)), min_le_left _ _, fun _ => ?_⟩
      have := min_le_right (η a r) ((v a (σ a) - v a r) / lam a r)
      calc lam a r * min (η a r) ((v a (σ a) - v a r) / lam a r)
          ≤ lam a r * ((v a (σ a) - v a r) / lam a r) :=
            mul_le_mul_of_nonneg_left this (hlam0 a r).le
        _ = v a (σ a) - v a r := by field_simp [(hlam0 a r).ne']
  choose c hc0 hcη hcgap using hc
  set δ₀ := Finset.univ.inf' hne2 c with hδ₀
  have hδ₀pos : 0 < δ₀ := (Finset.lt_inf'_iff hne2).mpr (fun ar _ => hc0 ar)
  have hδ₀c : ∀ a r, δ₀ ≤ c (a, r) := fun a r => Finset.inf'_le _ (Finset.mem_univ _)
  refine ⟨δ₀, hδ₀pos, fun δ hδ hδle => ?_⟩
  set D := Finset.univ.sup' hne d with hD
  have hdD : ∀ r, d r ≤ D := fun r => Finset.le_sup' d (Finset.mem_univ r)
  have hD0 : 0 < D := lt_of_lt_of_le (hd0 ⟨0, hnpos⟩) (hdD _)
  set s := δ / D with hs
  have hs0 : 0 < s := div_pos hδ hD0
  set t : Fin n → ℝ := fun r => s * d r with ht
  have ht0 : ∀ r, 0 < t r := fun r => mul_pos hs0 (hd0 r)
  have htδ : ∀ r, t r ≤ δ := by
    intro r
    simp only [ht, hs]
    rw [div_mul_eq_mul_div, div_le_iff₀ hD0]
    exact mul_le_mul_of_nonneg_left (hdD r) hδ.le
  refine ⟨fun r => p r - t r, ?_, fun r => ⟨by linarith [htδ r], by linarith [ht0 r]⟩⟩
  intro a r
  have htη : ∀ a r, t r ≤ η a r := fun a r =>
    le_trans (htδ r) (le_trans hδle (le_trans (hδ₀c a r) (hcη (a, r))))
  show (J.v a r).eval (p r - t r) ≤ (J.v a (σ a)).eval (p (σ a) - t (σ a))
  rw [hη a r (t r) (ht0 r).le (htη a r), hη a (σ a) (t (σ a)) (ht0 _).le (htη a _)]
  by_cases hEar : E a r
  · have heq : v a r = v a (σ a) := le_antisymm (hσfc a r) (hEar (σ a))
    have h1 : lam a r * t r ≤ lam a (σ a) * t (σ a) := by
      simp only [ht]
      have := hdE a r hEar
      nlinarith
    linarith
  · have h1 := hcgap (a, r) hEar
    have h2 : lam a r * t r ≤ lam a r * c (a, r) :=
      mul_le_mul_of_nonneg_left (le_trans (htδ r) (le_trans hδle (hδ₀c a r))) (hlam0 a r).le
    have h3 : 0 ≤ lam a (σ a) * t (σ a) := (mul_pos (hlam0 _ _) (ht0 _)).le
    simp only at h1
    linarith
