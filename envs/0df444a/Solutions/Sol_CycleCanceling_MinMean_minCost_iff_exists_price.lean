-- Prove2me | solution 1 for CycleCanceling.MinMean.minCost_iff_exists_price
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T01:02:12.820357+00:00
-- url     : https://prove2.me/submissions/74c10390-3213-4f6b-8d48-362a07c6bc78

import Mathlib
import Definitions.Def_CycleCanceling_MinMean_Network
import Definitions.Def_CycleCanceling_MinMean_EpsOptimal

set_option autoImplicit false

namespace P86d315c5

open CycleCanceling.MinMean

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem sum_swap (N : CircNetwork V) (F : V → V → ℝ) :
    ∑ e ∈ N.E, F e.1 e.2 = ∑ e ∈ N.E, F e.2 e.1 := by
  apply Finset.sum_nbij' Prod.swap Prod.swap
  · intro e he; exact (N.symm e.1 e.2).1 he
  · intro e he; exact (N.symm e.1 e.2).1 he
  · intro e _; simp
  · intro e _; simp
  · intro e _; simp

theorem sum_E_eq (N : CircNetwork V) (F : V → V → ℝ) :
    ∑ e ∈ N.E, F e.1 e.2 = ∑ x, ∑ y ∈ Finset.univ.filter (fun y => (x, y) ∈ N.E), F x y := by
  calc ∑ e ∈ N.E, F e.1 e.2 = ∑ e : V × V, if e ∈ N.E then F e.1 e.2 else 0 := by
        rw [Finset.sum_ite_mem, Finset.univ_inter]
    _ = ∑ x, ∑ y, if (x, y) ∈ N.E then F x y else 0 :=
        Fintype.sum_prod_type (fun e : V × V => if e ∈ N.E then F e.1 e.2 else 0)
    _ = _ := by simp only [Finset.sum_filter]

theorem pot_zero (N : CircNetwork V) (p : V → ℝ) (d : V → V → ℝ)
    (hanti : ∀ v w, (v, w) ∈ N.E → d v w = -d w v)
    (hcons : ∀ w, ∑ v ∈ Finset.univ.filter (fun v => (w, v) ∈ N.E), d v w = 0) :
    ∑ e ∈ N.E, (p e.1 - p e.2) * d e.1 e.2 = 0 := by
  have h1 : ∑ e ∈ N.E, p e.1 * d e.1 e.2 = 0 := by
    rw [sum_E_eq N (fun x y => p x * d x y)]
    apply Finset.sum_eq_zero
    intro x _
    rw [← Finset.mul_sum]
    have : ∑ y ∈ Finset.univ.filter (fun y => (x, y) ∈ N.E), d x y
        = -∑ y ∈ Finset.univ.filter (fun y => (x, y) ∈ N.E), d y x := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro y hy
      exact hanti x y (Finset.mem_filter.1 hy).2
    rw [this, hcons x, neg_zero, mul_zero]
  have h2 : ∑ e ∈ N.E, p e.2 * d e.1 e.2 = 0 := by
    have hs := sum_swap N (fun x y => p y * d x y)
    rw [hs]
    have : ∀ e ∈ N.E, p e.1 * d e.2 e.1 = -(p e.1 * d e.1 e.2) := by
      intro e he; rw [hanti e.1 e.2 he]; ring
    rw [Finset.sum_congr rfl this, Finset.sum_neg_distrib, h1, neg_zero]
  have : ∑ e ∈ N.E, (p e.1 - p e.2) * d e.1 e.2
      = ∑ e ∈ N.E, p e.1 * d e.1 e.2 - ∑ e ∈ N.E, p e.2 * d e.1 e.2 := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e _; ring
  rw [this, h1, h2, sub_zero]

/-- signed count of the arc `(v, w)` in an arc list -/
def sc (A : List (V × V)) (v w : V) : ℝ :=
  (A.map (fun a => (if a = (v, w) then (1:ℝ) else 0) - (if a = (w, v) then (1:ℝ) else 0))).sum

theorem fsum_list {ι : Type*} (s : Finset ι) (A : List (V × V)) (φ : ι → V × V → ℝ) :
    ∑ i ∈ s, (A.map (φ i)).sum = (A.map (fun a => ∑ i ∈ s, φ i a)).sum := by
  induction A with
  | nil => simp
  | cons a A ih => simp [Finset.sum_add_distrib, ih]

theorem lsum_sub {α : Type*} (A : List α) (P Q : α → ℝ) :
    (A.map (fun a => P a - Q a)).sum = (A.map P).sum - (A.map Q).sum := by
  induction A with
  | nil => simp
  | cons a A ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem closed_nonneg (N : CircNetwork V) (f : V → V → ℝ) (hmin : IsMinCost N f)
    (A : List (V × V)) (hA : ∀ a ∈ A, a ∈ N.E ∧ 0 < resCap N f a.1 a.2)
    (hperm : (A.map Prod.fst).Perm (A.map Prod.snd)) :
    0 ≤ (A.map (fun a => N.c a.1 a.2)).sum := by
  by_contra hneg
  rw [not_le] at hneg
  have hAne : A ≠ [] := by rintro rfl; simp at hneg
  obtain ⟨a0, ha0, hmin0⟩ := A.toFinset.exists_min_image (fun a => resCap N f a.1 a.2)
    (by simpa [List.toFinset_nonempty_iff] using hAne)
  rw [List.mem_toFinset] at ha0
  have hlen : (0:ℝ) < A.length := by
    have : 0 < A.length := List.length_pos_iff_ne_nil.2 hAne
    exact_mod_cast this
  set δ := resCap N f a0.1 a0.2 / A.length with hδ
  have hδpos : 0 < δ := div_pos (hA a0 ha0).2 hlen
  have hδle : ∀ a ∈ A, δ * A.length ≤ resCap N f a.1 a.2 := by
    intro a ha; rw [hδ, div_mul_cancel₀ _ hlen.ne']; exact hmin0 a (List.mem_toFinset.2 ha)
  let g : V → V → ℝ := fun v w => f v w + δ * sc A v w
  have hg : IsCirculation N g := by
    refine ⟨?_, ?_, ?_⟩
    · intro v w hvw
      by_cases hin : (v, w) ∈ A
      · have h1 : sc A v w ≤ A.length := by
          unfold sc
          have := List.sum_le_card_nsmul
            (A.map (fun a => (if a = (v, w) then (1:ℝ) else 0) - (if a = (w, v) then (1:ℝ) else 0)))
            1 (by
              intro x hx; rw [List.mem_map] at hx; obtain ⟨a, _, rfl⟩ := hx
              split_ifs <;> norm_num)
          simpa using this
        have h2 := hδle (v, w) hin
        simp only [g]; unfold resCap at h2; simp only at h2; nlinarith
      · have h1 : sc A v w ≤ 0 := by
          unfold sc
          have := List.sum_le_card_nsmul
            (A.map (fun a => (if a = (v, w) then (1:ℝ) else 0) - (if a = (w, v) then (1:ℝ) else 0)))
            0 (by
              intro x hx; rw [List.mem_map] at hx; obtain ⟨a, ha, rfl⟩ := hx
              have : a ≠ (v, w) := fun h => hin (h ▸ ha)
              simp only [if_neg this]; split_ifs <;> norm_num)
          simpa using this
        simp only [g]; have := hmin.1.1 v w hvw; nlinarith
    · intro v w hvw
      simp only [g]
      rw [hmin.1.2.1 v w hvw]
      have : sc A v w + sc A w v = 0 := by
        unfold sc; rw [← List.sum_map_add]
        have : ∀ a : V × V, ((if a = (v, w) then (1:ℝ) else 0) - (if a = (w, v) then (1:ℝ) else 0))
            + ((if a = (w, v) then (1:ℝ) else 0) - (if a = (v, w) then (1:ℝ) else 0)) = 0 :=
          fun a => by ring
        simp [this]
      have : sc A v w = -sc A w v := by linarith
      rw [this]; ring
    · intro w
      simp only [g]
      rw [Finset.sum_add_distrib, hmin.1.2.2 w, zero_add, ← Finset.mul_sum]
      apply mul_eq_zero_of_right
      unfold sc
      rw [fsum_list _ A (fun v a => (if a = (v, w) then (1:ℝ) else 0) - (if a = (w, v) then (1:ℝ) else 0))]
      have hterm : ∀ a ∈ A, ∑ v ∈ Finset.univ.filter (fun v => (w, v) ∈ N.E),
          ((if a = (v, w) then (1:ℝ) else 0) - (if a = (w, v) then (1:ℝ) else 0))
          = (if a.2 = w then (1:ℝ) else 0) - (if a.1 = w then (1:ℝ) else 0) := by
        intro a ha
        rw [Finset.sum_sub_distrib]
        obtain ⟨a1, a2⟩ := a
        have haE := (hA _ ha).1
        have haE' : (a2, a1) ∈ N.E := (N.symm a1 a2).1 haE
        congr 1
        · by_cases h2 : a2 = w
          · subst h2
            simp [Finset.mem_filter, haE']
          · simp [h2]
        · by_cases h1 : a1 = w
          · subst h1
            simp [Finset.mem_filter, haE]
          · simp [h1]
      rw [List.map_congr_left hterm, lsum_sub A (fun a => if a.2 = w then (1:ℝ) else 0)
        (fun a => if a.1 = w then (1:ℝ) else 0)]
      have e1 : (A.map (fun a : V × V => if a.2 = w then (1:ℝ) else 0)).sum
          = ((A.map Prod.snd).map (fun x => if x = w then (1:ℝ) else 0)).sum := by
        rw [List.map_map]; rfl
      have e2 : (A.map (fun a : V × V => if a.1 = w then (1:ℝ) else 0)).sum
          = ((A.map Prod.fst).map (fun x => if x = w then (1:ℝ) else 0)).sum := by
        rw [List.map_map]; rfl
      rw [e1, e2, ((hperm.map (fun x => if x = w then (1:ℝ) else 0)).sum_eq), sub_self]
  have hterm : ∀ a ∈ A, ∑ e ∈ N.E, N.c e.1 e.2 *
      ((if a = (e.1, e.2) then (1:ℝ) else 0) - (if a = (e.2, e.1) then (1:ℝ) else 0))
      = 2 * N.c a.1 a.2 := by
    intro a ha
    have haE := (hA a ha).1
    have hsw := sum_swap N (fun x y => N.c x y * if a = (y, x) then (1:ℝ) else 0)
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [hsw]
    simp only [Prod.mk.eta, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, haE, if_true]
    rw [N.cost_antisymm a.1 a.2 haE]; ring
  have h2 : ∑ e ∈ N.E, N.c e.1 e.2 * sc A e.1 e.2 = 2 * (A.map (fun a => N.c a.1 a.2)).sum := by
    calc ∑ e ∈ N.E, N.c e.1 e.2 * sc A e.1 e.2
        = ∑ e ∈ N.E, (A.map (fun a => N.c e.1 e.2 *
            ((if a = (e.1, e.2) then (1:ℝ) else 0) - (if a = (e.2, e.1) then (1:ℝ) else 0)))).sum := by
          apply Finset.sum_congr rfl; intro e _; unfold sc; rw [List.sum_map_mul_left]
      _ = (A.map (fun a => ∑ e ∈ N.E, N.c e.1 e.2 *
            ((if a = (e.1, e.2) then (1:ℝ) else 0) - (if a = (e.2, e.1) then (1:ℝ) else 0)))).sum :=
          fsum_list N.E A (fun e a => N.c e.1 e.2 *
            ((if a = (e.1, e.2) then (1:ℝ) else 0) - (if a = (e.2, e.1) then (1:ℝ) else 0)))
      _ = (A.map (fun a => 2 * N.c a.1 a.2)).sum := by rw [List.map_congr_left hterm]
      _ = 2 * (A.map (fun a => N.c a.1 a.2)).sum := List.sum_map_mul_left A (fun a => N.c a.1 a.2) 2
  have hcost : cost N g = cost N f + δ * (A.map (fun a => N.c a.1 a.2)).sum := by
    unfold cost
    have : ∑ e ∈ N.E, N.c e.1 e.2 * g e.1 e.2 = ∑ e ∈ N.E, N.c e.1 e.2 * f e.1 e.2
        + δ * ∑ e ∈ N.E, N.c e.1 e.2 * sc A e.1 e.2 := by
      simp only [g]; rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro e _; ring
    rw [this, h2]; ring
  have := hmin.2 g hg
  have := mul_neg_of_pos_of_neg hδpos hneg
  linarith

/-- the arcs of the backward walk `… → y₂ → y₁ → w` given by `w` and `[y₁, y₂, …]` -/
def arcs : V → List V → List (V × V)
  | _, [] => []
  | w, y :: l => (y, w) :: arcs y l

theorem arcs_append (w x : V) (s t : List V) :
    arcs w (s ++ x :: t) = arcs w (s ++ [x]) ++ arcs x t := by
  induction s generalizing w with
  | nil => simp [arcs]
  | cons y s ih => simp [arcs, ih]

theorem map_fst_arcs (w : V) (l : List V) : (arcs w l).map Prod.fst = l := by
  induction l generalizing w with
  | nil => simp [arcs]
  | cons y l ih => simp [arcs, ih]

theorem map_snd_arcs (w x : V) (s : List V) : (arcs w (s ++ [x])).map Prod.snd = w :: s := by
  induction s generalizing w with
  | nil => simp [arcs]
  | cons y s ih => simp [arcs, ih]

theorem shortcut (N : CircNetwork V) (f : V → V → ℝ) (hmin : IsMinCost N f) :
    ∀ (l : List V) (w : V), (∀ a ∈ arcs w l, a ∈ N.E ∧ 0 < resCap N f a.1 a.2) →
    ∃ l', (∀ a ∈ arcs w l', a ∈ N.E ∧ 0 < resCap N f a.1 a.2) ∧ (w :: l').Nodup ∧
      ((arcs w l').map (fun a => N.c a.1 a.2)).sum ≤ ((arcs w l).map (fun a => N.c a.1 a.2)).sum := by
  intro l
  induction l with
  | nil => intro w _; exact ⟨[], by simp [arcs], by simp, le_rfl⟩
  | cons y l1 ih =>
    intro w hv
    have hyw : (y, w) ∈ N.E ∧ 0 < resCap N f y w := hv (y, w) (by simp [arcs])
    have hv1 : ∀ a ∈ arcs y l1, a ∈ N.E ∧ 0 < resCap N f a.1 a.2 :=
      fun a ha => hv a (by simp [arcs, ha])
    obtain ⟨l2, hv2, hnd2, hle2⟩ := ih y hv1
    have hv2' : ∀ a ∈ arcs w (y :: l2), a ∈ N.E ∧ 0 < resCap N f a.1 a.2 := by
      intro a ha
      simp only [arcs, List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact hyw
      · exact hv2 a ha
    have hle2' : ((arcs w (y :: l2)).map (fun a => N.c a.1 a.2)).sum
        ≤ ((arcs w (y :: l1)).map (fun a => N.c a.1 a.2)).sum := by
      simp only [arcs, List.map_cons, List.sum_cons]; linarith
    by_cases hw : w ∈ y :: l2
    · obtain ⟨s, t, hst⟩ := List.append_of_mem hw
      refine ⟨t, ?_, ?_, ?_⟩
      · intro e he; apply hv2' e; rw [hst, arcs_append]; exact List.mem_append_right _ he
      · have : (s ++ w :: t).Nodup := by rw [← hst]; exact hnd2
        exact this.sublist (List.sublist_append_right s (w :: t))
      · have hcl : 0 ≤ ((arcs w (s ++ [w])).map (fun a => N.c a.1 a.2)).sum := by
          apply closed_nonneg N f hmin
          · intro e he; apply hv2' e; rw [hst, arcs_append]; exact List.mem_append_left _ he
          · rw [map_fst_arcs, map_snd_arcs]; exact List.perm_append_singleton w s
        have hsplit : ((arcs w (y :: l2)).map (fun a => N.c a.1 a.2)).sum
            = ((arcs w (s ++ [w])).map (fun a => N.c a.1 a.2)).sum
              + ((arcs w t).map (fun a => N.c a.1 a.2)).sum := by
          rw [hst, arcs_append, List.map_append, List.sum_append]
        linarith
    · exact ⟨y :: l2, hv2', List.nodup_cons.2 ⟨hw, hnd2⟩, hle2'⟩

theorem bk_lower (N : CircNetwork V) (f : V → V → ℝ) (M : ℝ)
    (hM : ∀ a ∈ N.E, -M ≤ N.c a.1 a.2) :
    ∀ (l : List V) (w : V), (∀ a ∈ arcs w l, a ∈ N.E ∧ 0 < resCap N f a.1 a.2) →
      -(l.length * M) ≤ ((arcs w l).map (fun a => N.c a.1 a.2)).sum := by
  intro l
  induction l with
  | nil => intro w _; simp [arcs]
  | cons y l ih =>
    intro w hv
    have h1 : -M ≤ N.c y w := hM (y, w) (hv (y, w) (by simp [arcs])).1
    have h2 := ih y (fun a ha => hv a (by simp [arcs, ha]))
    simp only [arcs, List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith

end P86d315c5

open CycleCanceling.MinMean in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (N : CircNetwork V) (f : V → V → ℝ) (hf : IsCirculation N f) :
    IsMinCost N f ↔ ∃ p : V → ℝ, ∀ v w, (v, w) ∈ N.E → 0 < resCap N f v w →
      0 ≤ reducedCost N p v w := by
  constructor
  · intro hmin
    set M : ℝ := ∑ a ∈ N.E, |N.c a.1 a.2| with hMdef
    have hM : ∀ a ∈ N.E, -M ≤ N.c a.1 a.2 := by
      intro a ha
      have h1 := Finset.single_le_sum (f := fun a : V × V => |N.c a.1 a.2|)
        (fun i _ => abs_nonneg _) ha
      have h2 := neg_abs_le (N.c a.1 a.2)
      linarith
    have hM0 : 0 ≤ M := Finset.sum_nonneg (fun i _ => abs_nonneg _)
    let S : V → Set ℝ := fun w => {x | ∃ l : List V,
      (∀ a ∈ P86d315c5.arcs w l, a ∈ N.E ∧ 0 < resCap N f a.1 a.2) ∧
        ((P86d315c5.arcs w l).map (fun a => N.c a.1 a.2)).sum = x}
    have hne : ∀ w, (S w).Nonempty := fun w => ⟨0, [], by simp [P86d315c5.arcs], by simp [P86d315c5.arcs]⟩
    have hbdd : ∀ w, BddBelow (S w) := by
      intro w
      refine ⟨-((Fintype.card V : ℝ) * M), ?_⟩
      rintro x ⟨l, hv, rfl⟩
      obtain ⟨l', hv', hnd, hle⟩ := P86d315c5.shortcut N f hmin l w hv
      have hlb := P86d315c5.bk_lower N f M hM l' w hv'
      have hlen : (w :: l').length ≤ Fintype.card V := hnd.length_le_card
      simp only [List.length_cons] at hlen
      have : (l'.length : ℝ) ≤ Fintype.card V := by
        exact_mod_cast (by omega : l'.length ≤ Fintype.card V)
      nlinarith
    refine ⟨fun w => sInf (S w), ?_⟩
    intro v w hvw hres
    unfold reducedCost
    have : sInf (S w) - N.c v w ≤ sInf (S v) := by
      apply le_csInf (hne v)
      rintro x ⟨l, hv, rfl⟩
      have hmem : N.c v w + ((P86d315c5.arcs v l).map (fun a => N.c a.1 a.2)).sum ∈ S w := by
        refine ⟨v :: l, ?_, ?_⟩
        · intro a ha
          simp only [P86d315c5.arcs, List.mem_cons] at ha
          rcases ha with rfl | ha
          · exact ⟨hvw, hres⟩
          · exact hv a ha
        · simp [P86d315c5.arcs]
      have := csInf_le (hbdd w) hmem
      linarith
    linarith
  · rintro ⟨p, hp⟩
    refine ⟨hf, fun g hg => ?_⟩
    let d : V → V → ℝ := fun v w => g v w - f v w
    have hanti : ∀ v w, (v, w) ∈ N.E → d v w = -d w v := by
      intro v w hvw
      simp only [d]; rw [hg.2.1 v w hvw, hf.2.1 v w hvw]; ring
    have hcons : ∀ w, ∑ v ∈ Finset.univ.filter (fun v => (w, v) ∈ N.E), d v w = 0 := by
      intro w; simp only [d]; rw [Finset.sum_sub_distrib, hg.2.2 w, hf.2.2 w, sub_zero]
    have key : 0 ≤ ∑ e ∈ N.E, N.c e.1 e.2 * d e.1 e.2 := by
      have hsplit : ∑ e ∈ N.E, N.c e.1 e.2 * d e.1 e.2
          = ∑ e ∈ N.E, reducedCost N p e.1 e.2 * d e.1 e.2
            - ∑ e ∈ N.E, (p e.1 - p e.2) * d e.1 e.2 := by
        rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro e _
        unfold reducedCost; ring
      rw [hsplit, P86d315c5.pot_zero N p d hanti hcons, sub_zero]
      apply Finset.sum_nonneg
      intro e he
      have he' : (e.2, e.1) ∈ N.E := (N.symm e.1 e.2).1 he
      have hga := hg.2.1 e.1 e.2 he
      have hfa := hf.2.1 e.1 e.2 he
      rcases lt_trichotomy (d e.1 e.2) 0 with h | h | h
      · have hr : 0 < resCap N f e.2 e.1 := by
          unfold resCap
          have := hg.1 e.2 e.1 he'
          simp only [d] at h
          linarith
        have h3 := hp e.2 e.1 he' hr
        have h4 : reducedCost N p e.1 e.2 = -reducedCost N p e.2 e.1 := by
          unfold reducedCost; rw [N.cost_antisymm e.1 e.2 he]; ring
        rw [h4]; nlinarith
      · rw [h, mul_zero]
      · have hr : 0 < resCap N f e.1 e.2 := by
          unfold resCap
          have := hg.1 e.1 e.2 he
          simp only [d] at h
          linarith
        have h3 := hp e.1 e.2 he hr
        exact mul_nonneg h3 h.le
    have : ∑ e ∈ N.E, N.c e.1 e.2 * d e.1 e.2
        = ∑ e ∈ N.E, N.c e.1 e.2 * g e.1 e.2 - ∑ e ∈ N.E, N.c e.1 e.2 * f e.1 e.2 := by
      rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro e _; simp only [d]; ring
    unfold cost
    linarith
