-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.semistandardPeel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:19.83433+00:00
-- url     : https://prove2.me/submissions/0482c213-bdf8-40cd-ab25-62abc5ca4ca5

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LCssytLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_SSYTPeel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MvPolynomial Finset
noncomputable section
namespace Formalism.GradedWeylDivisibility
private theorem exists_pos_of_sum_pos {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (h : 0 < ∑ i ∈ s, f i) : ∃ i ∈ s, 0 < f i := by
  by_contra hne
  push_neg at hne
  have hz : ∑ i ∈ s, f i = 0 := Finset.sum_eq_zero (fun i hi => by have := hne i hi; omega)
  omega
private theorem colExp_apply {r n h : ℕ} (c : Fin h → Fin r) (hh : h ≤ n) (a : Fin r)
    (t : Fin n) :
    colExp c hh (a, t) = if ht : t.val < h then (if c ⟨t.val, ht⟩ = a then 1 else 0) else 0 := by
  unfold colExp
  rw [Finsupp.finset_sum_apply]
  simp only [Finsupp.single_apply, Prod.mk.injEq]
  by_cases ht : t.val < h
  · rw [dif_pos ht]
    rw [Finset.sum_eq_single ⟨t.val, ht⟩]
    · have e : Fin.castLE hh ⟨t.val, ht⟩ = t := Fin.ext rfl
      by_cases hca : c ⟨t.val, ht⟩ = a
      · rw [if_pos ⟨hca, e⟩, if_pos hca]
      · rw [if_neg (fun hh' => hca hh'.1), if_neg hca]
    · intro p _ hp
      rw [if_neg]
      rintro ⟨_, h2⟩
      have h3 : p.val = t.val := congrArg Fin.val h2
      exact hp (Fin.ext h3)
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  · rw [dif_neg ht]
    apply Finset.sum_eq_zero
    intro p _
    rw [if_neg]
    rintro ⟨_, h2⟩
    have h3 : p.val = t.val := congrArg Fin.val h2
    have h4 := p.isLt
    apply ht
    omega
private theorem sum_colExp_apply_eq_ite_mem {r n h : ℕ} (c : Fin h → Fin r) (hh : h ≤ n)
    (S : Finset (Fin r)) (t : Fin n) :
    ∑ b ∈ S, colExp c hh (b, t) =
      if ht : t.val < h then (if c ⟨t.val, ht⟩ ∈ S then 1 else 0) else 0 := by
  simp only [colExp_apply]
  by_cases ht : t.val < h
  · simp only [dif_pos ht]
    exact Finset.sum_ite_eq S (c ⟨t.val, ht⟩) (fun _ => 1)
  · simp only [dif_neg ht]
    exact Finset.sum_const_zero
end Formalism.GradedWeylDivisibility
end
end

set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution : SSYTPeel := by
  intro r n ν m hcol hint_r _hm
  have hstep : ∀ l j : Fin n, j.val = l.val + 1 → 0 < ν j → 0 < ν l := by
    intro l j hlj hj
    rw [← hcol j] at hj
    obtain ⟨a, -, ha⟩ := exists_pos_of_sum_pos _ _ hj
    have h1 : (∑ b : Fin r with b ≤ a, m (b, j)) ≤ 0 + ∑ b : Fin r with b < a, m (b, l) :=
      hint_r l j hlj a
    have h2 : m (a, j) ≤ ∑ b : Fin r with b ≤ a, m (b, j) :=
      Finset.single_le_sum (f := fun b => m (b, j)) (fun _ _ => Nat.zero_le _) (by simp)
    have h3 : (∑ b : Fin r with b < a, m (b, l)) ≤ ∑ b, m (b, l) :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    rw [← hcol l]
    omega
  have hdown : ∀ (d : ℕ) (t t' : Fin n), t.val = t'.val + d → 0 < ν t → 0 < ν t' := by
    intro d
    induction d with
    | zero =>
      intro t t' htt ht
      have e : t = t' := Fin.ext (by omega)
      rw [← e]
      exact ht
    | succ d ih =>
      intro t t' htt ht
      have hs : t'.val + d < n := by have := t.isLt; omega
      exact ih ⟨t'.val + d, hs⟩ t' rfl
        (hstep ⟨t'.val + d, hs⟩ t (by show t.val = t'.val + d + 1; omega) ht)
  have hmono : ∀ t t' : Fin n, t' ≤ t → 0 < ν t → 0 < ν t' := by
    intro t t' hle ht
    have hle' : t'.val ≤ t.val := hle
    exact hdown (t.val - t'.val) t t' (by omega) ht
  obtain ⟨h, hh, hiff⟩ : ∃ h : ℕ, h ≤ n ∧ ∀ t : Fin n, t.val < h ↔ 0 < ν t := by
    refine ⟨(Finset.univ.filter (fun t : Fin n => 0 < ν t)).card, ?_, ?_⟩
    · exact le_trans (Finset.card_filter_le _ _) (by rw [Finset.card_univ, Fintype.card_fin])
    · intro t
      constructor
      · intro ht
        by_contra hnt
        have hsub : Finset.univ.filter (fun t : Fin n => 0 < ν t) ⊆ Finset.Iio t := by
          intro s hs
          rw [Finset.mem_filter] at hs
          rw [Finset.mem_Iio]
          by_contra hst
          push_neg at hst
          exact hnt (hmono s t hst hs.2)
        have hc := Finset.card_le_card hsub
        rw [Fin.card_Iio] at hc
        omega
      · intro ht
        have hsub : Finset.Iic t ⊆ Finset.univ.filter (fun t : Fin n => 0 < ν t) := by
          intro s hs
          rw [Finset.mem_Iic] at hs
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ _, hmono t s hs ht⟩
        have hc := Finset.card_le_card hsub
        rw [Fin.card_Iic] at hc
        omega
  have hex : ∀ p : Fin h, ∃ a : Fin r, 0 < m (a, Fin.castLE hh p) ∧
      ∀ b : Fin r, 0 < m (b, Fin.castLE hh p) → a ≤ b := by
    intro p
    have hp : 0 < ν (Fin.castLE hh p) := (hiff _).1 p.isLt
    rw [← hcol] at hp
    obtain ⟨a, -, ha⟩ := exists_pos_of_sum_pos _ _ hp
    have hS : (Finset.univ.filter (fun b : Fin r => 0 < m (b, Fin.castLE hh p))).Nonempty :=
      ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩⟩
    refine ⟨(Finset.univ.filter (fun b : Fin r => 0 < m (b, Fin.castLE hh p))).min' hS, ?_, ?_⟩
    · exact (Finset.mem_filter.mp (Finset.min'_mem _ hS)).2
    · intro b hb
      exact Finset.min'_le _ b (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩)
  choose c hc1 hc2 using hex
  have hc1' : ∀ (t : Fin n) (ht : t.val < h), 0 < m (c ⟨t.val, ht⟩, t) := by
    intro t ht
    have e : Fin.castLE hh ⟨t.val, ht⟩ = t := Fin.ext rfl
    have h1 := hc1 ⟨t.val, ht⟩
    rwa [e] at h1
  have hc2' : ∀ (t : Fin n) (ht : t.val < h) (b : Fin r), 0 < m (b, t) → c ⟨t.val, ht⟩ ≤ b := by
    intro t ht b hb
    have e : Fin.castLE hh ⟨t.val, ht⟩ = t := Fin.ext rfl
    apply hc2 ⟨t.val, ht⟩ b
    rw [e]
    exact hb
  have hcstep : ∀ (l j : Fin n) (hl : l.val < h) (hj : j.val < h), j.val = l.val + 1 →
      c ⟨l.val, hl⟩ < c ⟨j.val, hj⟩ := by
    intro l j hl hj hlj
    have h1 : (∑ b : Fin r with b ≤ c ⟨j.val, hj⟩, m (b, j)) ≤
        0 + ∑ b : Fin r with b < c ⟨j.val, hj⟩, m (b, l) := hint_r l j hlj (c ⟨j.val, hj⟩)
    have h2 : m (c ⟨j.val, hj⟩, j) ≤ ∑ b : Fin r with b ≤ c ⟨j.val, hj⟩, m (b, j) :=
      Finset.single_le_sum (f := fun b => m (b, j)) (fun _ _ => Nat.zero_le _) (by simp)
    have h3 := hc1' j hj
    have h4 : 0 < ∑ b : Fin r with b < c ⟨j.val, hj⟩, m (b, l) := by omega
    obtain ⟨b, hb, hbpos⟩ := exists_pos_of_sum_pos _ _ h4
    rw [Finset.mem_filter] at hb
    exact lt_of_le_of_lt (hc2' l hl b hbpos) hb.2
  have hcstep' : ∀ p q : Fin h, q.val = p.val + 1 → c p < c q := by
    intro p q hpq
    have := hcstep (Fin.castLE hh p) (Fin.castLE hh q) p.isLt q.isLt hpq
    exact this
  have hkey : ∀ (d : ℕ) (p q : Fin h), q.val = p.val + d + 1 → c p < c q := by
    intro d
    induction d with
    | zero =>
      intro p q hpq
      exact hcstep' p q (by omega)
    | succ d ih =>
      intro p q hpq
      have hs : p.val + d + 1 < h := by have := q.isLt; omega
      exact lt_trans (ih p ⟨p.val + d + 1, hs⟩ rfl)
        (hcstep' ⟨p.val + d + 1, hs⟩ q (by show q.val = p.val + d + 1 + 1; omega))
  have hcmono : StrictMono c := by
    intro p q hpq
    have hpq' : p.val < q.val := hpq
    exact hkey (q.val - p.val - 1) p q (by omega)
  have hle : ∀ (a : Fin r) (t : Fin n), colExp c hh (a, t) ≤ m (a, t) := by
    intro a t
    rw [colExp_apply]
    by_cases ht : t.val < h
    · rw [dif_pos ht]
      by_cases hca : c ⟨t.val, ht⟩ = a
      · rw [if_pos hca]
        have h1 := hc1' t ht
        rw [hca] at h1
        omega
      · rw [if_neg hca]
        exact Nat.zero_le _
    · rw [dif_neg ht]
      exact Nat.zero_le _
  have hsub : ∀ x, (m - colExp c hh) x = m x - colExp c hh x := by
    intro x
    first
      | exact Finsupp.tsub_apply _ _ _
      | simp
      | rfl
  have hpart : ∀ (S : Finset (Fin r)) (t : Fin n),
      ∑ b ∈ S, (m - colExp c hh) (b, t) =
        ∑ b ∈ S, m (b, t) - (if ht : t.val < h then (if c ⟨t.val, ht⟩ ∈ S then 1 else 0) else 0) := by
    intro S t
    have hadd : ∑ b ∈ S, (m - colExp c hh) (b, t) + ∑ b ∈ S, colExp c hh (b, t) =
        ∑ b ∈ S, m (b, t) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [hsub]
      exact Nat.sub_add_cancel (hle b t)
    rw [sum_colExp_apply_eq_ite_mem] at hadd
    omega
  have hzero : ∀ t : Fin n, ¬ t.val < h → ∀ S : Finset (Fin r), ∑ b ∈ S, m (b, t) = 0 := by
    intro t ht S
    have hν : ν t = 0 := by
      have := (hiff t).not.mp ht
      omega
    have h1 : ∑ b ∈ S, m (b, t) ≤ ∑ b, m (b, t) :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    rw [hcol t, hν] at h1
    omega
  refine ⟨h, hh, c, hcmono, hiff, ?_, ?_, ?_⟩
  · first
      | exact Finsupp.le_def.mpr (fun x => hle x.1 x.2)
      | exact fun x => hle x.1 x.2
      | (intro x; exact hle x.1 x.2)
  · intro l j hlj a
    show (∑ b : Fin r with b ≤ a, (m - colExp c hh) (b, j)) ≤
      0 + ∑ b : Fin r with b < a, (m - colExp c hh) (b, l)
    rw [hpart, hpart]
    have h1 : (∑ b : Fin r with b ≤ a, m (b, j)) ≤ 0 + ∑ b : Fin r with b < a, m (b, l) :=
      hint_r l j hlj a
    by_cases hl : l.val < h
    · by_cases hcl : c ⟨l.val, hl⟩ < a
      · have hmemL : c ⟨l.val, hl⟩ ∈ Finset.univ.filter (fun b : Fin r => b < a) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcl⟩
        rw [dif_pos hl, if_pos hmemL]
        by_cases hj : j.val < h
        · by_cases hcj : c ⟨j.val, hj⟩ ≤ a
          · have hmemJ : c ⟨j.val, hj⟩ ∈ Finset.univ.filter (fun b : Fin r => b ≤ a) :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcj⟩
            rw [dif_pos hj, if_pos hmemJ]
            omega
          · have hz : ∑ b : Fin r with b ≤ a, m (b, j) = 0 := by
              apply Finset.sum_eq_zero
              intro b hb
              rw [Finset.mem_filter] at hb
              by_contra hne
              exact hcj (le_trans (hc2' j hj b (Nat.pos_of_ne_zero hne)) hb.2)
            omega
        · have hz := hzero j hj (Finset.univ.filter (fun b : Fin r => b ≤ a))
          omega
      · have hz : ∑ b : Fin r with b < a, m (b, l) = 0 := by
          apply Finset.sum_eq_zero
          intro b hb
          rw [Finset.mem_filter] at hb
          by_contra hne
          exact hcl (lt_of_le_of_lt (hc2' l hl b (Nat.pos_of_ne_zero hne)) hb.2)
        omega
    · have hz := hzero l hl (Finset.univ.filter (fun b : Fin r => b < a))
      omega
  · intro t
    rw [hpart, hcol t]
    by_cases ht : t.val < h
    · rw [dif_pos ht, if_pos (Finset.mem_univ _), if_pos ht]
    · rw [dif_neg ht, if_neg ht]
end Formalism.GradedWeylDivisibility
