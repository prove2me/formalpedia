-- Prove2me | solution 1 for CombOpt.MatroidPolytope.convexHull_charVec_eq_rankPolytope
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-11T05:30:07.33675+00:00
-- url     : https://prove2.me/submissions/d0c5e4ce-2d2d-43f1-9db4-5dc7c1c84593

import Mathlib
import Definitions.Def_CombOpt_MatroidPolytope_IsMatroid
import Definitions.Def_CombOpt_MatroidPolytope_rankPolytope
import Definitions.Def_OnlineCRS_Combine_indicatorVec

set_option autoImplicit false

namespace EdmondsAux
open CombOpt.MatroidPolytope

/-- An independent subset of `A` has at most `rank A` elements. -/
lemma card_le_rank {α : Type*} (I : Finset α → Prop) {A J : Finset α} (hJA : J ⊆ A)
    (hJ : I J) : J.card ≤ rank I A := by
  classical
  unfold rank
  exact Finset.le_sup (f := Finset.card)
    (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hJA, hJ⟩)

/-- Every independent subset of `A` extends to an independent subset of `A` of size `rank A`
(axiom M2). -/
lemma exists_extend {α : Type*} [DecidableEq α] (I : Finset α → Prop) (hI : IsMatroid I)
    {A J₀ : Finset α} (hA : J₀ ⊆ A) (hJ₀ : I J₀) :
    ∃ J, J₀ ⊆ J ∧ J ⊆ A ∧ I J ∧ rank I A ≤ J.card := by
  classical
  obtain ⟨J, hJmem, hJmax⟩ :=
    (A.powerset.filter (fun J => I J ∧ J₀ ⊆ J)).exists_max_image Finset.card
      ⟨J₀, by simp [hA, hJ₀]⟩
  simp only [Finset.mem_filter, Finset.mem_powerset] at hJmem
  obtain ⟨hJA, hJI, hJ₀J⟩ := hJmem
  have hbJ : IsBasisOf I A J := by
    refine ⟨hJA, hJI, fun J' hJJ' hJ'A hJ'I => ?_⟩
    have hle : J'.card ≤ J.card :=
      hJmax J' (by simp [hJ'A, hJ'I, hJ₀J.trans hJJ'])
    exact (Finset.eq_of_subset_of_card_le hJJ' hle).symm
  have hne : (A.powerset.filter I).Nonempty :=
    ⟨∅, Finset.mem_filter.2 ⟨Finset.empty_mem_powerset _, hI.1.1⟩⟩
  obtain ⟨Js, hJsmem, hJseq⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  rw [Finset.mem_filter, Finset.mem_powerset] at hJsmem
  have hbJs : IsBasisOf I A Js := by
    refine ⟨hJsmem.1, hJsmem.2, fun J' hJJ' hJ'A hJ'I => ?_⟩
    have hle : J'.card ≤ Js.card := by
      have := card_le_rank I hJ'A hJ'I
      unfold rank at this
      rw [hJseq] at this
      exact this
    exact (Finset.eq_of_subset_of_card_le hJJ' hle).symm
  refine ⟨J, hJ₀J, hJA, hJI, ?_⟩
  have hc := hI.2 A J Js hbJ hbJs
  unfold rank
  rw [hJseq, hc]

/-- Greedy bound for nonnegative weights, by induction on the size of the support. -/
lemma greedy_bound {α : Type*} [Fintype α] [DecidableEq α] (I : Finset α → Prop)
    (hI : IsMatroid I) (x : α → ℝ) (hx : x ∈ rankPolytope I) :
    ∀ n : ℕ, ∀ w : α → ℝ, (∀ e, 0 ≤ w e) →
      (Finset.univ.filter (fun e => 0 < w e)).card ≤ n →
      ∃ J, I J ∧ J ⊆ Finset.univ.filter (fun e => 0 < w e) ∧
        ∑ e, w e * x e ≤ ∑ e ∈ J, w e := by
  have hx' : (∀ e, 0 ≤ x e) ∧ ∀ A : Finset α, ∑ e ∈ A, x e ≤ (rank I A : ℝ) := hx
  have hzero : ∀ w : α → ℝ, (∀ e, 0 ≤ w e) →
      Finset.univ.filter (fun e => 0 < w e) = ∅ →
      ∃ J, I J ∧ J ⊆ Finset.univ.filter (fun e => 0 < w e) ∧
        ∑ e, w e * x e ≤ ∑ e ∈ J, w e := by
    intro w hw hS
    refine ⟨∅, hI.1.1, Finset.empty_subset _, ?_⟩
    have hw0 : ∀ e, w e = 0 := by
      intro e
      have he : e ∉ Finset.univ.filter (fun e => 0 < w e) := by rw [hS]; simp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at he
      exact le_antisymm he (hw e)
    simp [hw0]
  intro n
  induction n with
  | zero =>
    intro w hw hn
    exact hzero w hw (Finset.card_eq_zero.1 (Nat.le_zero.1 hn))
  | succ n ih =>
    intro w hw hn
    rcases (Finset.univ.filter (fun e => 0 < w e)).eq_empty_or_nonempty with hS | hS
    · exact hzero w hw hS
    set S := Finset.univ.filter (fun e => 0 < w e) with hSdef
    obtain ⟨e0, he0S, he0⟩ := S.exists_mem_eq_inf' hS w
    set m := S.inf' hS w with hm
    have hmpos : 0 < m := by
      rw [he0]
      simpa [hSdef] using he0S
    have hmle : ∀ e ∈ S, m ≤ w e := fun e he => Finset.inf'_le w he
    set w' : α → ℝ := fun e => if e ∈ S then w e - m else 0 with hw'
    have hw'nn : ∀ e, 0 ≤ w' e := by
      intro e
      simp only [hw']
      split_ifs with h
      · linarith [hmle e h]
      · exact le_refl 0
    have hsub : Finset.univ.filter (fun e => 0 < w' e) ⊆ S.erase e0 := by
      intro e he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hw'] at he
      split_ifs at he with h
      · refine Finset.mem_erase.2 ⟨?_, h⟩
        rintro rfl
        rw [← he0] at he
        linarith
      · exact absurd he (lt_irrefl 0)
    have hcard : (Finset.univ.filter (fun e => 0 < w' e)).card ≤ n := by
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem he0S] at h1
      omega
    obtain ⟨J', hJ'I, hJ'sub, hJ'bound⟩ := ih w' hw'nn hcard
    have hJ'S : J' ⊆ S := hJ'sub.trans (hsub.trans (Finset.erase_subset _ _))
    obtain ⟨J, hJ'J, hJS, hJI, hJcard⟩ := exists_extend I hI hJ'S hJ'I
    refine ⟨J, hJI, hJS, ?_⟩
    have hdecomp : ∀ e, w e = (if e ∈ S then m else 0) + w' e := by
      intro e
      simp only [hw']
      split_ifs with h
      · ring
      · have h2 : ¬ 0 < w e := by simpa [hSdef] using h
        have h3 := hw e
        simp only [zero_add]
        linarith
    have h1 : ∑ e, w e * x e = ∑ e ∈ S, m * x e + ∑ e, w' e * x e := by
      have h4 : ∑ e ∈ S, m * x e = ∑ e, (if e ∈ S then m * x e else 0) := by
        rw [Finset.sum_ite_mem, Finset.univ_inter]
      rw [h4, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun e _ => ?_)
      rw [hdecomp e]
      split_ifs <;> ring
    have h2 : ∑ e ∈ J, w e = m * J.card + ∑ e ∈ J, w' e := by
      rw [Finset.sum_congr rfl (fun e he =>
        (show w e = m + w' e by rw [hdecomp e, if_pos (hJS he)]))]
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      ring
    have h3 : ∑ e ∈ S, m * x e ≤ m * J.card := by
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ hmpos.le
      calc ∑ e ∈ S, x e ≤ (rank I S : ℝ) := hx'.2 S
        _ ≤ J.card := by exact_mod_cast hJcard
    have h4 : ∑ e ∈ J', w' e ≤ ∑ e ∈ J, w' e :=
      Finset.sum_le_sum_of_subset_of_nonneg hJ'J (fun e _ _ => hw'nn e)
    linarith

/-- LP bound: every point of the rank polytope is beaten, for any weight, by some independent
set. -/
lemma lp_bound {α : Type*} [Fintype α] [DecidableEq α] (I : Finset α → Prop) (hI : IsMatroid I)
    (x : α → ℝ) (hx : x ∈ rankPolytope I) (w : α → ℝ) :
    ∃ J, I J ∧ ∑ e, w e * x e ≤ ∑ e ∈ J, w e := by
  have hx' : (∀ e, 0 ≤ x e) ∧ ∀ A : Finset α, ∑ e ∈ A, x e ≤ (rank I A : ℝ) := hx
  obtain ⟨J, hJI, hJsub, hJb⟩ := greedy_bound I hI x hx _ (fun e => max (w e) 0)
    (fun e => le_max_right _ _) le_rfl
  refine ⟨J, hJI, ?_⟩
  have h1 : ∑ e, w e * x e ≤ ∑ e, max (w e) 0 * x e :=
    Finset.sum_le_sum (fun e _ => mul_le_mul_of_nonneg_right (le_max_left _ _) (hx'.1 e))
  have h2 : ∑ e ∈ J, max (w e) 0 = ∑ e ∈ J, w e := by
    refine Finset.sum_congr rfl (fun e he => ?_)
    have h3 := hJsub he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h3
    have h4 : 0 < w e := (lt_max_iff.1 h3).resolve_right (lt_irrefl 0)
    exact max_eq_left h4.le
  linarith

end EdmondsAux

open CombOpt.MatroidPolytope in
theorem solution {α : Type*} [Fintype α] [DecidableEq α]
    (I : Finset α → Prop) (hI : IsMatroid I) :
    convexHull ℝ {x : α → ℝ | ∃ J : Finset α, I J ∧ x = OnlineCRS.Combine.indicatorVec J} =
      rankPolytope I := by
  have hsum : ∀ J A : Finset α,
      ∑ e ∈ A, OnlineCRS.Combine.indicatorVec J e = ((A ∩ J).card : ℝ) := by
    intro J A
    simp only [OnlineCRS.Combine.indicatorVec]
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter]
  apply Set.Subset.antisymm
  · apply convexHull_min
    · rintro x ⟨J, hJ, rfl⟩
      refine ⟨fun e => ?_, fun A => ?_⟩
      · simp only [OnlineCRS.Combine.indicatorVec]
        split_ifs <;> norm_num
      · rw [hsum]
        exact_mod_cast EdmondsAux.card_le_rank I Finset.inter_subset_left
          (hI.1.2 _ _ Finset.inter_subset_right hJ)
    · intro x hx y hy a b ha hb hab
      obtain ⟨hx1, hx2⟩ := hx
      obtain ⟨hy1, hy2⟩ := hy
      refine ⟨fun e => ?_, fun A => ?_⟩
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have := hx1 e
        have := hy1 e
        positivity
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
          ← Finset.mul_sum]
        calc a * ∑ e ∈ A, x e + b * ∑ e ∈ A, y e
            ≤ a * (rank I A : ℝ) + b * (rank I A : ℝ) :=
              add_le_add (mul_le_mul_of_nonneg_left (hx2 A) ha)
                (mul_le_mul_of_nonneg_left (hy2 A) hb)
          _ = (rank I A : ℝ) := by rw [← add_mul, hab, one_mul]
  · intro x hx
    by_contra hnot
    have hTfin : {x : α → ℝ | ∃ J : Finset α, I J ∧ x = OnlineCRS.Combine.indicatorVec J}.Finite := by
      apply (Finset.univ.powerset.image
        (fun J => OnlineCRS.Combine.indicatorVec J) : Finset (α → ℝ)).finite_toSet.subset
      rintro y ⟨J, _, rfl⟩
      simp
    have hcomp : IsCompact (convexHull ℝ
        {x : α → ℝ | ∃ J : Finset α, I J ∧ x = OnlineCRS.Combine.indicatorVec J}) :=
      hTfin.isCompact_convexHull (𝕜 := ℝ)
    obtain ⟨f, u, hfa, hfx⟩ :=
      geometric_hahn_banach_closed_point (convex_convexHull ℝ _) hcomp.isClosed hnot
    set w : α → ℝ := fun e => f (fun j => if e = j then 1 else 0) with hwdef
    have hf : ∀ y : α → ℝ, f y = ∑ e, w e * y e := by
      intro y
      conv_lhs => rw [pi_eq_sum_univ y]
      rw [map_sum]
      refine Finset.sum_congr rfl (fun e _ => ?_)
      rw [map_smul, smul_eq_mul, hwdef, mul_comm]
    obtain ⟨J, hJ, hb⟩ := EdmondsAux.lp_bound I hI x hx w
    have hJmem : OnlineCRS.Combine.indicatorVec J ∈ convexHull ℝ
        {x : α → ℝ | ∃ J : Finset α, I J ∧ x = OnlineCRS.Combine.indicatorVec J} :=
      subset_convexHull ℝ _ ⟨J, hJ, rfl⟩
    have h1 := hfa _ hJmem
    rw [hf] at h1 hfx
    have h2 : ∑ e, w e * OnlineCRS.Combine.indicatorVec J e = ∑ e ∈ J, w e := by
      simp only [OnlineCRS.Combine.indicatorVec, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    linarith
