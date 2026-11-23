-- Prove2me | solution 1 for ChenCapacityTerminals.Exact.greedy_cover_card_bound
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:19:39.736113+00:00
-- url     : https://prove2.me/submissions/5160ca23-1db5-45b0-b8ad-8901f2b9d6ed

import Definitions.Def_ChenCapacityTerminals_Exact_Construction

set_option autoImplicit false

open ChenCapacityTerminals.Exact

namespace GreedyCoverAux

lemma uncoveredCount_cons_of_mem (groups : List (Finset ℕ)) (v : ℕ) (g : Finset ℕ)
    (h : v ∈ g) : uncoveredCount (g :: groups) v = uncoveredCount groups v + 1 := by
  simp [uncoveredCount, h]

lemma uncoveredCount_cons_of_not_mem (groups : List (Finset ℕ)) (v : ℕ) (g : Finset ℕ)
    (h : v ∉ g) : uncoveredCount (g :: groups) v = uncoveredCount groups v := by
  simp [uncoveredCount, h]

lemma uncoveredCount_eq_sum (groups : List (Finset ℕ)) (v : ℕ) :
    uncoveredCount groups v = (groups.map fun g => if v ∈ g then 1 else 0).sum := by
  induction groups with
  | nil => rfl
  | cons g groups ih =>
      by_cases h : v ∈ g
      · rw [uncoveredCount_cons_of_mem _ _ _ h, ih]
        simp [h, Nat.add_comm]
      · rw [uncoveredCount_cons_of_not_mem _ _ _ h, ih]
        simp [h]

lemma filter_not_length (groups : List (Finset ℕ)) (v : ℕ) :
    (groups.filter fun g => v ∉ g).length + uncoveredCount groups v = groups.length := by
  induction groups with
  | nil => rfl
  | cons g groups ih =>
      by_cases h : v ∈ g
      · have hnot : (List.filter (fun g => v ∉ g) (g :: groups)) =
            List.filter (fun g => v ∉ g) groups := by simp [h]
        calc
          (List.filter (fun g => v ∉ g) (g :: groups)).length +
              uncoveredCount (g :: groups) v =
            (List.filter (fun g => v ∉ g) groups).length +
              (uncoveredCount groups v + 1) := by
                rw [hnot, uncoveredCount_cons_of_mem _ _ _ h]
          _ = (g :: groups).length := by simp only [List.length_cons]; omega
      · have hnot : (List.filter (fun g => v ∉ g) (g :: groups)) =
            g :: List.filter (fun g => v ∉ g) groups := by simp [h]
        calc
          (List.filter (fun g => v ∉ g) (g :: groups)).length +
              uncoveredCount (g :: groups) v =
            ((List.filter (fun g => v ∉ g) groups).length + 1) +
              uncoveredCount groups v := by
                rw [hnot, uncoveredCount_cons_of_not_mem _ _ _ h]
                rfl
          _ = (g :: groups).length := by simp only [List.length_cons]; omega

lemma sum_uncovered_swap (V : Finset ℕ) (groups : List (Finset ℕ)) :
    ∑ v ∈ V, (groups.map fun g => if v ∈ g then 1 else 0).sum =
      (groups.map fun g => ∑ v ∈ V, if v ∈ g then 1 else 0).sum := by
  induction groups with
  | nil => simp
  | cons g groups ih => simp [Finset.sum_add_distrib, ih]

lemma total_uncoveredCount (V : Finset ℕ) (d : ℕ) (groups : List (Finset ℕ))
    (hgroups : ∀ g ∈ groups, g ⊆ V ∧ g.card = d) :
    ∑ v ∈ V, uncoveredCount groups v = groups.length * d := by
  calc
    ∑ v ∈ V, uncoveredCount groups v =
        ∑ v ∈ V, (groups.map fun g => if v ∈ g then 1 else 0).sum := by
          apply Finset.sum_congr rfl
          intro v hv
          rw [uncoveredCount_eq_sum]
    _ = (groups.map fun g => ∑ v ∈ V, if v ∈ g then 1 else 0).sum :=
          sum_uncovered_swap V groups
    _ = (groups.map fun _ => d).sum := by
          congr 1
          apply List.map_congr_left
          intro g hg
          have hsub := (hgroups g hg).1
          have hcard := (hgroups g hg).2
          rw [Finset.sum_boole]
          have heq : {x ∈ V | x ∈ g} = g := by
            ext x
            simp only [Finset.mem_filter]
            exact ⟨fun h => h.2, fun h => ⟨hsub h, h⟩⟩
          simp [heq, hcard]
    _ = groups.length * d := by simp [Nat.mul_comm]

lemma card_sum_eq (d : ℕ) : ∀ groups : List (Finset ℕ),
    (∀ g ∈ groups, g.card = d) → (groups.map Finset.card).sum = groups.length * d := by
  intro groups
  induction groups with
  | nil => simp
  | cons g groups ih =>
      intro h
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [h g (by simp), ih (fun a ha => h a (by simp [ha]))]
      simp [Nat.add_mul, Nat.add_comm]

end GreedyCoverAux

open GreedyCoverAux

theorem solution (V : Finset ℕ) (d : ℕ)
    (groups : List (Finset ℕ)) (D : List ℕ) :
    1 ≤ d → d ≤ V.card →
    (∀ g ∈ groups, g ⊆ V ∧ g.card = d) →
    Greedy V groups D →
    (D.toFinset.card : ℝ) ≤
      2 * ((V.card : ℝ) / d) * Real.log (2 + (groups.map Finset.card).sum) := by
  classical
  intro hd hdn hgroups hgreedy
  have hn : 0 < V.card := by omega
  have hnpos : (0 : ℝ) < V.card := by exact_mod_cast hn
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have aux : ∀ (sel : List ℕ) (gs : List (Finset ℕ)),
      (∀ g ∈ gs, g ⊆ V ∧ g.card = d) → Greedy V gs sel →
      (sel.length : ℝ) ≤
        2 * ((V.card : ℝ) / d) * Real.log (1 + gs.length) := by
    intro sel
    induction sel with
    | nil =>
        intro gs hgs hgr
        change gs = [] at hgr
        subst gs
        simp
    | cons v rest ih =>
        intro gs hgs hgr
        rw [Greedy] at hgr
        rcases hgr with ⟨hvV, hvpos, hvmax, hrest⟩
        let gs' := gs.filter fun g => v ∉ g
        have hgs' : ∀ g ∈ gs', g ⊆ V ∧ g.card = d := by
          intro g hg
          exact hgs g (List.mem_of_mem_filter hg)
        have ihr := ih gs' hgs' hrest
        have hlen : gs'.length + uncoveredCount gs v = gs.length := by
          exact filter_not_length gs v
        have hh : 0 < gs.length := by omega
        have hh' : gs'.length ≤ gs.length := by omega
        have htotal : ∑ u ∈ V, uncoveredCount gs u = gs.length * d :=
          total_uncoveredCount V d gs hgs
        have hcover : gs.length * d ≤ V.card * uncoveredCount gs v := by
          calc
            gs.length * d = ∑ u ∈ V, uncoveredCount gs u := htotal.symm
            _ ≤ ∑ u ∈ V, uncoveredCount gs v := by
              apply Finset.sum_le_sum
              intro u hu
              exact hvmax u hu
            _ = V.card * uncoveredCount gs v := by simp
        have hdiffnat : gs.length - gs'.length = uncoveredCount gs v := by omega
        have hcover' : gs.length * d ≤ V.card * (gs.length - gs'.length) := by
          simpa [hdiffnat] using hcover
        have hcastR : ((gs.length * d : ℕ) : ℝ) ≤
            ((V.card * (gs.length - gs'.length) : ℕ) : ℝ) := by
          exact_mod_cast hcover'
        push_cast [Nat.cast_sub hh'] at hcastR
        have hlog0 := Real.log_le_sub_one_of_pos
          (show 0 < (1 + (gs'.length : ℝ)) / (1 + (gs.length : ℝ)) by positivity)
        rw [Real.log_div (by positivity : (1 : ℝ) + gs'.length ≠ 0)
          (by positivity : (1 : ℝ) + gs.length ≠ 0)] at hlog0
        have hid : (1 + (gs'.length : ℝ)) / (1 + (gs.length : ℝ)) - 1 =
            -(((gs.length : ℝ) - (gs'.length : ℝ)) / (1 + (gs.length : ℝ))) := by
          field_simp
          <;> ring
        rw [hid] at hlog0
        have hlog : ((gs.length : ℝ) - (gs'.length : ℝ)) / (1 + (gs.length : ℝ)) ≤
            Real.log (1 + gs.length) - Real.log (1 + gs'.length) := by
          linarith
        have hfraction : (d : ℝ) / (2 * (V.card : ℝ)) ≤
            ((gs.length : ℝ) - (gs'.length : ℝ)) / (1 + (gs.length : ℝ)) := by
          apply (div_le_div_iff₀ (by positivity) (by positivity)).2
          have hhar : 1 + (gs.length : ℝ) ≤ 2 * (gs.length : ℝ) := by
            have hhR : (1 : ℝ) ≤ gs.length := by exact_mod_cast hh
            linarith
          have hnum := mul_le_mul_of_nonneg_left hhar (show 0 ≤ (d : ℝ) by positivity)
          nlinarith [hcastR]
        have hlogdiff : (d : ℝ) / (2 * (V.card : ℝ)) ≤
            Real.log (1 + gs.length) - Real.log (1 + gs'.length) :=
          hfraction.trans hlog
        have hmul := mul_le_mul_of_nonneg_left hlogdiff
          (show 0 ≤ 2 * ((V.card : ℝ) / d) by positivity)
        have hcoef : 2 * ((V.card : ℝ) / d) * ((d : ℝ) / (2 * (V.card : ℝ))) = 1 := by
          field_simp
          <;> ring
        rw [hcoef] at hmul
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        linarith [ihr]
  have hcard : (D.toFinset.card : ℝ) ≤ (D.length : ℝ) := by
    exact_mod_cast List.toFinset_card_le D
  have haux := aux D groups hgroups hgreedy
  have hsum : (groups.map Finset.card).sum = groups.length * d :=
    card_sum_eq d groups (fun g hg => (hgroups g hg).2)
  have hle : 1 + groups.length ≤ 2 + (groups.map Finset.card).sum := by
    rw [hsum]
    have hm : groups.length ≤ groups.length * d := by
      simpa using Nat.mul_le_mul_left groups.length hd
    omega
  have hleR : (1 : ℝ) + groups.length ≤ 2 + ((groups.map Finset.card).sum : ℝ) := by
    exact_mod_cast hle
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 1 + groups.length) hleR
  have hmul := mul_le_mul_of_nonneg_left hlog
    (show 0 ≤ 2 * ((V.card : ℝ) / d) by positivity)
  linarith
