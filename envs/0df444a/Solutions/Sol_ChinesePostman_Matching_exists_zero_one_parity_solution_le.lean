-- Prove2me | solution 1 for ChinesePostman.Matching.exists_zero_one_parity_solution_le
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T07:33:46.147254+00:00
-- url     : https://prove2.me/submissions/6cf070db-6d68-48a4-9785-4c6864eb20c5

import Mathlib
import Definitions.Def_ChinesePostman_Matching_Setting



namespace ChinesePostman.Matching

section WkSec
variable {V E : Type*}

inductive Wk (G : EdmondsMatching65.Polyhedron.Graph V E) : V → V → List E → Prop
  | nil (a : V) : Wk G a a []
  | cons (a a' b : V) (e : E) (es : List E) :
      G.ends e = s(a, a') → Wk G a' b es → Wk G a b (e :: es)

theorem Wk.append {G : EdmondsMatching65.Polyhedron.Graph V E} {a b c : V} {l1 l2 : List E}
    (h1 : Wk G a b l1) (h2 : Wk G b c l2) : Wk G a c (l1 ++ l2) := by
  induction h1 with
  | nil a => simpa using h2
  | cons a a' b e es he _ ih => exact Wk.cons a a' c e _ he (ih h2)

theorem Wk.reverse {G : EdmondsMatching65.Polyhedron.Graph V E} {a b : V} {es : List E}
    (h : Wk G a b es) : Wk G b a es.reverse := by
  induction h with
  | nil a => exact Wk.nil a
  | cons a a' b e es he _ ih =>
    simp only [List.reverse_cons]
    refine ih.append (Wk.cons a' a a e [] ?_ (Wk.nil a))
    rw [he, Sym2.eq_swap]

theorem isWalk_cons {G : EdmondsMatching65.Polyhedron.Graph V E} {a a' : V} {ns : List V}
    {e : E} {es : List E} :
    IsWalk G (a :: a' :: ns) (e :: es) ↔ G.ends e = s(a, a') ∧ IsWalk G (a' :: ns) es := by
  unfold IsWalk
  simp only [List.length_cons, add_left_inj, Fin.forall_fin_succ]
  constructor
  · rintro ⟨hl, h0, hs⟩
    refine ⟨?_, hl, ?_⟩
    · obtain ⟨u, v, hu, hv, he⟩ := h0
      simp at hu hv
      subst hu; subst hv; exact he
    · intro i
      simpa using hs i
  · rintro ⟨he, hl, hs⟩
    refine ⟨hl, ⟨a, a', by simp, by simp, by simpa using he⟩, ?_⟩
    intro i
    simpa using hs i

theorem Wk.exists_walk {G : EdmondsMatching65.Polyhedron.Graph V E} {a b : V} {es : List E}
    (h : Wk G a b es) : ∃ ns : List V, IsWalkFrom G a b ns es := by
  induction h with
  | nil a => exact ⟨[a], ⟨by simp, by simp⟩, by simp, by simp⟩
  | cons a a' b e es he _ ih =>
    obtain ⟨ns, hw, hh, hl⟩ := ih
    cases ns with
    | nil => simp at hh
    | cons x ns' =>
      simp at hh; subst hh
      refine ⟨a :: x :: ns', isWalk_cons.2 ⟨he, hw⟩, by simp, ?_⟩
      cases ns' with
      | nil => simpa using hl
      | cons y ns'' => simpa [List.getLast?_cons] using hl

theorem IsWalkFrom.wk {G : EdmondsMatching65.Polyhedron.Graph V E} {a b : V} {ns : List V}
    {es : List E} (h : IsWalkFrom G a b ns es) : Wk G a b es := by
  obtain ⟨hw, hh, hl⟩ := h
  induction es generalizing ns a with
  | nil =>
    have hlen := hw.1
    match ns, hlen with
    | [x], _ =>
      simp at hh hl; subst hh; subst hl; exact Wk.nil _
  | cons e es ih =>
    have hlen := hw.1
    match ns, hlen with
    | x :: y :: ns', _ =>
      simp at hh; subst hh
      obtain ⟨he, hw'⟩ := isWalk_cons.1 hw
      refine Wk.cons _ y _ e es he (ih hw' (by simp) ?_)
      simpa [List.getLast?_cons] using hl

theorem IsWalk.reverse {G : EdmondsMatching65.Polyhedron.Graph V E} {ns : List V} {es : List E}
    (h : IsWalk G ns es) : IsWalk G ns.reverse es.reverse := by
  obtain ⟨hl, hs⟩ := h
  refine ⟨by simpa using hl, ?_⟩
  intro i
  have hi : i.val < es.length := by simpa using i.2
  have hrev : es.reverse[i] = es[es.length - 1 - i.val] := by
    simp [List.getElem_reverse]
  obtain ⟨u, v, hu, hv, he⟩ := hs ⟨es.length - 1 - i.val, by omega⟩
  simp only at hu hv he
  refine ⟨v, u, ?_, ?_, ?_⟩
  · rw [List.getElem?_reverse (by omega)]
    have : ns.length - 1 - i.val = es.length - 1 - i.val + 1 := by omega
    rw [this]; exact hv
  · rw [List.getElem?_reverse (by omega)]
    have : ns.length - 1 - (i.val + 1) = es.length - 1 - i.val := by omega
    rw [this]; exact hu
  · rw [hrev]; exact he.trans Sym2.eq_swap


theorem incidentSum_eq [Fintype E] [DecidableEq V] (G : EdmondsMatching65.Polyhedron.Graph V E)
    (x : E → ℕ) (v : V) : incidentSum G x v = ∑ e, if v ∈ G.ends e then x e else 0 := by
  classical
  unfold incidentSum
  rw [Finset.sum_filter]
  
theorem degree_eq [Fintype E] [DecidableEq V] (G : EdmondsMatching65.Polyhedron.Graph V E)
    (v : V) : degree G v = incidentSum G (fun _ => 1) v := by
  classical
  unfold degree incidentSum
  simp

theorem isParity_iff [Fintype E] [DecidableEq V] (G : EdmondsMatching65.Polyhedron.Graph V E)
    (x : E → ℕ) : IsParitySolution G x ↔
      ∀ v, incidentSum G x v % 2 = if Odd (degree G v) then 1 else 0 := by
  unfold IsParitySolution
  constructor
  · rintro ⟨w, hw⟩ v
    rw [hw v]
    split_ifs <;> omega
  · intro h
    refine ⟨fun v => incidentSum G x v / 2, fun v => ?_⟩
    have := h v
    dsimp only
    split_ifs at this ⊢ <;> omega

theorem Wk.count_mod [DecidableEq V] {G : EdmondsMatching65.Polyhedron.Graph V E} {a b : V}
    {es : List E} (h : Wk G a b es) (v : V) :
    (es.filter (fun e => decide (v ∈ G.ends e))).length % 2 =
      ((if v = a then 1 else 0) + (if v = b then 1 else 0)) % 2 := by
  induction h with
  | nil a => split_ifs <;> simp
  | cons a a' b e es he _ ih =>
    have hne : a ≠ a' := by
      intro hh
      have := G.loopless e
      rw [he, hh] at this
      simp at this
    rw [List.filter_cons]
    by_cases hv : v ∈ G.ends e
    · have hv' : v = a ∨ v = a' := by rw [he] at hv; simpa using hv
      rw [if_pos (by simpa using hv)]
      simp only [List.length_cons]
      rcases hv' with rfl | rfl
      · simp [hne] at ih ⊢; split_ifs at ih ⊢ <;> omega
      · simp [hne.symm] at ih ⊢; split_ifs at ih ⊢ <;> omega
    · have hv' : ¬ (v = a ∨ v = a') := by rw [he] at hv; simpa using hv
      push_neg at hv'
      rw [if_neg (by simpa using hv)]
      simp [hv'.1, hv'.2] at ih ⊢
      exact ih

theorem sum_count_filter [Fintype E] [DecidableEq E] [DecidableEq V]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (v : V) (l : List E) :
    (∑ e, if v ∈ G.ends e then l.count e else 0) =
      (l.filter (fun e => decide (v ∈ G.ends e))).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.count_cons, List.filter_cons]
    have : (∑ e, if v ∈ G.ends e then (l.count e + if a = e then 1 else 0) else 0) =
        (∑ e, if v ∈ G.ends e then l.count e else 0) +
          ∑ e, if v ∈ G.ends e then (if a = e then 1 else 0) else 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun e _ => ?_
      split_ifs <;> simp
    simp only [beq_iff_eq]
    have key : (∑ e, if v ∈ G.ends e then (if a = e then 1 else 0) else 0) =
        if v ∈ G.ends a then 1 else 0 := by
      rw [Finset.sum_eq_single a]
      · simp
      · intro e _ hne; simp [Ne.symm hne]
      · simp
    rw [this, ih, key]
    by_cases h : v ∈ G.ends a <;> simp [h]

theorem mem_oddNodes_iff [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (v : V) :
    v ∈ oddNodes G ↔ Odd (degree G v) := by
  unfold oddNodes
  simp

noncomputable def reps [Fintype V] [Fintype E] [DecidableEq V]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (f : V → V) : Finset V := by
  classical
  exact (oddNodes G).filter (fun u => (Fintype.equivFin V u : ℕ) < (Fintype.equivFin V (f u) : ℕ))

theorem mem_reps [Fintype V] [Fintype E] [DecidableEq V]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (f : V → V) (u : V) :
    u ∈ reps G f ↔ u ∈ oddNodes G ∧
      (Fintype.equivFin V u : ℕ) < (Fintype.equivFin V (f u) : ℕ) := by
  unfold reps
  simp

theorem reps_sum [Fintype V] [Fintype E] [DecidableEq V]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (f : V → V) (hf : IsOddPerfectMatching G f)
    (v : V) :
    ∑ u ∈ reps G f, ((if v = u then 1 else 0) + (if v = f u then 1 else 0) : ℕ) =
      if v ∈ oddNodes G then 1 else 0 := by
  by_cases hv : v ∈ oddNodes G
  · rw [if_pos hv]
    obtain ⟨hfo, hne, hff⟩ := hf.1 v hv
    have hidx : (Fintype.equivFin V v : ℕ) ≠ (Fintype.equivFin V (f v) : ℕ) := by
      intro h
      exact hne ((Fintype.equivFin V).injective (Fin.ext h)).symm
    rcases lt_or_gt_of_ne hidx with hlt | hgt
    · rw [Finset.sum_eq_single v]
      · simp [hne.symm]
      · intro u hu huv
        rw [mem_reps] at hu
        have hfu := hf.1 u hu.1
        have h1 : v ≠ u := Ne.symm huv
        have h2 : v ≠ f u := by
          intro h
          have : f v = u := by rw [h, hfu.2.2]
          have e1 : f u = v := h.symm
          have h3 := hu.2
          rw [e1] at h3
          rw [this] at hlt
          omega
        simp [h1, h2]
      · intro h; exact absurd ((mem_reps G f v).2 ⟨hv, hlt⟩) h
    · rw [Finset.sum_eq_single (f v)]
      · simp [hne.symm, hff]
      · intro u hu hufv
        rw [mem_reps] at hu
        have hfu := hf.1 u hu.1
        have h2 : v ≠ f u := by
          intro h
          have : f v = u := by rw [h, hfu.2.2]
          exact hufv this.symm
        have h1 : v ≠ u := by
          intro h
          subst h
          have := hu.2
          omega
        simp [h1, h2]
      · intro h
        exfalso; apply h
        rw [mem_reps]
        refine ⟨hfo, ?_⟩
        rw [hff]; exact hgt
  · rw [if_neg hv]
    apply Finset.sum_eq_zero
    intro u hu
    rw [mem_reps] at hu
    have hfu := hf.1 u hu.1
    have h1 : v ≠ u := fun h => hv (h ▸ hu.1)
    have h2 : v ≠ f u := fun h => hv (h ▸ hfu.1)
    simp [h1, h2]

theorem parity_core [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (f : V → V) (hf : IsOddPerfectMatching G f)
    (L : V → List E) (hL : ∀ u ∈ oddNodes G, Wk G u (f u) (L u)) :
    IsParitySolution G (fun e => ∑ u ∈ reps G f, (L u).count e) := by
  rw [isParity_iff]
  intro v
  rw [incidentSum_eq]
  have h1 : ∀ e, (if v ∈ G.ends e then ∑ u ∈ reps G f, (L u).count e else 0) =
      ∑ u ∈ reps G f, if v ∈ G.ends e then (L u).count e else 0 := by
    intro e; split_ifs <;> simp
  simp only [h1]
  rw [Finset.sum_comm]
  simp only [sum_count_filter]
  rw [Finset.sum_nat_mod]
  have h2 : ∀ u ∈ reps G f, ((L u).filter (fun e => decide (v ∈ G.ends e))).length % 2 =
      ((if v = u then 1 else 0) + (if v = f u then 1 else 0) : ℕ) % 2 := by
    intro u hu
    rw [mem_reps] at hu
    exact (hL u hu.1).count_mod v
  rw [Finset.sum_congr rfl h2, ← Finset.sum_nat_mod, reps_sum G f hf]
  by_cases hv : Odd (degree G v)
  · rw [if_pos ((mem_oddNodes_iff G v).2 hv), if_pos hv]
  · rw [if_neg (fun h => hv ((mem_oddNodes_iff G v).1 h)), if_neg hv]

theorem zero_one_core [Fintype E] [DecidableEq V]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (c : E → ℝ) (hc : ∀ e, 0 ≤ c e)
    (x : E → ℕ) (hx : IsParitySolution G x) :
    ∃ x' : E → ℕ, IsParitySolution G x' ∧
      (∀ e, x' e ≤ 1) ∧ cost c x' ≤ cost c x := by
  refine ⟨fun e => x e % 2, ?_, fun e => by show x e % 2 ≤ 1; omega, ?_⟩
  · rw [isParity_iff] at hx ⊢
    intro v
    rw [← hx v, incidentSum_eq, incidentSum_eq, Finset.sum_nat_mod,
      Finset.sum_nat_mod (f := fun e => if v ∈ G.ends e then x e else 0)]
    congr 1
    apply Finset.sum_congr rfl
    intro e _
    split_ifs <;> simp
  · unfold cost
    apply Finset.sum_le_sum
    intro e _
    apply mul_le_mul_of_nonneg_left _ (hc e)
    exact_mod_cast Nat.mod_le (x e) 2

theorem exists_rep [Fintype V] [Fintype E] [DecidableEq V]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (f : V → V) (hf : IsOddPerfectMatching G f)
    (v : V) (hv : v ∈ oddNodes G) : ∃ u ∈ reps G f, u = v ∨ u = f v := by
  obtain ⟨hfo, hne, hff⟩ := hf.1 v hv
  have hidx : (Fintype.equivFin V v : ℕ) ≠ (Fintype.equivFin V (f v) : ℕ) := by
    intro h
    exact hne ((Fintype.equivFin V).injective (Fin.ext h)).symm
  rcases lt_or_gt_of_ne hidx with hlt | hgt
  · exact ⟨v, (mem_reps G f v).2 ⟨hv, hlt⟩, Or.inl rfl⟩
  · refine ⟨f v, (mem_reps G f (f v)).2 ⟨hfo, ?_⟩, Or.inr rfl⟩
    rw [hff]; exact hgt

theorem rep_ne_f [Fintype V] [Fintype E] [DecidableEq V]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (f : V → V) (hf : IsOddPerfectMatching G f)
    (u w : V) (hu : u ∈ reps G f) (hw : w ∈ reps G f) : w ≠ f u := by
  intro h
  rw [mem_reps] at hu hw
  have h1 := hu.2
  have h2 := hw.2
  rw [h] at h2
  have := (hf.1 u hu.1).2.2
  rw [this] at h2
  omega

theorem parity_of_edge_disjoint_paths_core [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (f : V → V) (hf : IsOddPerfectMatching G f)
    (P : V → List V × List E) (hP : MatchingPaths G f P) :
    IsParitySolution G (pathIndicator G P) := by
  have hcore := parity_core G f hf (fun v => (P v).2)
    (fun u hu => (hP.1 u hu).1.1.wk)
  convert hcore using 1
  funext e
  by_cases h : ∃ v ∈ oddNodes G, e ∈ (P v).2
  · have h1 : pathIndicator G P e = 1 := by unfold pathIndicator; rw [if_pos h]
    rw [h1]
    obtain ⟨v, hv, he⟩ := h
    obtain ⟨u, hu, huv⟩ := exists_rep G f hf v hv
    have hu' := (mem_reps G f u).1 hu
    have heu : e ∈ (P u).2 := by
      rcases huv with rfl | rfl
      · exact he
      · rw [(hP.1 v hv).2.2]; simpa using he
    rw [Finset.sum_eq_single u]
    · exact (List.count_eq_one_of_mem (hP.1 u hu'.1).1.2 heu).symm
    · intro w hw hwu
      have hw' := (mem_reps G f w).1 hw
      have : e ∉ (P w).2 := (hP.2 u w hu'.1 hw'.1 hwu (rep_ne_f G f hf u w hu hw) e heu)
      exact List.count_eq_zero.2 this
    · intro hh; exact absurd hu hh
  · have h1 : pathIndicator G P e = 0 := by unfold pathIndicator; rw [if_neg h]
    rw [h1]
    symm
    apply Finset.sum_eq_zero
    intro u hu
    have hu' := (mem_reps G f u).1 hu
    exact List.count_eq_zero.2 (fun he => h ⟨u, hu'.1, he⟩)

end WkSec
end ChinesePostman.Matching

open ChinesePostman.Matching


theorem solution
    {V E : Type*} [Fintype E] [DecidableEq V]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (c : E → ℝ) (hc : ∀ e, 0 ≤ c e)
    (x : E → ℕ) (hx : IsParitySolution G x) :
    ∃ x' : E → ℕ, IsParitySolution G x' ∧
      (∀ e, x' e ≤ 1) ∧ cost c x' ≤ cost c x := by
  exact zero_one_core G c hc x hx
