-- Prove2me | solution 1 for ChinesePostman.Matching.zero_one_parity_solution_decomposes
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T07:40:43.629441+00:00
-- url     : https://prove2.me/submissions/5f308e55-6338-4e68-888e-b94fe755120e

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

def degS [DecidableEq V] (G : EdmondsMatching65.Polyhedron.Graph V E) (S : Finset E) (v : V) : ℕ :=
  (S.filter (fun e => v ∈ G.ends e)).card

theorem degS_univ [Fintype E] [DecidableEq V] (G : EdmondsMatching65.Polyhedron.Graph V E) (v : V) :
    degree G v = degS G Finset.univ v := by
  classical
  unfold degree degS
  congr

theorem degS_sdiff [DecidableEq V] [DecidableEq E] (G : EdmondsMatching65.Polyhedron.Graph V E)
    {T S : Finset E} (hT : T ⊆ S) (v : V) : degS G S v = degS G T v + degS G (S \ T) v := by
  unfold degS
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext e
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases h : e ∈ T
      · exact Or.inl ⟨h, h2⟩
      · exact Or.inr ⟨⟨h1, h⟩, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨⟨h1, _⟩, h2⟩)
      · exact ⟨hT h1, h2⟩
      · exact ⟨h1, h2⟩
  · rw [Finset.disjoint_left]
    intro e h1 h2
    simp only [Finset.mem_filter, Finset.mem_sdiff] at h1 h2
    exact h2.1.2 h1.1

theorem degS_list [DecidableEq V] [DecidableEq E] (G : EdmondsMatching65.Polyhedron.Graph V E)
    {es : List E} (h : es.Nodup) (v : V) :
    degS G es.toFinset v = (es.filter (fun e => decide (v ∈ G.ends e))).length := by
  unfold degS
  rw [show es.toFinset.filter (fun e => v ∈ G.ends e) =
      (es.filter (fun e => decide (v ∈ G.ends e))).toFinset from by ext e; simp]
  rw [List.toFinset_card_of_nodup (h.filter _)]

theorem incidentSum_01 [Fintype E] [DecidableEq V]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (x : E → ℕ) (hx : ∀ e, x e ≤ 1) (v : V) :
    incidentSum G x v = degS G (Finset.univ.filter (fun e => x e = 1)) v := by
  classical
  rw [incidentSum_eq]
  unfold degS
  rw [Finset.card_filter]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  have := hx e
  by_cases h1 : v ∈ G.ends e <;> by_cases h2 : x e = 1 <;> simp [h1, h2] <;> omega

theorem Wk.split [DecidableEq V] {G : EdmondsMatching65.Polyhedron.Graph V E} {a b : V}
    {es : List E} (h : Wk G a b es) (z : V) (hz : z = a ∨ ∃ e ∈ es, z ∈ G.ends e) :
    ∃ es1 es2, es = es1 ++ es2 ∧ Wk G a z es1 ∧ Wk G z b es2 := by
  induction h with
  | nil a =>
    rcases hz with rfl | ⟨e, he, _⟩
    · exact ⟨[], [], rfl, Wk.nil _, Wk.nil _⟩
    · simp at he
  | cons a a' b e es he hw ih =>
    by_cases hza : z = a
    · subst hza
      exact ⟨[], e :: es, rfl, Wk.nil _, Wk.cons _ a' b e es he hw⟩
    · by_cases hza' : z = a'
      · subst hza'
        exact ⟨[e], es, rfl, Wk.cons a z z e [] he (Wk.nil _), hw⟩
      · have hz' : z = a' ∨ ∃ e' ∈ es, z ∈ G.ends e' := by
          rcases hz with h1 | ⟨e', he', hze'⟩
          · exact absurd h1 hza
          · rcases List.mem_cons.1 he' with rfl | hm
            · rw [he] at hze'
              simp at hze'
              rcases hze' with h | h
              · exact absurd h hza
              · exact absurd h hza'
            · exact Or.inr ⟨e', hm, hze'⟩
        obtain ⟨es1, es2, hes, h1, h2⟩ := ih hz'
        exact ⟨e :: es1, es2, by simp [hes], Wk.cons a a' z e es1 he h1, h2⟩

theorem exists_max_trail [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (S : Finset E) (w : V) :
    ∃ z es, Wk G w z es ∧ es.Nodup ∧ (∀ e ∈ es, e ∈ S) ∧ ∀ e ∈ S, z ∈ G.ends e → e ∈ es := by
  let s : Set ℕ := {n | ∃ z es, Wk G w z es ∧ es.Nodup ∧ (∀ e ∈ es, e ∈ S) ∧ es.length = n}
  have hne : s.Nonempty := ⟨0, w, [], Wk.nil w, List.nodup_nil, by simp, rfl⟩
  have hbd : BddAbove s := by
    refine ⟨S.card, ?_⟩
    rintro n ⟨z, es, _, hnd, hsub, rfl⟩
    have : es.toFinset ⊆ S := fun e he => hsub e (List.mem_toFinset.1 he)
    calc es.length = es.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
      _ ≤ S.card := Finset.card_le_card this
  obtain ⟨z, es, hw, hnd, hsub, hlen⟩ := Nat.sSup_mem hne hbd
  refine ⟨z, es, hw, hnd, hsub, ?_⟩
  by_contra hcon
  push_neg at hcon
  obtain ⟨e, heS, hze, hnot⟩ := hcon
  obtain ⟨z', hz'⟩ := Sym2.mem_iff_exists.1 hze
  have hmem : es.length + 1 ∈ s := by
    refine ⟨z', es ++ [e], hw.append (Wk.cons z z' z' e [] hz' (Wk.nil _)), ?_, ?_, by simp⟩
    · rw [List.nodup_append]
      refine ⟨hnd, by simp, ?_⟩
      intro a ha b hb
      simp at hb; subst hb
      intro hh; subst hh; exact hnot ha
    · intro a ha
      rcases List.mem_append.1 ha with h | h
      · exact hsub a h
      · simp at h; subst h; exact heS
  have := le_csSup hbd hmem
  omega

theorem exists_euler_tour_core [Fintype V] [Nonempty V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (hG : Connected G)
    (heven : ∀ v, Even (degree G v)) :
    ∃ ns : List V, ∃ es : List E, IsEulerTour G ns es := by
  obtain v0 : V := Classical.arbitrary V
  let s : Set ℕ := {n | ∃ es, Wk G v0 v0 es ∧ es.Nodup ∧ es.length = n}
  have hne : s.Nonempty := ⟨0, [], Wk.nil v0, List.nodup_nil, rfl⟩
  have hbd : BddAbove s := by
    refine ⟨Fintype.card E, ?_⟩
    rintro n ⟨es, _, hnd, rfl⟩
    exact hnd.length_le_card
  obtain ⟨es, hw, hnd, hlen⟩ := Nat.sSup_mem hne hbd
  have hall : ∀ e, e ∈ es := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨e, he⟩ := hcon
    -- Step 1
    have hz : ∃ z, (z = v0 ∨ ∃ e1 ∈ es, z ∈ G.ends e1) ∧ ∃ e' ∉ es, z ∈ G.ends e' := by
      by_contra hcon2
      push_neg at hcon2
      have hreach : ∀ a b es', Wk G a b es' → (a = v0 ∨ ∃ e1 ∈ es, a ∈ G.ends e1) →
          (b = v0 ∨ ∃ e1 ∈ es, b ∈ G.ends e1) := by
        intro a b es' h
        induction h with
        | nil a => exact id
        | cons a a' b e1 es1 he1 _ ih =>
          intro ha
          apply ih
          have hmem : e1 ∈ es := by
            by_contra hh
            exact hcon2 a ha e1 hh (by rw [he1]; simp)
          exact Or.inr ⟨e1, hmem, by rw [he1]; simp⟩
      obtain ⟨a, b, hab⟩ := Sym2.exists.1 (⟨G.ends e, rfl⟩ : ∃ q, q = G.ends e)
      obtain ⟨ns, es', hwk⟩ := hG v0 a
      have hN := hreach v0 a es' hwk.wk (Or.inl rfl)
      exact hcon2 a hN e he (by rw [← hab]; simp)
    obtain ⟨z, hzN, e', he', hze'⟩ := hz
    obtain ⟨es1, es2, hes, hw1, hw2⟩ := hw.split z hzN
    -- Step 2
    set S' : Finset E := Finset.univ \ es.toFinset with hS'
    have hevenS : ∀ v, Even (degS G S' v) := by
      intro v
      have h1 := degS_sdiff G (Finset.subset_univ es.toFinset) v
      rw [← degS_univ] at h1
      rw [← hS'] at h1
      have h2 := degS_list G hnd v
      have h3 := hw.count_mod v
      have h4 := heven v
      rw [Nat.even_iff] at h4 ⊢
      rw [h2] at h1
      split_ifs at h3 <;> omega
    obtain ⟨z', loop, hwl, hnl, hsubl, hmax⟩ := exists_max_trail G S' z
    have hS'mem : ∀ e1, e1 ∈ S' ↔ e1 ∉ es := by
      intro e1; simp [hS']
    have hz'z : z' = z := by
      by_contra hne'
      have h3 := hwl.count_mod z'
      rw [if_neg hne', if_pos rfl] at h3
      have h5 : degS G S' z' = degS G loop.toFinset z' := by
        unfold degS
        congr 1
        ext e1
        simp only [Finset.mem_filter, List.mem_toFinset]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨hmax e1 h1 h2, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨hsubl e1 h1, h2⟩
      have h6 := hevenS z'
      rw [h5, degS_list G hnl, Nat.even_iff] at h6
      omega
    subst hz'z
    have hloopmem : e' ∈ loop := hmax e' ((hS'mem e').2 he') hze'
    -- Step 4
    have hnew : Wk G v0 v0 (es1 ++ (loop ++ es2)) := hw1.append (hwl.append hw2)
    have hnd' : (es1 ++ (loop ++ es2)).Nodup := by
      have hperm : (es1 ++ (loop ++ es2)).Perm (loop ++ es) := by
        rw [hes]
        have p1 : List.Perm (es1 ++ (loop ++ es2)) (es1 ++ loop ++ es2) := by
          rw [List.append_assoc]
        have p2 : List.Perm (es1 ++ loop ++ es2) (loop ++ es1 ++ es2) :=
          (List.perm_append_comm).append_right _
        have p3 : (loop ++ es1 ++ es2) = loop ++ (es1 ++ es2) := List.append_assoc _ _ _
        rw [p3] at p2
        exact p1.trans p2
      rw [hperm.nodup_iff, List.nodup_append]
      refine ⟨hnl, hnd, ?_⟩
      intro a ha b hb hab
      subst hab
      exact ((hS'mem a).1 (hsubl a ha)) hb
    have hle : (es1 ++ (loop ++ es2)).length ≤ sSup s := le_csSup hbd ⟨_, hnew, hnd', rfl⟩
    have hlen' : (es1 ++ (loop ++ es2)).length = es.length + loop.length := by
      have : es.length = es1.length + es2.length := by rw [hes]; simp
      simp; omega
    have hpos : 0 < loop.length := List.length_pos_of_mem hloopmem
    omega
  obtain ⟨ns, hns⟩ := hw.exists_walk
  refine ⟨ns, es, ⟨⟨hns.1, by rw [hns.2.1, hns.2.2]⟩, fun e => ?_⟩⟩
  exact List.count_eq_one_of_mem hnd (hall e)

def PairData [DecidableEq V] (G : EdmondsMatching65.Polyhedron.Graph V E) (O : Finset V)
    (S : Finset E) (f : V → V) (L : V → List E) : Prop :=
  (∀ v ∈ O, f v ∈ O ∧ f v ≠ v ∧ f (f v) = v) ∧ (∀ v ∉ O, f v = v) ∧
  (∀ v ∈ O, Wk G v (f v) (L v) ∧ (L v).Nodup ∧ (∀ e ∈ L v, e ∈ S) ∧ L (f v) = (L v).reverse) ∧
  (∀ v ∈ O, ∀ w ∈ O, w ≠ v → w ≠ f v → ∀ e ∈ L v, e ∉ L w)

theorem PairData.insert [DecidableEq V] [DecidableEq E]
    {G : EdmondsMatching65.Polyhedron.Graph V E} {O : Finset V} {S : Finset E}
    {f' : V → V} {L' : V → List E} {w z : V} {es : List E}
    (hwz : w ≠ z) (hwO : w ∈ O) (hzO : z ∈ O) (hes : Wk G w z es) (hnd : es.Nodup)
    (hT : es.toFinset ⊆ S)
    (hPD : PairData G ((O.erase w).erase z) (S \ es.toFinset) f' L') :
    ∃ f L, PairData G O S f L := by
  obtain ⟨h1, h2, h3, h4⟩ := hPD
  have hO' : ∀ v, v ∈ (O.erase w).erase z ↔ v ≠ z ∧ v ≠ w ∧ v ∈ O := by
    intro v; simp [Finset.mem_erase]
  have hzw : z ≠ w := hwz.symm
  have hmemT : ∀ e, e ∈ es → e ∈ S := fun e he => hT (List.mem_toFinset.2 he)
  have hSS : ∀ e, e ∈ S \ es.toFinset → e ∈ S ∧ e ∉ es := by
    intro e he; simpa using he
  obtain ⟨f, hf⟩ : ∃ f : V → V, f = fun v => if v = w then z else if v = z then w else f' v := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : V → List E,
      L = fun v => if v = w then es else if v = z then es.reverse else L' v := ⟨_, rfl⟩
  have fw : f w = z := by rw [hf]; simp
  have fz : f z = w := by rw [hf]; simp [hzw]
  have fo : ∀ v, v ≠ w → v ≠ z → f v = f' v := by intro v a b; rw [hf]; simp [a, b]
  have Lw : L w = es := by rw [hL]; simp
  have Lz : L z = es.reverse := by rw [hL]; simp [hzw]
  have Lo : ∀ v, v ≠ w → v ≠ z → L v = L' v := by intro v a b; rw [hL]; simp [a, b]
  refine ⟨f, L, ?_, ?_, ?_, ?_⟩
  · intro v hv
    by_cases hvw : v = w
    · subst hvw; rw [fw, fz]; exact ⟨hzO, hzw, rfl⟩
    · by_cases hvz : v = z
      · subst hvz; rw [fz, fw]; exact ⟨hwO, hwz, rfl⟩
      · have hv' : v ∈ (O.erase w).erase z := (hO' v).2 ⟨hvz, hvw, hv⟩
        obtain ⟨a1, a2, a3⟩ := h1 v hv'
        have b := (hO' (f' v)).1 a1
        rw [fo v hvw hvz, fo _ b.2.1 b.1, a3]
        exact ⟨b.2.2, a2, rfl⟩
  · intro v hv
    have hvw : v ≠ w := fun h => hv (h ▸ hwO)
    have hvz : v ≠ z := fun h => hv (h ▸ hzO)
    have : v ∉ (O.erase w).erase z := fun h => hv ((hO' v).1 h).2.2
    rw [fo v hvw hvz, h2 v this]
  · intro v hv
    by_cases hvw : v = w
    · subst hvw
      rw [fw, Lw, Lz]
      exact ⟨hes, hnd, hmemT, rfl⟩
    · by_cases hvz : v = z
      · subst hvz
        rw [fz, Lz, Lw]
        exact ⟨hes.reverse, List.nodup_reverse.2 hnd, fun e he => hmemT e (List.mem_reverse.1 he), by simp⟩
      · have hv' : v ∈ (O.erase w).erase z := (hO' v).2 ⟨hvz, hvw, hv⟩
        obtain ⟨a1, a2, a3⟩ := h1 v hv'
        have b := (hO' (f' v)).1 a1
        obtain ⟨c1, c2, c3, c4⟩ := h3 v hv'
        rw [fo v hvw hvz, Lo v hvw hvz, Lo _ b.2.1 b.1]
        exact ⟨c1, c2, fun e he => (hSS e (c3 e he)).1, c4⟩
  · intro v hv u hu huv hufv e he
    by_cases hvw : v = w
    · subst hvw
      rw [fw] at hufv
      rw [Lw] at he
      have hu1 : u ≠ v := huv
      have hu2 : u ≠ z := hufv
      rw [Lo u hu1 hu2]
      intro hh
      have hu' : u ∈ (O.erase v).erase z := (hO' u).2 ⟨hu2, hu1, hu⟩
      exact (hSS e ((h3 u hu').2.2.1 e hh)).2 he
    · by_cases hvz : v = z
      · subst hvz
        rw [fz] at hufv
        rw [Lz] at he
        have he' : e ∈ es := List.mem_reverse.1 he
        have hu1 : u ≠ w := hufv
        have hu2 : u ≠ v := huv
        rw [Lo u hu1 hu2]
        intro hh
        have hu' : u ∈ (O.erase w).erase v := (hO' u).2 ⟨hu2, hu1, hu⟩
        exact (hSS e ((h3 u hu').2.2.1 e hh)).2 he'
      · have hv' : v ∈ (O.erase w).erase z := (hO' v).2 ⟨hvz, hvw, hv⟩
        rw [Lo v hvw hvz] at he
        have heS := (hSS e ((h3 v hv').2.2.1 e he))
        by_cases huw : u = w
        · subst huw; rw [Lw]; exact fun hh => heS.2 hh
        · by_cases huz : u = z
          · subst huz; rw [Lz]; exact fun hh => heS.2 (List.mem_reverse.1 hh)
          · have hu' : u ∈ (O.erase w).erase z := (hO' u).2 ⟨huz, huw, hu⟩
            rw [fo v hvw hvz] at hufv
            rw [Lo u huw huz]
            exact h4 v hv' u hu' huv hufv e he

theorem exists_pairdata [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) :
    ∀ n, ∀ S : Finset E, S.card = n →
      ∃ f L, PairData G (Finset.univ.filter (fun v => Odd (degS G S v))) S f L := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S hS
  by_cases hO : (Finset.univ.filter (fun v => Odd (degS G S v))) = ∅
  · refine ⟨id, fun _ => [], ?_⟩
    rw [hO]
    exact ⟨by simp, by simp, by simp, by simp⟩
  · obtain ⟨w, hw⟩ := Finset.nonempty_iff_ne_empty.2 hO
    have hwodd : Odd (degS G S w) := by simpa using hw
    obtain ⟨z, es, hwk, hnd, hsub, hmax⟩ := exists_max_trail G S w
    have hT : es.toFinset ⊆ S := fun e he => hsub e (List.mem_toFinset.1 he)
    have hdz : degS G S z = degS G es.toFinset z := by
      unfold degS
      congr 1
      ext e
      simp only [Finset.mem_filter, List.mem_toFinset]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨hmax e h1 h2, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨hsub e h1, h2⟩
    have hcz := hwk.count_mod z
    have hTz := degS_list G hnd z
    have hzw : z ≠ w := by
      intro h
      subst h
      simp at hcz
      rw [Nat.odd_iff] at hwodd
      rw [← hTz] at hcz
      omega
    have hzodd : Odd (degS G S z) := by
      rw [Nat.odd_iff, hdz, hTz]
      simp [hzw] at hcz
      omega
    have hdeg : ∀ v, degS G S v = degS G es.toFinset v + degS G (S \ es.toFinset) v :=
      degS_sdiff G hT
    have hO' : (Finset.univ.filter (fun v => Odd (degS G (S \ es.toFinset) v))) =
        ((Finset.univ.filter (fun v => Odd (degS G S v))).erase w).erase z := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      have hc := hwk.count_mod v
      have hd := hdeg v
      rw [degS_list G hnd v] at hd
      rw [Nat.odd_iff, Nat.odd_iff]
      by_cases hvw : v = w
      · subst hvw
        simp [hzw.symm] at hc
        rw [Nat.odd_iff] at hwodd
        simp
        omega
      · by_cases hvz : v = z
        · subst hvz
          simp [hvw] at hc
          rw [Nat.odd_iff] at hzodd
          simp
          omega
        · simp [hvw, hvz] at hc ⊢
          omega
    have hne : es ≠ [] := by
      intro h
      rw [h] at hwk
      cases hwk
      exact hzw rfl
    have hcard : (S \ es.toFinset).card < n := by
      rw [← hS]
      apply Finset.card_lt_card
      apply Finset.sdiff_ssubset hT
      obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil es hne
      exact ⟨e, List.mem_toFinset.2 he⟩
    obtain ⟨f', L', hPD⟩ := ih _ hcard (S \ es.toFinset) rfl
    rw [hO'] at hPD
    have hwO : w ∈ (Finset.univ.filter (fun v => Odd (degS G S v))) := hw
    have hzO : z ∈ (Finset.univ.filter (fun v => Odd (degS G S v))) := by simpa using hzodd
    exact PairData.insert hzw.symm hwO hzO hwk hnd hT hPD

theorem lift_paths [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (S : Finset E) (f : V → V) (L : V → List E)
    (hPD : PairData G (oddNodes G) S f L) :
    IsOddPerfectMatching G f ∧
      ∃ P : V → List V × List E, MatchingPaths G f P ∧ ∀ v ∈ oddNodes G, (P v).2 = L v := by
  classical
  obtain ⟨h1, h2, h3, h4⟩ := hPD
  refine ⟨⟨h1, h2⟩, ?_⟩
  let C : V → List V := fun u =>
    if h : Wk G u (f u) (L u) then Classical.choose h.exists_walk else []
  have hC : ∀ u, Wk G u (f u) (L u) → IsWalkFrom G u (f u) (C u) (L u) := by
    intro u hu
    simp only [C, dif_pos hu]
    exact Classical.choose_spec hu.exists_walk
  let N : V → List V := fun v =>
    if (Fintype.equivFin V v : ℕ) < (Fintype.equivFin V (f v) : ℕ) then C v else (C (f v)).reverse
  have hrevwalk : ∀ u ns, IsWalkFrom G u (f u) ns (L u) → u ∈ oddNodes G →
      IsWalkFrom G (f u) u ns.reverse (L (f u)) := by
    intro u ns hw hu
    obtain ⟨hw1, hh, hl⟩ := hw
    refine ⟨?_, ?_, ?_⟩
    · rw [(h3 u hu).2.2.2]; exact hw1.reverse
    · rw [List.head?_reverse]; exact hl
    · rw [List.getLast?_reverse]; exact hh
  have hN : ∀ v ∈ oddNodes G, IsWalkFrom G v (f v) (N v) (L v) := by
    intro v hv
    obtain ⟨hfo, hne, hff⟩ := h1 v hv
    by_cases hlt : (Fintype.equivFin V v : ℕ) < (Fintype.equivFin V (f v) : ℕ)
    · simp only [N, if_pos hlt]
      exact hC v (h3 v hv).1
    · simp only [N, if_neg hlt]
      have := hrevwalk (f v) (C (f v)) (hC (f v) (h3 (f v) hfo).1) hfo
      rw [hff] at this
      exact this
  have hidx : ∀ v ∈ oddNodes G, (Fintype.equivFin V v : ℕ) ≠ (Fintype.equivFin V (f v) : ℕ) := by
    intro v hv h
    exact (h1 v hv).2.1 ((Fintype.equivFin V).injective (Fin.ext h)).symm
  refine ⟨fun v => (N v, L v), ⟨?_, ?_⟩, fun v _ => rfl⟩
  · intro v hv
    obtain ⟨hfo, hne, hff⟩ := h1 v hv
    refine ⟨⟨hN v hv, (h3 v hv).2.1⟩, ?_, (h3 v hv).2.2.2⟩
    show N (f v) = (N v).reverse
    by_cases hlt : (Fintype.equivFin V v : ℕ) < (Fintype.equivFin V (f v) : ℕ)
    · have : ¬ (Fintype.equivFin V (f v) : ℕ) < (Fintype.equivFin V (f (f v)) : ℕ) := by
        rw [hff]; omega
      simp only [N, if_pos hlt, if_neg this, hff]
    · have hgt : (Fintype.equivFin V (f v) : ℕ) < (Fintype.equivFin V (f (f v)) : ℕ) := by
        rw [hff]; have := hidx v hv; omega
      simp only [N, if_neg hlt, if_pos hgt, List.reverse_reverse]
  · intro v w hv hw hwv hwf e he
    exact h4 v hv w hw hwv hwf e he

theorem zero_one_parity_solution_decomposes_core [Fintype V] [Fintype E] [DecidableEq V]
    [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (x : E → ℕ) (hx : IsParitySolution G x)
    (hx01 : ∀ e, x e ≤ 1) :
    ∃ f : V → V, IsOddPerfectMatching G f ∧
      ∃ P : V → List V × List E, MatchingPaths G f P ∧
        ∀ v ∈ oddNodes G, ∀ e ∈ (P v).2, x e = 1 := by
  classical
  set S : Finset E := Finset.univ.filter (fun e => x e = 1) with hS
  have hO : oddNodes G = Finset.univ.filter (fun v => Odd (degS G S v)) := by
    ext v
    rw [isParity_iff] at hx
    have h := hx v
    have h' : incidentSum G x v = degS G S v := incidentSum_01 G x hx01 v
    rw [h'] at h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [mem_oddNodes_iff, Nat.odd_iff, Nat.odd_iff]
    by_cases hv : Odd (degree G v)
    · rw [if_pos hv] at h
      rw [Nat.odd_iff] at hv
      omega
    · rw [if_neg hv] at h
      rw [Nat.odd_iff] at hv
      omega
  obtain ⟨f, L, hPD⟩ := exists_pairdata G _ S rfl
  rw [← hO] at hPD
  obtain ⟨hm, P, hP, hPL⟩ := lift_paths G S f L hPD
  refine ⟨f, hm, P, hP, ?_⟩
  intro v hv e he
  rw [hPL v hv] at he
  have := (hPD.2.2.1 v hv).2.2.1 e he
  simpa [hS] using this

end WkSec
end ChinesePostman.Matching

open ChinesePostman.Matching


theorem solution
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (x : E → ℕ) (hx : IsParitySolution G x)
    (hx01 : ∀ e, x e ≤ 1) :
    ∃ f : V → V, IsOddPerfectMatching G f ∧
      ∃ P : V → List V × List E, MatchingPaths G f P ∧
        ∀ v ∈ oddNodes G, ∀ e ∈ (P v).2, x e = 1 := by
  exact zero_one_parity_solution_decomposes_core G x hx hx01
