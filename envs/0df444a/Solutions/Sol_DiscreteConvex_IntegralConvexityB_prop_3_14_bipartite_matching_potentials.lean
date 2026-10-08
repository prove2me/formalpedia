-- Prove2me | solution 1 for DiscreteConvex.IntegralConvexityB.prop_3_14_bipartite_matching_potentials
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T00:39:23.439043+00:00
-- url     : https://prove2.me/submissions/b774a7e9-e7d3-4b4f-8df4-a1b36a88f24c

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityB_IsPerfectMatchingBij
import Definitions.Def_DiscreteConvex_IntegralConvexityB_IsMinWeightMatching
import Definitions.Def_DiscreteConvex_IntegralConvexityB_MatchingWeight



namespace DiscreteConvex.IntegralConvexityB

/-- path cost -/
def pcost {α : Type*} (w : α → α → ℝ) : List α → ℝ
  | a :: b :: t => w a b + pcost w (b :: t)
  | _ => 0

lemma pcost_append {α : Type*} (w : α → α → ℝ) (l1 : List α) (x : α) (l2 : List α) :
    pcost w (l1 ++ x :: l2) = pcost w (l1 ++ [x]) + pcost w (x :: l2) := by
  induction l1 with
  | nil => simp [pcost]
  | cons a l1 ih =>
    cases l1 with
    | nil => simp [pcost]
    | cons b l1' =>
      simp only [List.cons_append] at ih ⊢
      rw [pcost, pcost, ih]; ring

lemma pcost_cons_snoc {α : Type*} (w : α → α → ℝ) (a : α) (l : List α) (z : α) :
    pcost w (a :: (l ++ [z])) = w a ((l ++ [z]).headD z) + pcost w (l ++ [z]) := by
  cases l with
  | nil => simp [pcost]
  | cons b l => simp [pcost]

lemma pcost_lb {α : Type*} (w : α → α → ℝ) (M : ℝ) (hM : ∀ a b, -M ≤ w a b) (hM0 : 0 ≤ M) :
    ∀ l : List α, -((l.length : ℝ) * M) ≤ pcost w l := by
  intro l
  induction l with
  | nil => simp [pcost]
  | cons a t ih =>
    cases t with
    | nil => simp [pcost]; exact hM0
    | cons b t =>
      rw [pcost]
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at ih ⊢
      nlinarith [hM a b]

lemma cyc_perm {α : Type*} [Fintype α] [DecidableEq α] (arc : α → α → Prop) (w : α → α → ℝ)
    (hw0 : ∀ u, w u u = 0) :
    ∀ (l : List α) (z : α), (l ++ [z]).Nodup → List.IsChain arc (l ++ [z]) →
      ∃ ρ : Equiv.Perm α, (∀ x, x ∉ l ++ [z] → ρ x = x) ∧ (∀ x, x ≠ z → ρ x = x ∨ arc x (ρ x)) ∧
        ρ z = (l ++ [z]).headD z ∧
        ∑ x, w x (ρ x) = pcost w (l ++ [z]) + w z ((l ++ [z]).headD z) := by
  intro l
  induction l with
  | nil =>
    intro z _ _
    refine ⟨1, fun x _ => rfl, fun x _ => Or.inl rfl, rfl, ?_⟩
    simp [hw0, pcost]
  | cons a l ih =>
    intro z hnd hch
    have hnd' : (l ++ [z]).Nodup := (List.nodup_cons.mp (by simpa using hnd)).2
    have ha : a ∉ l ++ [z] := (List.nodup_cons.mp (by simpa using hnd)).1
    have hch' : List.IsChain arc (a :: (l ++ [z])) := by simpa using hch
    rw [List.isChain_cons] at hch'
    obtain ⟨ρ0, h1, h2, h3, h4⟩ := ih z hnd' hch'.2
    set h0 := (l ++ [z]).headD z with hh0
    have harc : arc a h0 := by
      apply hch'.1
      cases l <;> simp [hh0]
    have hz : z ∈ l ++ [z] := by simp
    have haz : a ≠ z := fun h => ha (h ▸ hz)
    refine ⟨ρ0 * Equiv.swap a z, ?_, ?_, ?_, ?_⟩
    · intro x hx
      have hxa : x ≠ a := fun h => hx (by simp [h])
      have hxm : x ∉ l ++ [z] := fun h => hx (by simp at h ⊢; tauto)
      have hxz : x ≠ z := fun h => hxm (h ▸ hz)
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hxa hxz, h1 x hxm]
    · intro x hxz
      by_cases hxa : x = a
      · subst hxa
        right
        rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, h3]; exact harc
      · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hxa hxz]
        exact h2 x hxz
    · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right, h1 a ha]; simp
    · have hpt : ∀ x, w x ((ρ0 * Equiv.swap a z) x) = w x (ρ0 x) +
          ((if x = a then w a h0 else 0) + (if x = z then w z a - w z h0 else 0)) := by
        intro x
        by_cases hxa : x = a
        · subst hxa
          rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, h3, h1 x ha, if_pos rfl, if_neg haz, hw0]
          ring
        · by_cases hxz : x = z
          · subst hxz
            rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right, h1 a ha, if_neg hxa, if_pos rfl, h3]
            ring
          · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hxa hxz, if_neg hxa, if_neg hxz]
            ring
      simp_rw [hpt]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ a,
        Finset.sum_ite_eq' Finset.univ z, h4]
      simp only [Finset.mem_univ, if_true, List.cons_append, List.headD_cons]
      rw [pcost_cons_snoc]
      ring

lemma potential_exists {α : Type*} [Fintype α] [DecidableEq α] (arc : α → α → Prop)
    (w : α → α → ℝ) (hw0 : ∀ u, w u u = 0)
    (hcyc : ∀ ρ : Equiv.Perm α, (∀ x, ρ x = x ∨ arc x (ρ x)) → 0 ≤ ∑ x, w x (ρ x)) :
    ∃ π : α → ℝ, ∀ u u', arc u u' → π u' ≤ π u + w u u' := by
  let P : α → Set ℝ := fun u' => {r | ∃ l : List α, (l ++ [u']).Nodup ∧
    List.IsChain arc (l ++ [u']) ∧ r = pcost w (l ++ [u'])}
  set M : ℝ := ∑ a, ∑ b, |w a b| with hMdef
  have hM : ∀ a b, -M ≤ w a b := by
    intro a b
    have h1 : |w a b| ≤ ∑ b, |w a b| :=
      Finset.single_le_sum (f := fun b => |w a b|) (fun _ _ => abs_nonneg _) (Finset.mem_univ b)
    have h2 : ∑ b, |w a b| ≤ M :=
      Finset.single_le_sum (f := fun a => ∑ b, |w a b|)
        (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (Finset.mem_univ a)
    linarith [neg_abs_le (w a b)]
  have hM0 : 0 ≤ M := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  have hne : ∀ u', (P u').Nonempty := fun u' => ⟨_, [], by simp, by simp, rfl⟩
  have hbdd : ∀ u', BddBelow (P u') := by
    intro u'
    refine ⟨-((Fintype.card α : ℝ) * M), ?_⟩
    rintro r ⟨l, hnd, -, rfl⟩
    have := pcost_lb w M hM hM0 (l ++ [u'])
    have hlen : ((l ++ [u']).length : ℝ) ≤ Fintype.card α := by exact_mod_cast hnd.length_le_card
    nlinarith
  refine ⟨fun u' => sInf (P u'), fun u u' huu' => ?_⟩
  have key : ∀ l : List α, (l ++ [u]).Nodup → List.IsChain arc (l ++ [u]) →
      ∃ l' : List α, (l' ++ [u']).Nodup ∧ List.IsChain arc (l' ++ [u']) ∧
        pcost w (l' ++ [u']) ≤ pcost w (l ++ [u]) + w u u' := by
    intro l hnd hch
    by_cases hin : u' ∈ l ++ [u]
    · by_cases hEq : u' = u
      · subst hEq; exact ⟨l, hnd, hch, by rw [hw0]; linarith⟩
      · have hl : u' ∈ l := by simp at hin; tauto
        obtain ⟨l1, l2, rfl⟩ := List.append_of_mem hl
        have heq : l1 ++ u' :: l2 ++ [u] = (l1 ++ [u']) ++ (l2 ++ [u]) := by simp
        have heq2 : l1 ++ u' :: l2 ++ [u] = l1 ++ ((u' :: l2) ++ [u]) := by simp
        refine ⟨l1, ?_, ?_, ?_⟩
        · rw [heq] at hnd; exact (List.nodup_append.mp hnd).1
        · rw [heq] at hch; exact hch.left_of_append
        · have hnd2 : ((u' :: l2) ++ [u]).Nodup := by
            rw [heq2] at hnd; exact (List.nodup_append.mp hnd).2.1
          have hch2 : List.IsChain arc ((u' :: l2) ++ [u]) := by
            rw [heq2] at hch; exact hch.right_of_append
          obtain ⟨ρ, -, h2, h3, h4⟩ := cyc_perm arc w hw0 (u' :: l2) u hnd2 hch2
          have hc := hcyc ρ (fun x => by
            by_cases hx : x = u
            · subst hx; right; rw [h3]; simpa using huu'
            · exact h2 x hx)
          rw [h4] at hc
          simp only [List.cons_append, List.headD_cons] at hc
          have hsplit := pcost_append w l1 u' (l2 ++ [u])
          simp only [List.append_assoc, List.cons_append] at hsplit ⊢
          linarith
    · refine ⟨l ++ [u], ?_, ?_, ?_⟩
      · rw [List.nodup_append]
        exact ⟨hnd, by simp, fun a ha b hb => by simp at hb; subst hb; exact fun h => hin (h ▸ ha)⟩
      · apply List.IsChain.append hch (List.isChain_singleton _)
        intro x hx y hy
        simp at hx hy; subst hx; subst hy; exact huu'
      · have := pcost_append w l u [u']
        simp only [List.append_assoc, List.cons_append, List.nil_append] at this ⊢
        rw [this]; simp [pcost]
  have : sInf (P u') - w u u' ≤ sInf (P u) := by
    apply le_csInf (hne u)
    rintro r ⟨l, hnd, hch, rfl⟩
    obtain ⟨l', hnd', hch', hle⟩ := key l hnd hch
    have := csInf_le (hbdd u') ⟨l', hnd', hch', rfl⟩
    linarith
  linarith


theorem bm314_core {Vp Vm : Type*} [Fintype Vp] [Fintype Vm]
    [DecidableEq Vp] [DecidableEq Vm] (E : Set (Vp × Vm)) (c : Vp × Vm → WithTop ℝ)
    (hc : ∀ u v, c (u, v) < ⊤ ↔ (u, v) ∈ E) (sigma0 : Vp ≃ Vm)
    (hsigma0 : IsPerfectMatchingBij E sigma0) :
    ∃ (pp : Vp → ℝ) (pm : Vm → ℝ) (sigma : Vp ≃ Vm),
      (∀ u, c (u, sigma u) + (pp u : WithTop ℝ) - (pm (sigma u) : WithTop ℝ) = 0) ∧
        (∀ u v, c (u, v) + (pp u : WithTop ℝ) - (pm v : WithTop ℝ) ≥ 0) ∧
        IsMinWeightMatching E c sigma ∧
        MatchingWeight c sigma = ((∑ u, (pm (sigma u) - pp u) : ℝ) : WithTop ℝ) := by
  classical
  let cr : Vp × Vm → ℝ := fun e => (c e).untopD 0
  have hcr : ∀ e, e ∈ E → c e = (cr e : WithTop ℝ) := by
    intro e he
    have h : c e ≠ ⊤ := (hc e.1 e.2).mpr he |>.ne
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp h
    simp [cr, ← hr]
  let R : (Vp ≃ Vm) → ℝ := fun τ => ∑ u, cr (u, τ u)
  have hW : ∀ τ, IsPerfectMatchingBij E τ → MatchingWeight c τ = ((R τ : ℝ) : WithTop ℝ) := by
    intro τ hτ
    simp only [MatchingWeight, R]
    rw [WithTop.coe_sum]
    exact Finset.sum_congr rfl (fun u _ => hcr _ (hτ u))
  have hMne : (Finset.univ.filter (fun τ : Vp ≃ Vm => IsPerfectMatchingBij E τ)).Nonempty :=
    ⟨sigma0, by simp [hsigma0]⟩
  obtain ⟨σ, hσmem, hσmin⟩ := Finset.exists_min_image _ R hMne
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσmem hσmin
  let arc : Vp → Vp → Prop := fun u u' => (u, σ u') ∈ E
  let w : Vp → Vp → ℝ := fun u u' => cr (u, σ u') - cr (u, σ u)
  have hw0 : ∀ u, w u u = 0 := fun u => sub_self _
  have hcyc : ∀ ρ : Equiv.Perm Vp, (∀ x, ρ x = x ∨ arc x (ρ x)) → 0 ≤ ∑ x, w x (ρ x) := by
    intro ρ hρ
    have hτ : IsPerfectMatchingBij E (ρ.trans σ) := by
      intro x
      rcases hρ x with h | h
      · simp only [Equiv.trans_apply, h]; exact hσmem x
      · exact h
    have := hσmin _ hτ
    simp only [R, Equiv.trans_apply] at this
    simp only [w, Finset.sum_sub_distrib]
    linarith
  obtain ⟨π, hπ⟩ := potential_exists arc w hw0 hcyc
  refine ⟨fun u => π u - cr (u, σ u), fun v => π (σ.symm v), σ, ?_, ?_, ?_, ?_⟩
  · intro u
    dsimp only
    rw [hcr _ (hσmem u), Equiv.symm_apply_apply]
    have : ((cr (u, σ u) : ℝ) : WithTop ℝ) + ((π u - cr (u, σ u) : ℝ) : WithTop ℝ) -
        ((π u : ℝ) : WithTop ℝ) = (((cr (u, σ u)) + (π u - cr (u, σ u)) - π u : ℝ) : WithTop ℝ) := by
      norm_cast
    rw [this]; simp
  · intro u v
    dsimp only
    by_cases hE : (u, v) ∈ E
    · rw [hcr _ hE]
      have harc : arc u (σ.symm v) := by simp only [arc, Equiv.apply_symm_apply]; exact hE
      have h1 := hπ u (σ.symm v) harc
      simp only [w, Equiv.apply_symm_apply] at h1
      have : ((cr (u, v) : ℝ) : WithTop ℝ) + ((π u - cr (u, σ u) : ℝ) : WithTop ℝ) -
          ((π (σ.symm v) : ℝ) : WithTop ℝ) =
          (((cr (u, v)) + (π u - cr (u, σ u)) - π (σ.symm v) : ℝ) : WithTop ℝ) := by
        norm_cast
      rw [this, ge_iff_le, ← WithTop.coe_zero, WithTop.coe_le_coe]
      linarith
    · have htop : c (u, v) = ⊤ := by
        by_contra h
        exact hE ((hc u v).mp (lt_top_iff_ne_top.mpr h))
      rw [htop]; simp
  · refine ⟨hσmem, fun τ hτ => ?_⟩
    rw [hW σ hσmem, hW τ hτ, WithTop.coe_le_coe]
    exact hσmin τ hτ
  · rw [hW σ hσmem]
    congr 1
    simp only [R, Equiv.symm_apply_apply]
    exact Finset.sum_congr rfl (fun u _ => by ring)

end DiscreteConvex.IntegralConvexityB

open DiscreteConvex.IntegralConvexityB


theorem solution {Vp Vm : Type*} [Fintype Vp] [Fintype Vm]
    [DecidableEq Vp] [DecidableEq Vm] (E : Set (Vp × Vm)) (c : Vp × Vm → WithTop ℝ)
    (hc : ∀ u v, c (u, v) < ⊤ ↔ (u, v) ∈ E) (sigma0 : Vp ≃ Vm)
    (hsigma0 : IsPerfectMatchingBij E sigma0) :
    ∃ (pp : Vp → ℝ) (pm : Vm → ℝ) (sigma : Vp ≃ Vm),
      (∀ u, c (u, sigma u) + (pp u : WithTop ℝ) - (pm (sigma u) : WithTop ℝ) = 0) ∧
        (∀ u v, c (u, v) + (pp u : WithTop ℝ) - (pm v : WithTop ℝ) ≥ 0) ∧
        IsMinWeightMatching E c sigma ∧
        MatchingWeight c sigma = ((∑ u, (pm (sigma u) - pp u) : ℝ) : WithTop ℝ) := by
  exact bm314_core E c hc sigma0 hsigma0
