-- Prove2me | solution 1 for FlowsNetworks.DynamicFlow.maximal_min_cost_of_large_p
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T14:31:11.085761+00:00
-- url     : https://prove2.me/submissions/e1d92e04-33b6-4a15-ae8f-88d9c16ee790

import Mathlib
import Definitions.Def_FlowsNetworks_DynamicFlow_Network

section g70fn2S
variable {N : Type} [DecidableEq N]
set_option linter.unusedSectionVars false
def g70fn2_Step (R : N → N → Prop) (a b : N × List N) : Prop :=
  R a.1 b.1 ∧ b.1 ∉ a.2 ∧ b.2 = b.1 :: a.2

theorem g70fn2_step_mem {R : N → N → Prop} {s : N} {x : N} {l : List N}
    (h : Relation.ReflTransGen (g70fn2_Step R) (s, [s]) (x, l)) : x ∈ l ∧ s ∈ l := by
  generalize hb : (x, l) = b at h
  induction h generalizing x l with
  | refl => cases hb; simp
  | tail _ hst ih =>
    rename_i b c
    obtain ⟨b1, b2⟩ := b
    obtain ⟨_, _, h3⟩ := hst
    cases hb
    simp only at h3
    subst h3
    exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ (ih rfl).2⟩

theorem g70fn2_step_prefix {R : N → N → Prop} {s : N} {x : N} {l : List N}
    (h : Relation.ReflTransGen (g70fn2_Step R) (s, [s]) (x, l)) :
    ∀ z ∈ l, ∃ l', Relation.ReflTransGen (g70fn2_Step R) (s, [s]) (z, l') := by
  generalize hb : (x, l) = b at h
  induction h generalizing x l with
  | refl => cases hb; intro z hz; simp at hz; subst hz; exact ⟨_, Relation.ReflTransGen.refl⟩
  | tail h1 hst ih =>
    rename_i b c
    obtain ⟨b1, b2⟩ := b
    obtain ⟨_, _, h3⟩ := hst
    cases hb
    simp only at h3
    subst h3
    intro z hz
    rcases List.mem_cons.1 hz with hz | hz
    · subst hz; exact ⟨_, h1.tail ⟨by assumption, by assumption, rfl⟩⟩
    · exact ih rfl z hz

theorem g70fn2_simple {R : N → N → Prop} {s x : N} (h : Relation.ReflTransGen R s x) :
    ∃ l, Relation.ReflTransGen (g70fn2_Step R) (s, [s]) (x, l) := by
  induction h with
  | refl => exact ⟨_, Relation.ReflTransGen.refl⟩
  | @tail y x _ hyx ih =>
    obtain ⟨l, hl⟩ := ih
    by_cases hx : x ∈ l
    · exact g70fn2_step_prefix hl x hx
    · exact ⟨x :: l, hl.tail ⟨hyx, hx, rfl⟩⟩

/-- augmentation along a simple residual path -/

theorem g70fn2_to_fin {N : Type} {R : N → N → Prop} {s x : N} {l : List N}
    (h : Relation.ReflTransGen (g70fn2_Step R) (s, [s]) (x, l)) :
    ∃ (n : ℕ) (p : Fin (n + 1) → N), Function.Injective p ∧ p 0 = s ∧ p (Fin.last n) = x ∧
      (∀ i : Fin n, R (p i.castSucc) (p i.succ)) ∧ ∀ z, z ∈ l ↔ ∃ i, p i = z := by
  generalize hb : (x, l) = b at h
  induction h generalizing x l with
  | refl =>
    cases hb
    refine ⟨0, fun _ => s, fun i j _ => Fin.ext (by have := i.2; have := j.2; omega), rfl, rfl, fun i => i.elim0, ?_⟩
    intro z; simp [eq_comm]
  | tail h1 hst ih =>
    rename_i b c
    obtain ⟨y, l0⟩ := b
    obtain ⟨hR, hx, h3⟩ := hst
    cases hb
    simp only at h3 hR hx
    subst h3
    obtain ⟨n, p, hinj, h0, hlast, hstep, hmem⟩ := ih rfl
    refine ⟨n + 1, Fin.snoc (α := fun _ => N) p x, ?_, ?_, ?_, ?_, ?_⟩
    · apply Fin.snoc_injective_of_injective hinj
      rintro ⟨i, hi⟩; exact hx ((hmem x).2 ⟨i, hi⟩)
    · have : (0 : Fin (n + 2)) = (0 : Fin (n + 1)).castSucc := rfl
      rw [this, Fin.snoc_castSucc, h0]
    · simp
    · intro i
      induction i using Fin.lastCases with
      | last =>
        rw [Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc, hlast]; exact hR
      | cast j =>
        rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]; exact hstep j
    · intro z
      rw [Fin.exists_fin_succ', List.mem_cons, hmem z]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      constructor
      · rintro (h | h)
        · exact Or.inr h.symm
        · exact Or.inl h
      · rintro (h | h)
        · exact Or.inr h
        · exact Or.inl h.symm

end g70fn2S

open FlowsNetworks.DynamicFlow

theorem g70fn2_pot {N : Type} [Fintype N] [DecidableEq N] (G : Network N) (f : N → N → ℝ)
    (π : N → ℝ) :
    ∑ x, π x * netOut G f x = ∑ q ∈ G.arcs, f q.1 q.2 * (π q.1 - π q.2) := by
  unfold netOut arcSum
  have h1 : ∀ x, G.arcs.filter (fun q => q.1 ∈ ({x} : Finset N) ∧ q.2 ∈ Finset.univ)
      = G.arcs.filter (fun q => q.1 = x) := fun x => by
    ext q; simp
  have h2 : ∀ x, G.arcs.filter (fun q => q.1 ∈ (Finset.univ : Finset N) ∧ q.2 ∈ ({x} : Finset N))
      = G.arcs.filter (fun q => q.2 = x) := fun x => by
    ext q; simp
  simp only [h1, h2, Finset.sum_filter, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ)]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  congr 1 <;> exact Finset.sum_congr rfl fun q _ => by ring

theorem g70fn2_flowpot {N : Type} [Fintype N] [DecidableEq N] (G : Network N) (s t : N)
    (hst : s ≠ t) (f : N → N → ℝ) (v : ℝ) (hf : IsStaticFlow G s t f v) (π : N → ℝ) :
    ∑ q ∈ G.arcs, f q.1 q.2 * (π q.2 - π q.1) = (π t - π s) * v := by
  obtain ⟨-, -, h1, h2, h3⟩ := hf
  have := g70fn2_pot G f π
  have e : ∑ x, π x * netOut G f x =
      ∑ x, ((if x = s then π s * v else 0) + (if x = t then -(π t * v) else 0)) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hs : x = s
    · subst hs; simp [h1, hst]
    · by_cases ht : x = t
      · subst ht; simp [h3, hs]
      · simp [h2 x hs ht, hs, ht]
  rw [e, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq'] at this
  simp only [Finset.mem_univ, if_true] at this
  have h4 : ∑ q ∈ G.arcs, f q.1 q.2 * (π q.2 - π q.1) =
      -∑ q ∈ G.arcs, f q.1 q.2 * (π q.1 - π q.2) := by
    rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun q _ => by ring
  rw [h4, ← this]; ring

theorem g70fn2_rpo {N : Type} [Fintype N] [DecidableEq N]
    (G : Network N) (s t : N) (hst : s ≠ t) (p : ℕ)
    (f : N → N → ℝ) (v : ℝ) (hf : IsStaticFlow G s t f v)
    (π : N → ℤ) (hπ : OptimalityProperties G s t p f π) :
    (∀ (f' : N → N → ℝ) (v' : ℝ), IsStaticFlow G s t f' v' →
        (p : ℝ) * v' - totalCost G f' ≤ (p : ℝ) * v - totalCost G f) ∧
    IsDualFeasible G s t p (fun x => (π x : ℝ)) (fun x y => (arcNumber G π x y : ℝ)) ∧
    (∀ (π' : N → ℝ) (γ' : N → N → ℝ), IsDualFeasible G s t p π' γ' →
        dualObjective G (fun x y => (arcNumber G π x y : ℝ)) ≤ dualObjective G γ') ∧
    (p : ℝ) * v - totalCost G f = dualObjective G (fun x y => (arcNumber G π x y : ℝ)) := by
  obtain ⟨hs0, htp, hopt⟩ := hπ
  set πr : N → ℝ := fun x => (π x : ℝ)
  set γ : N → N → ℝ := fun x y => (arcNumber G π x y : ℝ)
  have hγ : ∀ x y, γ x y = max 0 (πr y - πr x - (G.cost x y : ℝ)) := by
    intro x y; simp only [γ, πr, arcNumber]; push_cast; rfl
  -- value identity
  have hval : ∀ f' v', IsStaticFlow G s t f' v' →
      (p : ℝ) * v' - totalCost G f' =
        ∑ q ∈ G.arcs, f' q.1 q.2 * (πr q.2 - πr q.1 - (G.cost q.1 q.2 : ℝ)) := by
    intro f' v' hf'
    have := g70fn2_flowpot G s t hst f' v' hf' πr
    have e2 : ∑ q ∈ G.arcs, f' q.1 q.2 * (πr q.2 - πr q.1 - (G.cost q.1 q.2 : ℝ)) =
        ∑ q ∈ G.arcs, f' q.1 q.2 * (πr q.2 - πr q.1) -
          ∑ q ∈ G.arcs, (G.cost q.1 q.2 : ℝ) * f' q.1 q.2 := by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun q _ => by ring
    rw [e2, this]
    unfold totalCost
    simp only [πr, hs0, htp]
    push_cast; ring
  have hcs : ∑ q ∈ G.arcs, f q.1 q.2 * (πr q.2 - πr q.1 - (G.cost q.1 q.2 : ℝ)) =
      dualObjective G γ := by
    unfold dualObjective
    refine Finset.sum_congr rfl fun q hq => ?_
    obtain ⟨o1, o2⟩ := hopt q hq
    rw [hγ]
    simp only [πr]
    rcases lt_trichotomy (π q.2 - π q.1) (G.cost q.1 q.2 : ℤ) with h | h | h
    · have hd : ((π q.2 : ℝ) - π q.1 - (G.cost q.1 q.2 : ℝ)) < 0 := by
        have : ((π q.2 - π q.1 : ℤ) : ℝ) < ((G.cost q.1 q.2 : ℤ) : ℝ) := by exact_mod_cast h
        push_cast at this; linarith
      rw [o1 h, max_eq_left hd.le]; ring
    · have hd : ((π q.2 : ℝ) - π q.1 - (G.cost q.1 q.2 : ℝ)) = 0 := by
        have : ((π q.2 - π q.1 : ℤ) : ℝ) = ((G.cost q.1 q.2 : ℤ) : ℝ) := by exact_mod_cast h
        push_cast at this; linarith
      rw [hd]; simp
    · have hd : 0 < ((π q.2 : ℝ) - π q.1 - (G.cost q.1 q.2 : ℝ)) := by
        have : ((G.cost q.1 q.2 : ℤ) : ℝ) < ((π q.2 - π q.1 : ℤ) : ℝ) := by exact_mod_cast h
        push_cast at this; linarith
      rw [o2 h, max_eq_right hd.le]
  have heq : (p : ℝ) * v - totalCost G f = dualObjective G γ := by rw [hval f v hf, hcs]
  refine ⟨?_, ?_, ?_, heq⟩
  · intro f' v' hf'
    rw [heq, hval f' v' hf']
    unfold dualObjective
    refine Finset.sum_le_sum fun q hq => ?_
    obtain ⟨-, hb, -⟩ := hf'
    obtain ⟨n1, n2⟩ := hb q hq
    rw [hγ]
    have g0 : 0 ≤ max 0 (πr q.2 - πr q.1 - (G.cost q.1 q.2 : ℝ)) := le_max_left _ _
    have g1 : πr q.2 - πr q.1 - (G.cost q.1 q.2 : ℝ) ≤ max 0 (πr q.2 - πr q.1 - (G.cost q.1 q.2 : ℝ)) :=
      le_max_right _ _
    calc f' q.1 q.2 * (πr q.2 - πr q.1 - (G.cost q.1 q.2 : ℝ))
        ≤ f' q.1 q.2 * max 0 (πr q.2 - πr q.1 - (G.cost q.1 q.2 : ℝ)) :=
          mul_le_mul_of_nonneg_left g1 n1
      _ ≤ (G.cap q.1 q.2 : ℝ) * max 0 (πr q.2 - πr q.1 - (G.cost q.1 q.2 : ℝ)) :=
          mul_le_mul_of_nonneg_right n2 g0
  · refine ⟨?_, fun q _ => ⟨?_, ?_⟩⟩
    · show -((π s : ℤ) : ℝ) + ((π t : ℤ) : ℝ) = (p : ℝ)
      rw [hs0, htp]; push_cast; ring
    · have := hγ q.1 q.2
      have g1 := le_max_right 0 (πr q.2 - πr q.1 - (G.cost q.1 q.2 : ℝ))
      simp only [γ, πr] at this g1 ⊢
      linarith
    · show (0:ℝ) ≤ (arcNumber G π q.1 q.2 : ℝ)
      unfold arcNumber; exact_mod_cast le_max_left _ _
  · intro π' γ' ⟨hp', hfe⟩
    rw [← heq, hval f v hf]
    have := g70fn2_flowpot G s t hst f v hf π'
    have hv2 : ∑ q ∈ G.arcs, f q.1 q.2 * (πr q.2 - πr q.1 - (G.cost q.1 q.2 : ℝ)) =
        ∑ q ∈ G.arcs, f q.1 q.2 * (π' q.2 - π' q.1 - (G.cost q.1 q.2 : ℝ)) := by
      have e1 := g70fn2_flowpot G s t hst f v hf πr
      have k : (πr t - πr s) = π' t - π' s := by simp only [πr, hs0, htp]; push_cast; linarith
      have d1 : ∀ ρ : N → ℝ, ∑ q ∈ G.arcs, f q.1 q.2 * (ρ q.2 - ρ q.1 - (G.cost q.1 q.2 : ℝ)) =
          ∑ q ∈ G.arcs, f q.1 q.2 * (ρ q.2 - ρ q.1) -
            ∑ q ∈ G.arcs, f q.1 q.2 * (G.cost q.1 q.2 : ℝ) := fun ρ => by
        rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun q _ => by ring
      rw [d1, d1, e1, this, k]
    rw [hv2]
    unfold dualObjective
    refine Finset.sum_le_sum fun q hq => ?_
    obtain ⟨-, hb, -⟩ := hf
    obtain ⟨n1, n2⟩ := hb q hq
    obtain ⟨d1, d2⟩ := hfe q hq
    calc f q.1 q.2 * (π' q.2 - π' q.1 - (G.cost q.1 q.2 : ℝ)) ≤ f q.1 q.2 * γ' q.1 q.2 :=
          mul_le_mul_of_nonneg_left (by linarith) n1
      _ ≤ (G.cap q.1 q.2 : ℝ) * γ' q.1 q.2 := mul_le_mul_of_nonneg_right n2 d2

theorem g70fn2_tele {n : ℕ} (y : Fin (n + 1) → ℤ) :
    ∑ i : Fin n, (y i.succ - y i.castSucc) = y (Fin.last n) - y 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    have := ih (fun i => y i.castSucc)
    simp only [Fin.succ_castSucc] at this ⊢
    rw [this]
    simp only [Fin.castSucc_zero, Fin.succ_last]
    ring

theorem solution {N : Type} [Fintype N] [DecidableEq N]
    (G : Network N) (s t : N) (hst : s ≠ t) (p : ℕ)
    (f : N → N → ℝ) (v : ℝ) (hf : IsStaticFlow G s t f v) (hint : IsIntegral f)
    (π : N → ℤ) (hπ : OptimalityProperties G s t p f π)
    (hp : ∀ (n : ℕ) (x : Fin (n + 1) → N) (fwd : Fin n → Bool),
      IsPathFromTo G s t x fwd → pathCost G x fwd < (p : ℤ)) :
    (∀ (f' : N → N → ℝ) (v' : ℝ), IsStaticFlow G s t f' v' → v' ≤ v) ∧
    (∀ f' : N → N → ℝ, IsStaticFlow G s t f' v → totalCost G f ≤ totalCost G f') := by
  have hrpo := g70fn2_rpo G s t hst p f v hf π hπ
  refine ⟨?_, fun f' hf' => by have := hrpo.1 f' v hf'; linarith⟩
  classical
  let R : N → N → Prop := fun u w =>
    ((u, w) ∈ G.arcs ∧ f u w < (G.cap u w : ℝ)) ∨ ((w, u) ∈ G.arcs ∧ 0 < f w u)
  obtain ⟨hs0, htp, hopt⟩ := hπ
  -- t is not reachable
  have ht : ¬ Relation.ReflTransGen R s t := by
    intro hr
    obtain ⟨l, hl⟩ := g70fn2_simple hr
    obtain ⟨n, x, hinj, h0, hlast, hstep, -⟩ := g70fn2_to_fin hl
    let fwd : Fin n → Bool := fun i =>
      decide ((x i.castSucc, x i.succ) ∈ G.arcs ∧ f (x i.castSucc) (x i.succ) <
        (G.cap (x i.castSucc) (x i.succ) : ℝ))
    have hpath : IsPathFromTo G s t x fwd := by
      refine ⟨hinj, h0, hlast, fun i => ⟨fun h => ?_, fun h => ?_⟩⟩
      · simp only [fwd, decide_eq_true_eq] at h; exact h.1
      · simp only [fwd, decide_eq_false_iff_not] at h
        rcases hstep i with h' | h'
        · exact absurd h' h
        · exact h'.1
    have hlt := hp n x fwd hpath
    have hle : (p : ℤ) ≤ pathCost G x fwd := by
      have tel := g70fn2_tele (fun i => π (x i))
      simp only [hlast, h0, hs0, htp, sub_zero] at tel
      rw [← tel]
      unfold pathCost
      refine Finset.sum_le_sum fun i _ => ?_
      by_cases hfw : fwd i = true
      · rw [if_pos hfw]
        simp only [fwd, decide_eq_true_eq] at hfw
        have := (hopt _ hfw.1).2
        by_contra hc
        push_neg at hc
        have := this hc
        simp only at this
        linarith [hfw.2]
      · rw [if_neg hfw]
        simp only [fwd, Bool.not_eq_true, decide_eq_false_iff_not] at hfw
        rcases hstep i with h' | h'
        · exact absurd h' hfw
        · have := (hopt _ h'.1).1
          by_contra hc
          push_neg at hc
          have := this (by simp only; linarith)
          simp only at this
          linarith [h'.2]
    omega
  -- the cut
  let X : Finset N := Finset.univ.filter (fun u => Relation.ReflTransGen R s u)
  have hsX : s ∈ X := by simp [X, Relation.ReflTransGen.refl]
  have htX : t ∉ X := by simp [X, ht]
  have hcl : ∀ u w, u ∈ X → R u w → w ∈ X := by
    intro u w hu huw
    simp only [X, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    exact hu.tail huw
  let ind : N → ℝ := fun u => if u ∈ X then 1 else 0
  have key : ∀ g w, IsStaticFlow G s t g w →
      w = ∑ q ∈ G.arcs, g q.1 q.2 * (ind q.1 - ind q.2) := by
    intro g w hg
    have := g70fn2_flowpot G s t hst g w hg ind
    have e : ∑ q ∈ G.arcs, g q.1 q.2 * (ind q.1 - ind q.2) =
        -∑ q ∈ G.arcs, g q.1 q.2 * (ind q.2 - ind q.1) := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun q _ => by ring
    rw [e, this]
    simp [ind, hsX, htX]
  intro f' v' hf'
  rw [key f' v' hf', key f v hf]
  apply Finset.sum_le_sum
  intro q hq
  obtain ⟨-, hb, -⟩ := hf'
  obtain ⟨-, hb0, -⟩ := hf
  obtain ⟨n1, n2⟩ := hb q hq
  obtain ⟨m1, m2⟩ := hb0 q hq
  by_cases a1 : q.1 ∈ X <;> by_cases a2 : q.2 ∈ X <;> simp only [ind, a1, a2, if_true, if_false]
  · simp
  · have : f q.1 q.2 = (G.cap q.1 q.2 : ℝ) := by
      by_contra hne
      exact a2 (hcl q.1 q.2 a1 (Or.inl ⟨hq, lt_of_le_of_ne m2 hne⟩))
    rw [this]; linarith
  · have : f q.1 q.2 = 0 := by
      by_contra hne
      exact a1 (hcl q.2 q.1 a2 (Or.inr ⟨hq, lt_of_le_of_ne m1 (Ne.symm hne)⟩))
    rw [this]; linarith
  · simp
