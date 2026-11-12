-- Prove2me | solution 1 for CombOpt.MinCostFlow.exists_integral_optimal_flow
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-11T14:22:47.607518+00:00
-- url     : https://prove2.me/submissions/72de9acb-af5a-46e8-8b03-10ab170edb80

import Mathlib
import Definitions.Def_CombOpt_MinCostFlow_Digraph_IsOptimalFlow
import Definitions.Def_CombOpt_MinCostFlow_IsIntegralExt

set_option autoImplicit false

namespace CombOpt.MinCostFlow.IntOptAux

open CombOpt.MinCostFlow
open Finset

section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

theorem netInflow_add (G : Digraph V E) (x y : E → ℝ) (v : V) :
    G.netInflow (x + y) v = G.netInflow x v + G.netInflow y v := by
  unfold Digraph.netInflow
  simp only [Pi.add_apply, Finset.sum_add_distrib]
  ring

theorem netInflow_smul (G : Digraph V E) (t : ℝ) (x : E → ℝ) (v : V) :
    G.netInflow (t • x) v = t * G.netInflow x v := by
  unfold Digraph.netInflow
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

theorem sum_netInflow (G : Digraph V E) (x : E → ℝ) :
    ∑ v, G.netInflow x v = 0 := by
  unfold Digraph.netInflow
  rw [Finset.sum_sub_distrib, Finset.sum_fiberwise Finset.univ G.head x,
    Finset.sum_fiberwise Finset.univ G.tail x]
  simp

theorem isInt_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) (h : ∀ i ∈ s, ∃ k : ℤ, f i = k) :
    ∃ k : ℤ, ∑ i ∈ s, f i = k := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨k1, hk1⟩ := h a (Finset.mem_insert_self a s)
    obtain ⟨k2, hk2⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    exact ⟨k1 + k2, by rw [Finset.sum_insert ha, hk1, hk2]; push_cast; ring⟩

open Classical in
/-- The arcs carrying a non-integral flow value. -/
noncomputable def fracSet (x : E → ℝ) : Finset E :=
  Finset.univ.filter (fun e => ¬ ∃ k : ℤ, x e = k)

theorem mem_fracSet {x : E → ℝ} {e : E} : e ∈ fracSet x ↔ ¬ ∃ k : ℤ, x e = k := by
  unfold fracSet
  simp

/-- Number of arc-ends of arcs of `F` at `v`. -/
def degF [DecidableEq E] (G : Digraph V E) (F : Finset E) (v : V) : ℕ :=
  (F.filter (fun e => G.head e = v)).card + (F.filter (fun e => G.tail e = v)).card

theorem deg_ne_one [DecidableEq E] (G : Digraph V E) (x : E → ℝ) (v : V)
    (hv : ∃ k : ℤ, G.netInflow x v = k)
    (F : Finset E) (hF : ∀ e, e ∈ F ↔ ¬ ∃ k : ℤ, x e = k) :
    degF G F v ≠ 1 := by
  unfold degF
  intro h1
  have eH : (univ.filter (fun e => G.head e = v)).filter (· ∈ F)
      = F.filter (fun e => G.head e = v) := by
    ext e; simp [and_comm]
  have eT : (univ.filter (fun e => G.tail e = v)).filter (· ∈ F)
      = F.filter (fun e => G.tail e = v) := by
    ext e; simp [and_comm]
  have hnF : ∀ s : Finset E, ∃ k : ℤ, ∑ e ∈ s.filter (· ∉ F), x e = k := by
    intro s
    apply isInt_sum
    intro e he
    have := (Finset.mem_filter.1 he).2
    by_contra hc
    exact this ((hF e).2 hc)
  obtain ⟨kh, hkh⟩ := hnF (univ.filter (fun e => G.head e = v))
  obtain ⟨kt, hkt⟩ := hnF (univ.filter (fun e => G.tail e = v))
  obtain ⟨kv, hkv⟩ := hv
  have hsplit : G.netInflow x v =
      (∑ e ∈ F.filter (fun e => G.head e = v), x e
        + ∑ e ∈ (univ.filter (fun e => G.head e = v)).filter (· ∉ F), x e)
      - (∑ e ∈ F.filter (fun e => G.tail e = v), x e
        + ∑ e ∈ (univ.filter (fun e => G.tail e = v)).filter (· ∉ F), x e) := by
    unfold Digraph.netInflow
    rw [← eH, ← eT, Finset.sum_filter_add_sum_filter_not, Finset.sum_filter_add_sum_filter_not]
  rw [hkh, hkt, hkv] at hsplit
  rcases Nat.add_eq_one_iff.1 h1 with ⟨hH, hT⟩ | ⟨hH, hT⟩
  · rw [Finset.card_eq_zero] at hH
    obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hT
    have haF : a ∈ F := by
      have : a ∈ F.filter (fun e => G.tail e = v) := by rw [ha]; exact Finset.mem_singleton_self a
      exact (Finset.mem_filter.1 this).1
    rw [hH, ha, Finset.sum_empty, Finset.sum_singleton] at hsplit
    exact (hF a).1 haF ⟨kh - kt - kv, by push_cast; linarith⟩
  · rw [Finset.card_eq_zero] at hT
    obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hH
    have haF : a ∈ F := by
      have : a ∈ F.filter (fun e => G.head e = v) := by rw [ha]; exact Finset.mem_singleton_self a
      exact (Finset.mem_filter.1 this).1
    rw [hT, ha, Finset.sum_empty, Finset.sum_singleton] at hsplit
    exact (hF a).1 haF ⟨kv - kh + kt, by push_cast; linarith⟩

theorem card_W_le [DecidableEq E] (G : Digraph V E) (F : Finset E)
    (hdeg : ∀ v, degF G F v ≠ 1) :
    (univ.filter (fun v => degF G F v ≠ 0)).card ≤ F.card := by
  have hsumH : ∑ v, (F.filter (fun e => G.head e = v)).card = F.card :=
    (Finset.card_eq_sum_card_fiberwise (f := G.head) (t := univ) (by intro e _; simp)).symm
  have hsumT : ∑ v, (F.filter (fun e => G.tail e = v)).card = F.card :=
    (Finset.card_eq_sum_card_fiberwise (f := G.tail) (t := univ) (by intro e _; simp)).symm
  have htot : ∑ v, degF G F v = 2 * F.card := by
    unfold degF
    rw [Finset.sum_add_distrib, hsumH, hsumT]
    ring
  have h2 : (univ.filter (fun v => degF G F v ≠ 0)).card • 2
      ≤ ∑ v ∈ univ.filter (fun v => degF G F v ≠ 0), degF G F v :=
    Finset.card_nsmul_le_sum _ _ _ (fun v hv => by
      have h0 := (Finset.mem_filter.1 hv).2
      have h1 := hdeg v
      omega)
  have h3 : ∑ v ∈ univ.filter (fun v => degF G F v ≠ 0), degF G F v ≤ ∑ v, degF G F v :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rw [smul_eq_mul] at h2
  omega

/-- Extension by zero from the arcs of `F` to all arcs. -/
noncomputable def extF [DecidableEq E] (F : Finset E) (y : ↥F → ℝ) : E → ℝ :=
  fun e => if h : e ∈ F then y ⟨e, h⟩ else 0

theorem extF_add [DecidableEq E] (F : Finset E) (y z : ↥F → ℝ) : extF F (y + z) = extF F y + extF F z := by
  funext e; simp only [extF, Pi.add_apply]; split_ifs <;> simp

theorem extF_smul [DecidableEq E] (F : Finset E) (t : ℝ) (y : ↥F → ℝ) : extF F (t • y) = t • extF F y := by
  funext e; simp only [extF, Pi.smul_apply, smul_eq_mul]; split_ifs <;> simp

/-- A nonempty arc set with no node of degree one carries a nonzero circulation. -/
theorem exists_circ [DecidableEq E] (G : Digraph V E) (F : Finset E) (hFne : F.Nonempty)
    (hdeg : ∀ v, degF G F v ≠ 1) :
    ∃ Y : E → ℝ, (∀ v, G.netInflow Y v = 0) ∧ (∀ e, Y e ≠ 0 → e ∈ F) ∧ ∃ e, Y e ≠ 0 := by
  set W := univ.filter (fun v => degF G F v ≠ 0) with hW
  have hWF : W.card ≤ F.card := card_W_le G F hdeg
  obtain ⟨e0, he0⟩ := hFne
  have hw0 : G.head e0 ∈ W := by
    rw [hW, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    unfold degF
    have : 0 < (F.filter (fun e => G.head e = G.head e0)).card :=
      Finset.card_pos.2 ⟨e0, Finset.mem_filter.2 ⟨he0, rfl⟩⟩
    omega
  set w0 := G.head e0 with hw0def
  let L : (↥F → ℝ) →ₗ[ℝ] (↥(W.erase w0) → ℝ) :=
    { toFun := fun y v => G.netInflow (extF F y) v.1
      map_add' := fun y z => by
        funext v
        simp only [Pi.add_apply]
        rw [extF_add, netInflow_add]
      map_smul' := fun t y => by
        funext v
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [extF_smul, netInflow_smul] }
  have hdim : Module.finrank ℝ (↥(W.erase w0) → ℝ) < Module.finrank ℝ (↥F → ℝ) := by
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
      Fintype.card_coe, Fintype.card_coe, Finset.card_erase_of_mem hw0]
    have := Finset.card_pos.2 ⟨_, hw0⟩
    omega
  obtain ⟨y, hyk, hy0⟩ := (Submodule.ne_bot_iff _).1 (LinearMap.ker_ne_bot_of_finrank_lt (f := L) hdim)
  rw [LinearMap.mem_ker] at hyk
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hy0
  have hother : ∀ v, v ≠ w0 → G.netInflow (extF F y) v = 0 := by
    intro v hv
    by_cases hvW : v ∈ W
    · have := congrFun hyk ⟨v, Finset.mem_erase.2 ⟨hv, hvW⟩⟩
      exact this
    · have hd0 : degF G F v = 0 := by
        by_contra h
        exact hvW (by rw [hW, Finset.mem_filter]; exact ⟨Finset.mem_univ _, h⟩)
      unfold degF at hd0
      have hH' : ∀ e ∈ F, ¬ G.head e = v :=
        Finset.filter_eq_empty_iff.1 (Finset.card_eq_zero.1 (by omega))
      have hT' : ∀ e ∈ F, ¬ G.tail e = v :=
        Finset.filter_eq_empty_iff.1 (Finset.card_eq_zero.1 (by omega))
      unfold Digraph.netInflow
      rw [Finset.sum_eq_zero, Finset.sum_eq_zero, sub_zero]
      all_goals
        intro e he
        rw [Finset.mem_filter] at he
        unfold extF
        split_ifs with heF
        · first
          | exact absurd he.2 (hH' e heF)
          | exact absurd he.2 (hT' e heF)
        · rfl
  refine ⟨extF F y, ?_, ?_, ⟨i.1, ?_⟩⟩
  · intro v
    by_cases hv : v = w0
    · have htot := sum_netInflow G (extF F y)
      rw [Finset.sum_eq_single w0 (fun v _ hv => hother v hv) (by simp)] at htot
      rw [hv]; exact htot
    · exact hother v hv
  · intro e he
    unfold extF at he
    split_ifs at he with h
    · exact h
    · exact absurd rfl he
  · unfold extF
    rw [dif_pos i.2]
    exact hi

theorem ceil_le_u (r : ℝ) (a : EReal) (h0 : 0 ≤ a) (ha : IsIntegralExt a)
    (hr : (r : EReal) ≤ a) : (((⌈r⌉ : ℤ) : ℝ) : EReal) ≤ a := by
  by_cases htop : a = ⊤
  · rw [htop]; exact le_top
  · have hbot : a ≠ ⊥ := by
      intro h; rw [h] at h0; simp at h0
    obtain ⟨k, hk⟩ := ha htop hbot
    rw [hk] at hr ⊢
    have hr' : r ≤ (k : ℝ) := EReal.coe_le_coe_iff.1 hr
    have : ⌈r⌉ ≤ k := Int.ceil_le.2 hr'
    exact EReal.coe_le_coe_iff.2 (by exact_mod_cast this)

/-- Step length to the next integer in direction `Y`. -/
noncomputable def tau (x Y : E → ℝ) (e : E) : ℝ :=
  if 0 < Y e then ((⌈x e⌉ : ℝ) - x e) / Y e else ((⌊x e⌋ : ℝ) - x e) / Y e

theorem step (G : Digraph V E) (b : V → ℝ) (u : E → EReal) (c : E → ℝ)
    (hu : ∀ e, 0 ≤ u e) (huint : ∀ e, IsIntegralExt (u e))
    (x : E → ℝ) (hx : G.IsOptimalFlow b u c x)
    (Y : E → ℝ) (hY0 : ∀ v, G.netInflow Y v = 0)
    (hYs : ∀ e, Y e ≠ 0 → ¬ ∃ k : ℤ, x e = k) (hYne : ∃ e, Y e ≠ 0)
    (hc : ∑ e, c e * Y e ≤ 0) :
    ∃ x', G.IsOptimalFlow b u c x' ∧ (fracSet x').card < (fracSet x).card := by
  classical
  set S := univ.filter (fun e => Y e ≠ 0) with hS
  have hSne : S.Nonempty := by
    obtain ⟨e, he⟩ := hYne
    exact ⟨e, by simp [hS, he]⟩
  obtain ⟨e1, he1S, he1⟩ := Finset.exists_mem_eq_inf' hSne (tau x Y)
  set t := S.inf' hSne (tau x Y) with ht
  have hfl : ∀ e, ¬ (∃ k : ℤ, x e = k) → (⌊x e⌋ : ℝ) < x e ∧ x e < ⌈x e⌉ := by
    intro e he
    exact ⟨lt_of_le_of_ne (Int.floor_le _) (fun h => he ⟨_, h.symm⟩),
      lt_of_le_of_ne (Int.le_ceil _) (fun h => he ⟨_, h⟩)⟩
  have hτpos : ∀ e ∈ S, 0 < tau x Y e := by
    intro e he
    have hYe : Y e ≠ 0 := (Finset.mem_filter.1 he).2
    obtain ⟨h1, h2⟩ := hfl e (hYs e hYe)
    unfold tau
    split_ifs with hpos
    · exact div_pos (by linarith) hpos
    · exact div_pos_of_neg_of_neg (by linarith) (lt_of_le_of_ne (not_lt.1 hpos) hYe)
  have htpos : 0 < t := by
    rw [ht, Finset.lt_inf'_iff]; exact hτpos
  have htle : ∀ e ∈ S, t ≤ tau x Y e := fun e he => Finset.inf'_le _ he
  set x' : E → ℝ := fun e => x e + t * Y e with hx'
  have hbetween : ∀ e, (⌊x e⌋ : ℝ) ≤ x' e ∧ x' e ≤ ⌈x e⌉ := by
    intro e
    by_cases hYe : Y e = 0
    · simp only [hx', hYe, mul_zero, add_zero]
      exact ⟨Int.floor_le _, Int.le_ceil _⟩
    · have heS : e ∈ S := by simp [hS, hYe]
      have h1 := htle e heS
      obtain ⟨hf1, hf2⟩ := hfl e (hYs e hYe)
      unfold tau at h1
      split_ifs at h1 with hpos
      · have h2 : t * Y e ≤ (⌈x e⌉ : ℝ) - x e := by rwa [le_div_iff₀ hpos] at h1
        have h3 := mul_pos htpos hpos
        simp only [hx']
        constructor <;> linarith
      · have hneg : Y e < 0 := lt_of_le_of_ne (not_lt.1 hpos) hYe
        have h2 : (⌊x e⌋ : ℝ) - x e ≤ t * Y e := by rwa [le_div_iff_of_neg hneg] at h1
        have h3 := mul_neg_of_pos_of_neg htpos hneg
        simp only [hx']
        constructor <;> linarith
  have hfeas : G.IsFeasibleFlow b u x' := by
    obtain ⟨⟨hflow, hbd⟩, _⟩ := hx
    refine ⟨fun v => ?_, fun e => ?_⟩
    · have : x' = x + t • Y := by
        funext e; simp [hx', smul_eq_mul]
      rw [this, netInflow_add, netInflow_smul, hY0, hflow]
      ring
    · obtain ⟨h0, hu'⟩ := hbd e
      obtain ⟨hb1, hb2⟩ := hbetween e
      refine ⟨le_trans (by exact_mod_cast Int.floor_nonneg.2 h0) hb1, ?_⟩
      exact le_trans (EReal.coe_le_coe_iff.2 hb2) (ceil_le_u (x e) (u e) (hu e) (huint e) hu')
  have hcost : ∑ e, c e * x' e ≤ ∑ e, c e * x e := by
    have : ∑ e, c e * x' e = ∑ e, c e * x e + t * ∑ e, c e * Y e := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro e _
      simp only [hx']
      ring
    rw [this]
    have := mul_nonpos_of_nonneg_of_nonpos htpos.le hc
    linarith
  have hopt : G.IsOptimalFlow b u c x' :=
    ⟨hfeas, fun x'' hx'' => le_trans hcost (hx.2 x'' hx'')⟩
  have hsub : fracSet x' ⊆ fracSet x := by
    intro e he
    rw [mem_fracSet] at he ⊢
    intro hint
    apply he
    by_cases hYe : Y e = 0
    · simpa [hx', hYe] using hint
    · exact absurd hint (hYs e hYe)
  have hYe1 : Y e1 ≠ 0 := (Finset.mem_filter.1 he1S).2
  have he1x : e1 ∈ fracSet x := mem_fracSet.2 (hYs e1 hYe1)
  have he1x' : e1 ∉ fracSet x' := by
    rw [mem_fracSet, not_not]
    simp only [hx']
    rw [he1]
    unfold tau
    split_ifs with hpos
    · exact ⟨⌈x e1⌉, by rw [div_mul_cancel₀ _ hYe1]; ring⟩
    · exact ⟨⌊x e1⌋, by rw [div_mul_cancel₀ _ hYe1]; ring⟩
  exact ⟨x', hopt, Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).2 ⟨e1, he1x, he1x'⟩)⟩

theorem main (G : Digraph V E) (b : V → ℝ) (u : E → EReal) (c : E → ℝ)
    (hu : ∀ e, 0 ≤ u e)
    (hbint : ∀ v, ∃ k : ℤ, b v = k) (huint : ∀ e, IsIntegralExt (u e))
    (hopt : ∃ x, G.IsOptimalFlow b u c x) :
    ∃ x, G.IsOptimalFlow b u c x ∧ ∀ e, ∃ k : ℤ, x e = k := by
  classical
  have hex : ∃ n, ∃ x, G.IsOptimalFlow b u c x ∧ (fracSet x).card = n := by
    obtain ⟨x, hx⟩ := hopt
    exact ⟨_, x, hx, rfl⟩
  obtain ⟨x, hx, hxn⟩ := Nat.find_spec hex
  by_cases hF : fracSet x = ∅
  · refine ⟨x, hx, fun e => ?_⟩
    by_contra h
    have : e ∈ fracSet x := mem_fracSet.2 h
    rw [hF] at this
    simp at this
  · exfalso
    have hFne : (fracSet x).Nonempty := Finset.nonempty_iff_ne_empty.2 hF
    have hdeg : ∀ v, degF G (fracSet x) v ≠ 1 := by
      intro v
      obtain ⟨k, hk⟩ := hbint v
      exact deg_ne_one G x v ⟨k, by rw [hx.1.1 v, hk]⟩ (fracSet x) (fun e => mem_fracSet)
    obtain ⟨Y, hY0, hYs, hYne⟩ := exists_circ G (fracSet x) hFne hdeg
    have hYs' : ∀ e, Y e ≠ 0 → ¬ ∃ k : ℤ, x e = k := fun e he => mem_fracSet.1 (hYs e he)
    by_cases hc : ∑ e, c e * Y e ≤ 0
    · obtain ⟨x', hx', hlt⟩ := step G b u c hu huint x hx Y hY0 hYs' hYne hc
      exact Nat.find_min hex (lt_of_lt_of_eq hlt hxn) ⟨x', hx', rfl⟩
    · have hneg0 : ∀ v, G.netInflow (-Y) v = 0 := by
        intro v
        have : -Y = (-1 : ℝ) • Y := by funext e; simp
        rw [this, netInflow_smul, hY0]
        ring
      have hnegs : ∀ e, (-Y) e ≠ 0 → ¬ ∃ k : ℤ, x e = k :=
        fun e he => hYs' e (by simpa using he)
      have hnegne : ∃ e, (-Y) e ≠ 0 := by
        obtain ⟨e, he⟩ := hYne
        exact ⟨e, by simpa using he⟩
      have hnegc : ∑ e, c e * (-Y) e ≤ 0 := by
        simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
        linarith [not_le.1 hc]
      obtain ⟨x', hx', hlt⟩ := step G b u c hu huint x hx (-Y) hneg0 hnegs hnegne hnegc
      exact Nat.find_min hex (lt_of_lt_of_eq hlt hxn) ⟨x', hx', rfl⟩

end

end CombOpt.MinCostFlow.IntOptAux

open CombOpt.MinCostFlow in
theorem solution {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Digraph V E) (b : V → ℝ) (u : E → EReal) (c : E → ℝ)
    (hb : ∑ v, b v = 0) (hu : ∀ e, 0 ≤ u e)
    (hbint : ∀ v, ∃ k : ℤ, b v = k) (huint : ∀ e, IsIntegralExt (u e))
    (hopt : ∃ x, G.IsOptimalFlow b u c x) :
    ∃ x, G.IsOptimalFlow b u c x ∧ ∀ e, ∃ k : ℤ, x e = k := by
  exact CombOpt.MinCostFlow.IntOptAux.main G b u c hu hbint huint hopt
