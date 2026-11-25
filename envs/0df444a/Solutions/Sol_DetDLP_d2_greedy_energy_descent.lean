-- Prove2me | solution 1 for DetDLP.d2_greedy_energy_descent
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T05:56:45.610598+00:00
-- url     : https://prove2.me/submissions/281db2a5-f1c1-4821-a314-053f288b9a26

import Definitions.Def_DetDLP_D2_Greedy
set_option autoImplicit false
namespace DetDLP.D2.Descent
open Greedy Finset

private theorem digit_count (m r k c : ℕ) (hk : 0 < k) (hc : c < r) :
    (∑ x : Fin ((m*r)*k), if x.val/k%r = c then r else 0) = (m*r)*k := by
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  simp only [finProdFinEquiv_apply_val, Nat.add_mul_div_left _ _ hk]
  simp_rw [Nat.div_eq_of_lt (Fin.isLt _), zero_add]
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  simp only [finProdFinEquiv_apply_val,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (Fin.isLt _)]
  have hc' (y : Fin r) : (y.val = c) = (y = (⟨c,hc⟩ : Fin r)) := by simp [Fin.ext_iff]
  simp [hc',mul_assoc,mul_comm k r]

private theorem keep (p : List ℕ) (r k u v g : ℕ) (hu : u ≠ p.length) (hv : v ≠ p.length) :
    factor (p++[g]) r k u v = factor p r k u v := by
  by_cases h : u < p.length ∧ v < p.length
  · simp [factor,h,h.1,h.2,show u < p.length+1 by omega,show v < p.length+1 by omega,List.getD_append]
  · simp [factor,h,show ¬ (u ≤ p.length ∧ v ≤ p.length) by omega]

private theorem factor_avg (p : List ℕ) (q r k u v : ℕ) (hr : 0 < r)
    (hc : ∀ c < r, (∑ g : Fin q, if g.val/k%r = c then r else 0) = q) :
    ∑ g : Fin q, factor (p++[g.val]) r k u v = q * factor p r k u v := by
  by_cases he : u = v
  · simp [factor,he]
  by_cases hu : u = p.length
  · subst u
    by_cases hv : v < p.length
    · simpa [factor,he,hv,show v < p.length+1 by omega,List.getD_append,List.getD_append_right] using hc (p.getD v 0/k%r) (Nat.mod_lt _ hr)
    · simp [factor,he,show ¬ v < p.length+1 by omega]
  by_cases hv : v = p.length
  · subst v
    by_cases hl : u < p.length
    · simpa [factor,he,hl,show u < p.length+1 by omega,List.getD_append,List.getD_append_right,eq_comm] using hc (p.getD u 0/k%r) (Nat.mod_lt _ hr)
    · simp [factor,he,show ¬ u < p.length+1 by omega]
  simp [keep p r k u v _ hu hv]

private theorem total_avg {α : Type} (q : ℕ) (l : List α) (f : Fin q → α → ℕ) (z : α → ℕ)
    (h : ∀ x ∈ l, ∑ g, f g x = q*z x) : (∑ g, total l (f g)) = q*total l z := by
  induction l with
  | nil => simp [total]
  | cons x xs ih =>
    simp only [total,List.map_cons,List.sum_cons] at ih ⊢
    rw [sum_add_distrib,h x (by simp),ih (fun y hy => h y (by simp [hy])),Nat.mul_add]

private theorem energy_avg (p : List ℕ) (a : ℕ) (es : List Edge) (hosts : List ℕ) (w v : ℕ)
    (hs : ∀ e ∈ es, ∀ f ∈ es, e.1 ≠ f.2) :
    let q := 64^a; let ks := (List.range a).map (64^·)
    ∑ g : Fin q, energy (p++[g.val]) q es ks hosts w v = q * energy p q es ks hosts w v := by
  intro q ks
  have hq : 0 < q := by dsimp [q]; positivity
  have full := factor_avg p q q 1
  have hfull : ∀ c < q, (∑ g : Fin q, if g.val/1%q = c then q else 0) = q := by
    intro c hc; have hh (g : Fin q) : (g.val = c) = (g = (⟨c,hc⟩ : Fin q)) := by simp [Fin.ext_iff];
    simp [Nat.mod_eq_of_lt (Fin.isLt _),hh]
  have hE : (∑ g : Fin q, edgeCost (p++[g.val]) q es) = q * edgeCost p q es := by
    unfold edgeCost
    apply total_avg; intro e he; apply total_avg; intro f hf
    by_cases h : e.1 = p.length ∨ f.1 = p.length
    · have hb : e.2 ≠ p.length ∧ f.2 ≠ p.length := by
        rcases h with h|h <;> simp only [← h] <;> exact ⟨(hs _ (by assumption) _ he).symm,(hs _ (by assumption) _ hf).symm⟩
      simp_rw [keep p q 1 e.2 f.2 _ hb.1 hb.2, ← sum_mul,full _ _ hq hfull,mul_assoc]
    · push_neg at h
      simp_rw [keep p q 1 e.1 f.1 _ h.1 h.2, ← mul_sum,full _ _ hq hfull]; ring
  have hL : (∑ g : Fin q, legCost (p++[g.val]) ks hosts) = q*legCost p ks hosts := by
    unfold legCost; apply total_avg; intro k hk; apply total_avg; intro x _; apply total_avg; intro y _
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hk
    have hi' := List.mem_range.mp hi
    apply factor_avg _ _ _ _ _ _ (by decide); intro c hc
    have eq : q = ((64^(a-i-1))*64)*64^i := by
      change 64^a = _; rw [←pow_succ,←pow_add]; congr 1; omega
    rw [eq]; apply digit_count <;> first | positivity | assumption
  unfold energy
  rw [sum_add_distrib, ← mul_sum, ← mul_sum,hE,hL]; ring

private def better (cost : ℕ → ℕ) (i j : ℕ) := if cost j < cost i then j else i
private theorem fold_spec (cost : ℕ → ℕ) (xs : List ℕ) (i : ℕ) :
    let z := xs.foldl (better cost) i
    (z = i ∨ z ∈ xs) ∧ cost z ≤ cost i ∧ ∀ x ∈ xs, cost z ≤ cost x := by
  induction xs generalizing i with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hm,h0,h1⟩ := ih (better cost i x)
    have hl : cost (better cost i x) ≤ cost i ∧ cost (better cost i x) ≤ cost x := by unfold better; split <;> omega
    refine ⟨?_,h0.trans hl.1,fun y hy => ?_⟩
    · rcases hm with hm|hm
      · change xs.foldl _ _ = i ∨ xs.foldl _ _ ∈ x::xs; rw [hm]; unfold better; split <;> simp
      · exact Or.inr (List.mem_cons_of_mem _ hm)
    · rcases List.mem_cons.mp hy with rfl|hy; exact h0.trans hl.2; exact h1 y hy

end DetDLP.D2.Descent
open DetDLP.D2.Descent DetDLP.D2.Greedy Finset
theorem solution (vertices : List ℕ) (a : ℕ) (hosts : List ℕ) (es : List Edge)
    (hs : ∀ e ∈ es, ∀ f ∈ es, e.1 ≠ f.2) :
    let q := 64^a; let ks := (List.range a).map (64^·)
    let w := max 1 (hosts.length * maxOn hosts (fun j => hosts.count j))
    let v := es.length * maxOn vertices (fun j => (es.filter (fun e => e.1 == j || e.2 == j)).length)
    let p := solve vertices (List.range q) ks hosts es
    p.length = vertices.length ∧ (∀ x ∈ p, x < q) ∧ energy p q es ks hosts w v ≤ energy [] q es ks hosts w v := by
  intro q ks w v p
  let E := fun z => energy z q es ks hosts w v
  have hq : 0 < q := by dsimp [q]; positivity
  have step (s : List ℕ) : let cost := fun g => E (s++[g]); let z := best cost (List.range q)
                            z < q ∧ cost z ≤ E s := by
    intro cost z
    obtain ⟨hm,_,h⟩ := fold_spec cost (List.range q) 0
    change (z = 0 ∨ _) at hm
    refine ⟨hm.elim (fun he => he ▸ hq) List.mem_range.mp,?_⟩
    apply Nat.le_of_mul_le_mul_left (c := q) _ hq
    calc q*cost z = ∑ _ : Fin q, cost z := by simp
         _ ≤ ∑ g : Fin q, cost g.val := sum_le_sum fun g _ => h _ (List.mem_range.mpr g.isLt)
         _ = _ := energy_avg s a es hosts w v hs
  have aux (vs s : List ℕ) (hb : ∀ x ∈ s, x < q) :
      let t := vs.foldl (fun z _ => z++[best (fun g => E (z++[g])) (List.range q)]) s
      t.length = vs.length+s.length ∧ (∀ x ∈ t, x < q) ∧ E t ≤ E s := by
    induction vs generalizing s with
    | nil => exact ⟨by simp,hb,le_rfl⟩
    | cons j vs ih =>
      let z := best (fun g => E (s++[g])) (List.range q)
      obtain ⟨hl,he⟩ := step s
      obtain ⟨hn,hb',hE⟩ := ih (s++[z]) (by intro x hx; rcases List.mem_append.mp hx with h|h; exact hb x h; simpa [List.mem_singleton.mp h,z] using hl)
      refine ⟨?_,hb',hE.trans he⟩; simp only [List.foldl_cons]; rw [hn]; simp; omega
  simpa [p,solve,E,q,ks,w,v] using aux vertices [] (by simp)
