-- Prove2me | solution 1 for DerandSq.theorem_4_7
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:21:36.045702+00:00
-- url     : https://prove2.me/submissions/7daf274f-c955-4f40-b464-b3099b733ed9

import Mathlib
import Definitions.Def_DerandSq_mGen
import Definitions.Def_DerandSq_dsTree
import Definitions.Def_DerandSq_prunedX
import Definitions.Def_DerandSq_closedWalks
import Definitions.Def_DerandSq_IsVertexTransitive
import Definitions.Def_DerandSq_LambdaH
import Definitions.Def_DerandSq_chi

section
set_option autoImplicit false
namespace DerandSq.Dev.C48b
open DerandSq

/-- a homomorphism out of `Z₂` picking an involution -/
def invHom {G : Type*} [Group G] (s : G) (hs : s * s = 1) : Multiplicative (ZMod 2) →* G where
  toFun x := if x = 1 then 1 else s
  map_one' := by simp
  map_mul' x y := by
    have hx : ∀ z : Multiplicative (ZMod 2), z = 1 ∨ z = Multiplicative.ofAdd 1 := by decide
    rcases hx x with rfl | rfl <;> rcases hx y with rfl | rfl
    · simp
    · simp
    · simp
    · have : (Multiplicative.ofAdd (1 : ZMod 2)) * Multiplicative.ofAdd 1 = 1 := by decide
      have h1 : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide
      simp [this, h1, hs]

theorem invHom_gen {G : Type*} [Group G] (s : G) (hs : s * s = 1) :
    invHom s hs (Multiplicative.ofAdd 1) = s := by
  have h1 : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide
  simp [invHom, h1]

variable {d : ℕ}

end DerandSq.Dev.C48b
end

section
set_option autoImplicit false
namespace DerandSq.Dev.C48a
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

theorem append_left_cancel {u v w : V} (P : G.Walk u v) (q q' : G.Walk v w)
    (h : P.append q = P.append q') : q = q' := by
  induction P with
  | nil => simpa using h
  | cons hh p ih =>
    simp only [Walk.cons_append, Walk.cons.injEq, heq_eq_eq, true_and] at h
    exact ih _ _ h

theorem append_right_cancel {u v w : V} (P : G.Walk v w) (q q' : G.Walk u v)
    (h : q.append P = q'.append P) : q = q' := by
  have := congrArg Walk.reverse h
  simp only [Walk.reverse_append] at this
  have := append_left_cancel _ _ _ this
  simpa using congrArg Walk.reverse this

theorem append_inj_len {u v w : V} (p p' : G.Walk u v) (q q' : G.Walk v w)
    (hl : p.length = p'.length) (h : p.append q = p'.append q') : p = p' ∧ q = q' := by
  induction p with
  | nil =>
    cases p' with
    | nil => exact ⟨rfl, by simpa using h⟩
    | cons _ _ => simp at hl
  | cons hh p ih =>
    cases p' with
    | nil => simp at hl
    | cons hh' p' =>
      simp only [Walk.cons_append, Walk.cons.injEq] at h
      obtain ⟨rfl, h2⟩ := h
      have h3 := eq_of_heq h2
      have := ih p' q q' (by simpa using hl) h3
      obtain ⟨rfl, rfl⟩ := this
      exact ⟨rfl, rfl⟩

/-- closed-walk counts -/
theorem cw_mul (hfin : ∀ (u y : V) (n : ℕ), Finite {w : G.Walk u y // w.length = n})
    (v : V) (a b : ℕ) :
    closedWalks G v a * closedWalks G v b ≤ closedWalks G v (a + b) := by
  unfold closedWalks
  rw [← Nat.card_prod]
  have := hfin v v (a + b)
  refine Nat.card_le_card_of_injective
    (fun x : {w : G.Walk v v // w.length = a} × {w : G.Walk v v // w.length = b} =>
      (⟨x.1.1.append x.2.1, by simp [x.1.2, x.2.2]⟩ : {w : G.Walk v v // w.length = a + b})) ?_
  rintro ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ ⟨⟨p', hp'⟩, ⟨q', hq'⟩⟩ h
  have h1 : p.append q = p'.append q' := congrArg Subtype.val h
  obtain ⟨rfl, rfl⟩ := append_inj_len p p' q q' (by rw [hp, hp']) h1
  rfl

theorem cw_zero_pos (hfin : ∀ (u y : V) (n : ℕ), Finite {w : G.Walk u y // w.length = n})
    (v : V) (n : ℕ) (h : ∃ w : G.Walk v v, w.length = n) : 0 < closedWalks G v n := by
  have := hfin v v n
  obtain ⟨w, hw⟩ := h
  have : Nonempty {w : G.Walk v v // w.length = n} := ⟨⟨w, hw⟩⟩
  exact Nat.card_pos

theorem cw_zero (v : V) : closedWalks G v 0 = 1 := by
  unfold closedWalks
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun a b => Subtype.ext ?_⟩, ⟨⟨Walk.nil, rfl⟩⟩⟩
  have ha := Walk.eq_nil_iff_nil.2 (Walk.length_eq_zero_iff.1 a.2)
  have hb := Walk.eq_nil_iff_nil.2 (Walk.length_eq_zero_iff.1 b.2)
  rw [ha, hb]

theorem cw_pow (hfin : ∀ (u y : V) (n : ℕ), Finite {w : G.Walk u y // w.length = n})
    (v : V) (n q : ℕ) : closedWalks G v n ^ q ≤ closedWalks G v (n * q) := by
  induction q with
  | zero => simp [cw_zero]
  | succ q ih =>
    calc closedWalks G v n ^ (q + 1) = closedWalks G v n ^ q * closedWalks G v n := pow_succ _ _
      _ ≤ closedWalks G v (n * q) * closedWalks G v n := Nat.mul_le_mul_right _ ih
      _ ≤ closedWalks G v (n * q + n) := cw_mul hfin v _ _
      _ = closedWalks G v (n * (q + 1)) := by rw [Nat.mul_succ]

theorem cw_conj (hfin : ∀ (u y : V) (n : ℕ), Finite {w : G.Walk u y // w.length = n})
    {u v : V} (P : G.Walk u v) (n : ℕ) :
    closedWalks G v n ≤ closedWalks G u (n + 2 * P.length) := by
  unfold closedWalks
  have := hfin u u (n + 2 * P.length)
  refine Nat.card_le_card_of_injective
    (fun x : {w : G.Walk v v // w.length = n} =>
      (⟨(P.append x.1).append P.reverse, by simp [x.2]; omega⟩ :
        {w : G.Walk u u // w.length = n + 2 * P.length})) ?_
  rintro ⟨w, hw⟩ ⟨w', hw'⟩ h
  have h1 : (P.append w).append P.reverse = (P.append w').append P.reverse := congrArg Subtype.val h
  have h2 := append_right_cancel _ _ _ h1
  have := append_left_cancel _ _ _ h2
  subst this
  rfl

theorem fin_of_hom {V' : Type*} {G' : SimpleGraph V'} (f : G →g G') (hf : Function.Injective f)
    (hfin : ∀ (u y : V') (n : ℕ), Finite {w : G'.Walk u y // w.length = n}) :
    ∀ (u y : V) (n : ℕ), Finite {w : G.Walk u y // w.length = n} := by
  intro u y n
  have := hfin (f u) (f y) n
  exact Finite.of_injective
    (fun w : {w : G.Walk u y // w.length = n} =>
      (⟨w.1.map f, by simp [w.2]⟩ : {w : G'.Walk (f u) (f y) // w.length = n}))
    (by
      rintro ⟨w, hw⟩ ⟨w', hw'⟩ h
      have := Walk.map_injective_of_injective hf u y (congrArg Subtype.val h)
      exact Subtype.ext this)

theorem cw_le_of_hom {V' : Type*} {G' : SimpleGraph V'} (f : G →g G')
    (hf : Function.Injective f)
    (hfin : ∀ (u y : V') (n : ℕ), Finite {w : G'.Walk u y // w.length = n})
    (u : V) (n : ℕ) : closedWalks G u n ≤ closedWalks G' (f u) n := by
  unfold closedWalks
  have := hfin (f u) (f u) n
  refine Nat.card_le_card_of_injective
    (fun w : {w : G.Walk u u // w.length = n} =>
      (⟨w.1.map f, by simp [w.2]⟩ : {w : G'.Walk (f u) (f u) // w.length = n})) ?_
  rintro ⟨w, hw⟩ ⟨w', hw'⟩ h
  have := Walk.map_injective_of_injective hf u u (congrArg Subtype.val h)
  exact Subtype.ext this

end DerandSq.Dev.C48a
end

section
set_option autoImplicit false

/-! Interfaces for the proof of `DerandSq.theorem_4_7` (q341). Every `sorry` here is a stub
proved in a Part file. -/

namespace DerandSq.Dev.T47
open SimpleGraph

/-- The block data: for every anchor `a`, the function `b ↦ W a b` on `H` is
`((μ - A_H)⁻¹)_{ab} / ((μ - A_H)⁻¹)_{aa}` at `μ = x₀`. -/
structure WData {d : ℕ} (H : SimpleGraph (Fin d)) [DecidableRel H.Adj] where
  W : Fin d → Fin d → ℝ
  μ : ℝ
  K : ℝ
  W_nonneg : ∀ a b, 0 ≤ W a b
  W_self : ∀ a, W a a = 1
  eig : ∀ a j, j ≠ a → ∑ b ∈ Finset.univ.filter (fun b => H.Adj j b), W a b = μ * W a j
  diag : ∀ a, ∑ b ∈ Finset.univ.filter (fun b => H.Adj a b), W a b = K
  lam : μ + ((d : ℝ) - 1) * K = LambdaH d H
  μ_pos : 0 < μ
  K_le : K ≤ μ
  shell : ∀ a, ((d : ℝ) - 1) * ∑ b ∈ Finset.univ.filter (fun b => b ≠ a), W a b ^ 2 = 1

theorem T_fin {d : ℕ} (H : SimpleGraph (Fin d)) :
    ∀ (u y : Gam d) (n : ℕ), Finite {w : (dsTree H).Walk u y // w.length = n} := by
  classical
  have hlf : (dsTree H).LocallyFinite := fun x => by
    have hs : ((dsTree H).neighborSet x).Finite := by
      refine (Set.finite_range (fun p : Fin d × Fin d => x * mGen p.1 * mGen p.2)).subset ?_
      rintro y ⟨_, i, j, _, rfl⟩
      exact ⟨(i, j), rfl⟩
    have : Finite ((dsTree H).neighborSet x) := hs.to_subtype
    exact Fintype.ofFinite _
  intro u y n
  infer_instance

theorem X_le {d : ℕ} (H : SimpleGraph (Fin d)) (i0 : Fin d) : prunedX H i0 ≤ dsTree H :=
  deleteEdges_le _

theorem X_fin {d : ℕ} (H : SimpleGraph (Fin d)) (i0 : Fin d) :
    ∀ (u y : Gam d) (n : ℕ), Finite {w : (prunedX H i0).Walk u y // w.length = n} :=
  DerandSq.Dev.C48a.fin_of_hom (Hom.ofLE (X_le H i0)) Function.injective_id (T_fin H)

end DerandSq.Dev.T47
end

section
set_option autoImplicit false
namespace DerandSq.Dev.T47A
open Polynomial

/-! Part A1: the real-variable part. For a real family `l : Fin d → ℝ`, `χ = ∏ (X - l i)`;
logarithmic derivatives `ψ`, `S₂`, and the existence of the largest root of
`(d-1)χχ'' - (d-2)χ'²` above `k`. -/

noncomputable def chiL {ι : Type*} [Fintype ι] (l : ι → ℝ) : ℝ[X] := ∏ i, (X - C (l i))

noncomputable def psiL {ι : Type*} [Fintype ι] (l : ι → ℝ) (x : ℝ) : ℝ := ∑ i, 1 / (x - l i)

noncomputable def s2L {ι : Type*} [Fintype ι] (l : ι → ℝ) (x : ℝ) : ℝ := ∑ i, 1 / (x - l i) ^ 2

noncomputable def rootL (d : ℕ) (l : Fin d → ℝ) : ℝ[X] :=
  C ((d : ℝ) - 1) * chiL l * derivative (derivative (chiL l)) -
    C ((d : ℝ) - 2) * (derivative (chiL l)) ^ 2

theorem prod_derivs {ι : Type*} [DecidableEq ι] (l : ι → ℝ) (x : ℝ) (s : Finset ι)
    (hx : ∀ i ∈ s, x ≠ l i) :
    (derivative (∏ i ∈ s, (X - C (l i)))).eval x =
        (∏ i ∈ s, (X - C (l i))).eval x * ∑ i ∈ s, 1 / (x - l i) ∧
      (derivative (derivative (∏ i ∈ s, (X - C (l i))))).eval x =
        (∏ i ∈ s, (X - C (l i))).eval x *
          ((∑ i ∈ s, 1 / (x - l i)) ^ 2 - ∑ i ∈ s, 1 / (x - l i) ^ 2) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨h1, h2⟩ := ih (fun i hi => hx i (Finset.mem_insert_of_mem hi))
    have hu : x - l a ≠ 0 := sub_ne_zero.2 (hx a (Finset.mem_insert_self a s))
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
    set Q := ∏ i ∈ s, (X - C (l i))
    set ψ := ∑ i ∈ s, 1 / (x - l i)
    set S := ∑ i ∈ s, 1 / (x - l i) ^ 2
    simp only [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul,
      derivative_add, eval_add, eval_mul, eval_sub, eval_X, eval_C] at h1 h2 ⊢
    rw [h1, h2]
    constructor
    · field_simp
      try ring
    · field_simp
      try ring

theorem chiL_derivs {d : ℕ} (l : Fin d → ℝ) (x : ℝ) (hx : ∀ i, x ≠ l i) :
    (derivative (chiL l)).eval x = (chiL l).eval x * psiL l x ∧
      (derivative (derivative (chiL l))).eval x =
        (chiL l).eval x * (psiL l x ^ 2 - s2L l x) :=
  prod_derivs l x Finset.univ (fun i _ => hx i)

theorem chiL_eval (d : ℕ) (l : Fin d → ℝ) (x : ℝ) : (chiL l).eval x = ∏ i, (x - l i) := by
  simp [chiL, eval_prod]

theorem chiL_ne {d : ℕ} (l : Fin d → ℝ) (x : ℝ) (hx : ∀ i, x ≠ l i) : (chiL l).eval x ≠ 0 := by
  rw [chiL_eval]
  exact Finset.prod_ne_zero_iff.2 fun i _ => sub_ne_zero.2 (hx i)

theorem rootL_eval {d : ℕ} (l : Fin d → ℝ) (x : ℝ) (hx : ∀ i, x ≠ l i) :
    (rootL d l).eval x =
      (chiL l).eval x ^ 2 * (psiL l x ^ 2 - ((d : ℝ) - 1) * s2L l x) := by
  obtain ⟨h1, h2⟩ := chiL_derivs l x hx
  simp only [rootL, eval_sub, eval_mul, eval_C, eval_pow, h1, h2]
  ring

/-- Positivity of `G = ψ² - (d-1)S₂` far to the right. -/
theorem G_pos_far {d k : ℕ} (hd : 3 ≤ d) (hk : 1 ≤ k) (l : Fin d → ℝ)
    (hl : ∀ i, -(k : ℝ) ≤ l i ∧ l i ≤ k) :
    0 < psiL l (4 * d * k) ^ 2 - ((d : ℝ) - 1) * s2L l (4 * d * k) := by
  set x : ℝ := 4 * d * k
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hxk : 0 < x - k := by
    have : (12 : ℝ) * k ≤ x := by simp only [x]; nlinarith
    linarith
  have hψ : (d : ℝ) / (x + k) ≤ psiL l x := by
    have : ∀ i, 1 / (x + k) ≤ 1 / (x - l i) := by
      intro i
      apply one_div_le_one_div_of_le (by linarith [(hl i).2]); linarith [(hl i).1]
    calc (d : ℝ) / (x + k) = ∑ _i : Fin d, 1 / (x + k) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, div_eq_mul_one_div]
      _ ≤ _ := Finset.sum_le_sum fun i _ => this i
  have hS : s2L l x ≤ (d : ℝ) / (x - k) ^ 2 := by
    have : ∀ i, 1 / (x - l i) ^ 2 ≤ 1 / (x - k) ^ 2 := by
      intro i
      apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_left₀ hxk.le (by linarith [(hl i).2]) 2
    calc s2L l x ≤ ∑ _i : Fin d, 1 / (x - k) ^ 2 := Finset.sum_le_sum fun i _ => this i
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hpos : 0 < (d : ℝ) / (x + k) := by positivity
  have h1 : ((d : ℝ) / (x + k)) ^ 2 ≤ psiL l x ^ 2 := pow_le_pow_left₀ hpos.le hψ 2
  have h2 : ((d : ℝ) - 1) * s2L l x ≤ ((d : ℝ) - 1) * ((d : ℝ) / (x - k) ^ 2) :=
    mul_le_mul_of_nonneg_left hS (by linarith)
  have h3 : ((d : ℝ) - 1) * ((d : ℝ) / (x - k) ^ 2) < ((d : ℝ) / (x + k)) ^ 2 := by
    rw [div_pow, mul_div_assoc', div_lt_div_iff₀ (by positivity) (by positivity)]
    have : (x - k) ^ 2 * d - (x + k) ^ 2 * (d - 1) = (k : ℝ) ^ 2 * (8 * d + 1) := by
      simp only [x]; ring
    have : 0 < (k : ℝ) ^ 2 * (8 * d + 1) := by positivity
    nlinarith
  linarith

/-- Negativity of `G` just to the right of `k`. -/
theorem G_neg_near {d k : ℕ} (hd : 3 ≤ d) (hk : 1 ≤ k) (l : Fin d → ℝ)
    (hl : ∀ i, -(k : ℝ) ≤ l i ∧ l i ≤ k) (hsum : ∑ i, l i = 0) (hex : ∃ i, l i = k) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      psiL l (k + t) ^ 2 - ((d : ℝ) - 1) * s2L l (k + t) < 0 := by
  classical
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  set T := Finset.univ.filter (fun i => l i = k) with hT
  set m := T.card with hm
  have hm1 : 1 ≤ m := by
    obtain ⟨i, hi⟩ := hex
    exact Finset.card_pos.2 ⟨i, by simp [hT, hi]⟩
  -- 2m ≤ d from the trace
  have hm2 : 2 * m ≤ d := by
    have hs := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => l i = k) l
    rw [hsum] at hs
    have e1 : ∑ i ∈ T, l i = m * k := by
      rw [Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.1 hi).2), Finset.sum_const,
        nsmul_eq_mul]
    have e2 : -(((d : ℝ) - m) * k) ≤ ∑ i ∈ Finset.univ.filter (fun i => ¬ l i = k), l i := by
      have hc : (Finset.univ.filter (fun i => ¬ l i = k)).card = d - m := by
        have := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i => l i = k)
        simp only [Finset.card_univ, Fintype.card_fin] at this
        rw [hm, hT]; omega
      have := Finset.card_nsmul_le_sum (Finset.univ.filter (fun i => ¬ l i = k)) l (-(k : ℝ))
        (fun i _ => (hl i).1)
      rw [hc, nsmul_eq_mul] at this
      have hmd : m ≤ d := by
        have := Finset.card_le_univ T; simpa using this
      push_cast [hmd] at this
      linarith
    rw [← hT, e1] at hs
    have : (2 * (m : ℝ) - d) * k ≤ 0 := by nlinarith
    have : 2 * (m : ℝ) - d ≤ 0 := by
      by_contra h; push Not at h; nlinarith
    exact_mod_cast (by linarith : (2 * m : ℝ) ≤ d)
  have hmd : (m : ℝ) + 2 ≤ d := by
    have : m + 2 ≤ d := by omega
    exact_mod_cast this
  have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  -- the gap
  obtain ⟨i0, -, hi0⟩ := Finset.exists_min_image Finset.univ
    (fun i => if l i < k then min ((k : ℝ) - l i) 1 else 1)
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  set δ := (if l i0 < k then min ((k : ℝ) - l i0) 1 else 1) with hδ
  have hδpos : 0 < δ := by
    simp only [hδ]; split_ifs with h
    · exact lt_min (by linarith) one_pos
    · exact one_pos
  have hδ1 : δ ≤ 1 := by simp only [hδ]; split_ifs <;> simp
  have hgap : ∀ i, l i ≠ k → δ ≤ k - l i := by
    intro i hi
    have hlt : l i < k := lt_of_le_of_ne (hl i).2 hi
    have := hi0 i (Finset.mem_univ _)
    simp only [hlt, if_true] at this
    exact this.trans (min_le_left _ _)
  set t : ℝ := δ / (4 * d * m) with ht
  have htpos : 0 < t := by positivity
  have ht1 : t ≤ 1 := by
    rw [ht, div_le_one (by positivity)]; nlinarith
  refine ⟨t, htpos, ht1, ?_⟩
  -- bounds for ψ and S₂ at k + t
  have hψ : t * psiL l (k + t) ≤ m + 1 / (4 * m) := by
    unfold psiL
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => l i = k), ← hT]
    have e1 : ∑ i ∈ T, 1 / ((k : ℝ) + t - l i) = m * (1 / t) := by
      rw [Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.1 hi).2])]
      simp [hm]
    have e2 : ∑ i ∈ Finset.univ.filter (fun i => ¬ l i = k), 1 / ((k : ℝ) + t - l i) ≤
        d * (1 / δ) := by
      calc _ ≤ ∑ i ∈ Finset.univ.filter (fun i => ¬ l i = k), 1 / δ := by
            refine Finset.sum_le_sum fun i hi => ?_
            have := hgap i (Finset.mem_filter.1 hi).2
            apply one_div_le_one_div_of_le hδpos; linarith
        _ = (Finset.univ.filter (fun i => ¬ l i = k)).card * (1 / δ) := by simp
        _ ≤ d * (1 / δ) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            have := Finset.card_le_univ (Finset.univ.filter (fun i => ¬ l i = k))
            simp only [Fintype.card_fin] at this; exact_mod_cast this
    rw [e1, mul_add]
    have : t * (m * (1 / t)) = m := by field_simp
    rw [this]
    have : t * (d * (1 / δ)) = 1 / (4 * m) := by
      rw [ht]; field_simp
      try ring
    have h3 := mul_le_mul_of_nonneg_left e2 htpos.le
    linarith
  have hS : (m : ℝ) ≤ t ^ 2 * s2L l (k + t) := by
    unfold s2L
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => l i = k), ← hT]
    have e1 : ∑ i ∈ T, 1 / ((k : ℝ) + t - l i) ^ 2 = m * (1 / t ^ 2) := by
      rw [Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.1 hi).2])]
      simp [hm]
    have e2 : 0 ≤ ∑ i ∈ Finset.univ.filter (fun i => ¬ l i = k), 1 / ((k : ℝ) + t - l i) ^ 2 :=
      Finset.sum_nonneg fun i _ => by positivity
    rw [e1, mul_add]
    have : t ^ 2 * (m * (1 / t ^ 2)) = m := by field_simp
    rw [this]
    nlinarith [sq_nonneg t]
  have hψ0 : 0 ≤ t * psiL l (k + t) := by
    apply mul_nonneg htpos.le
    exact Finset.sum_nonneg fun i _ => by
      have := (hl i).2; apply div_nonneg zero_le_one; linarith
  have hsq : (t * psiL l (k + t)) ^ 2 ≤ (m + 1 / (4 * m)) ^ 2 := pow_le_pow_left₀ hψ0 hψ 2
  have hq : ((m : ℝ) + 1 / (4 * m)) ^ 2 < ((d : ℝ) - 1) * m := by
    have : ((m : ℝ) + 1 / (4 * m)) ^ 2 = m ^ 2 + 1 / 2 + 1 / (16 * m ^ 2) := by
      field_simp; ring
    rw [this]
    have : 1 / (16 * (m : ℝ) ^ 2) ≤ 1 / 16 := by
      apply one_div_le_one_div_of_le (by norm_num); nlinarith
    nlinarith
  have key : t ^ 2 * (psiL l (k + t) ^ 2 - ((d : ℝ) - 1) * s2L l (k + t)) < 0 := by
    have : t ^ 2 * (psiL l (k + t) ^ 2 - ((d : ℝ) - 1) * s2L l (k + t)) =
        (t * psiL l (k + t)) ^ 2 - ((d : ℝ) - 1) * (t ^ 2 * s2L l (k + t)) := by ring
    rw [this]
    have := mul_le_mul_of_nonneg_left hS (by linarith : (0 : ℝ) ≤ (d : ℝ) - 1)
    linarith
  have ht2 : 0 < t ^ 2 := pow_pos htpos 2
  by_contra h
  push Not at h
  linarith [mul_nonneg ht2.le h]

/-- The largest root of `rootL` exceeds `k` and is a root. -/
theorem x0_spec {d k : ℕ} (hd : 3 ≤ d) (hk : 1 ≤ k) (l : Fin d → ℝ)
    (hl : ∀ i, -(k : ℝ) ≤ l i ∧ l i ≤ k) (hsum : ∑ i, l i = 0) (hex : ∃ i, l i = k) :
    (k : ℝ) < sSup {x : ℝ | (rootL d l).eval x = 0} ∧
      (rootL d l).eval (sSup {x : ℝ | (rootL d l).eval x = 0}) = 0 := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨t, ht0, ht1, hneg⟩ := G_neg_near hd hk l hl hsum hex
  have hpos := G_pos_far hd hk l hl
  set x1 : ℝ := k + t
  set x2 : ℝ := 4 * d * k
  have hx1 : ∀ i, x1 ≠ l i := fun i => by have := (hl i).2; simp only [x1]; intro h; linarith
  have hx2 : ∀ i, x2 ≠ l i := fun i => by
    have := (hl i).2
    have : (12 : ℝ) * k ≤ x2 := by simp only [x2]; nlinarith
    intro h; linarith
  have hr1 : (rootL d l).eval x1 < 0 := by
    rw [rootL_eval l x1 hx1]
    exact mul_neg_of_pos_of_neg (by have := chiL_ne l x1 hx1; positivity) hneg
  have hr2 : 0 < (rootL d l).eval x2 := by
    rw [rootL_eval l x2 hx2]
    exact mul_pos (by have := chiL_ne l x2 hx2; positivity) hpos
  have hle : x1 ≤ x2 := by
    simp only [x1, x2]; nlinarith
  obtain ⟨c, hc, hc0⟩ := intermediate_value_Ioo hle (rootL d l).continuous.continuousOn
    ⟨hr1, hr2⟩
  have hne : rootL d l ≠ 0 := by
    intro h; rw [h] at hr2; simp at hr2
  have hfin : {x : ℝ | (rootL d l).eval x = 0}.Finite := by
    convert Polynomial.finite_setOfPred_isRoot hne using 1
    ext x; simp [Polynomial.IsRoot]
  have hmem : c ∈ {x : ℝ | (rootL d l).eval x = 0} := hc0
  have hsup := le_csSup hfin.bddAbove hmem
  refine ⟨?_, Set.Nonempty.csSup_mem ⟨c, hmem⟩ hfin⟩
  have := hc.1
  simp only [x1] at this
  linarith

end DerandSq.Dev.T47A
end

section
set_option autoImplicit false
namespace DerandSq.Dev.T47A
open Polynomial Matrix SimpleGraph Unitary

/-! Part A2: the spectrum of `A_H` and the resolvent `(μ - A_H)⁻¹`. -/

section
variable {d : ℕ} (H : SimpleGraph (Fin d)) [DecidableRel H.Adj]

theorem adj_herm : (H.adjMatrix ℝ).IsHermitian := by
  rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
  exact H.isSymm_adjMatrix

/-- The eigenvalues of `A_H`. -/
noncomputable def lam : Fin d → ℝ := (adj_herm H).eigenvalues

theorem charpoly_eq_chiL : (H.adjMatrix ℝ).charpoly = chiL (lam H) := by
  rw [(adj_herm H).charpoly_eq, chiL, lam]
  simp

theorem chi_eq : chi H = chiL (lam H) := by
  rw [← charpoly_eq_chiL]
  unfold chi
  convert rfl

theorem lam_sum : ∑ i, lam H i = 0 := by
  have := (adj_herm H).trace_eq_sum_eigenvalues
  rw [trace_adjMatrix] at this
  simpa [lam, RCLike.ofReal_real_eq_id] using this.symm

theorem lam_bound {k : ℕ} (hH : H.IsRegularOfDegree k) (i : Fin d) :
    -(k : ℝ) ≤ lam H i ∧ lam H i ≤ k := by
  set hA := adj_herm H
  set v : Fin d → ℝ := ⇑(hA.eigenvectorBasis i)
  have hv : H.adjMatrix ℝ *ᵥ v = lam H i • v := hA.mulVec_eigenvectorBasis i
  have hv0 : v ≠ 0 := (WithLp.ofLp_eq_zero 2).ne.2 <| hA.eigenvectorBasis.orthonormal.ne_zero i
  have hne : (Finset.univ : Finset (Fin d)).Nonempty := by
    by_contra h
    apply hv0; ext j; exact absurd ⟨j, Finset.mem_univ j⟩ h
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun b => |v b|) hne
  have hvj : 0 < |v j| := by
    by_contra h
    apply hv0; ext b
    have := hj b (Finset.mem_univ b)
    simp only [Pi.zero_apply]
    exact abs_nonpos_iff.1 (this.trans (not_lt.1 h))
  have key : |lam H i| * |v j| ≤ k * |v j| := by
    have e := congrFun hv j
    rw [adjMatrix_mulVec_apply, Pi.smul_apply, smul_eq_mul] at e
    rw [← abs_mul, ← e]
    calc |∑ u ∈ H.neighborFinset j, v u| ≤ ∑ u ∈ H.neighborFinset j, |v u| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ u ∈ H.neighborFinset j, |v j| := Finset.sum_le_sum fun u _ => hj u (Finset.mem_univ u)
      _ = k * |v j| := by
          rw [Finset.sum_const, card_neighborFinset_eq_degree, hH j, nsmul_eq_mul]
  have := le_of_mul_le_mul_right key hvj
  exact ⟨by linarith [neg_abs_le (lam H i)], (le_abs_self _).trans this⟩

theorem lam_top {k : ℕ} (hd : 0 < d) (hH : H.IsRegularOfDegree k) : ∃ i, lam H i = k := by
  have hdet : (scalar (Fin d) (k : ℝ) - H.adjMatrix ℝ).det = 0 := by
    rw [← exists_mulVec_eq_zero_iff]
    refine ⟨Function.const _ 1, fun h => ?_, ?_⟩
    · have := congrFun h ⟨0, hd⟩; simp at this
    · ext a
      rw [sub_mulVec, Pi.sub_apply, adjMatrix_mulVec_const_apply_of_regular hH]
      simp
  rw [← eval_charpoly, charpoly_eq_chiL, chiL_eval] at hdet
  obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.1 hdet
  exact ⟨i, (sub_eq_zero.1 hi).symm⟩

/-- Spectral formula for the resolvent. -/
theorem resolvent_spec (μ : ℝ) (hμ : ∀ i, μ ≠ lam H i) :
    ∃ N : Matrix (Fin d) (Fin d) ℝ, (μ • 1 - H.adjMatrix ℝ) * N = 1 ∧
      N.trace = psiL (lam H) μ ∧ (N * N).trace = s2L (lam H) μ := by
  set hA := adj_herm H
  set U : Matrix (Fin d) (Fin d) ℝ := (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)
  have hU1 : star U * U = 1 := Unitary.coe_star_mul_self _
  have hU2 : U * star U = 1 := Unitary.coe_mul_star_self _
  have hspec : H.adjMatrix ℝ = U * diagonal (lam H) * star U := by
    have := hA.spectral_theorem
    rw [conjStarAlgAut_apply] at this
    rw [this]
    simp [U, lam, RCLike.ofReal_real_eq_id]
  set E : Matrix (Fin d) (Fin d) ℝ := diagonal (fun i => 1 / (μ - lam H i))
  have hE : (μ • 1 - diagonal (lam H)) * E = 1 := by
    have hD : μ • (1 : Matrix (Fin d) (Fin d) ℝ) - diagonal (lam H) =
        diagonal (fun i => μ - lam H i) := by
      ext i j; by_cases h : i = j <;> simp [h, one_apply]
    rw [hD, diagonal_mul_diagonal, ← diagonal_one]
    congr 1; ext i
    have : μ - lam H i ≠ 0 := sub_ne_zero.2 (hμ i)
    field_simp
  have hM : μ • (1 : Matrix (Fin d) (Fin d) ℝ) - H.adjMatrix ℝ =
      U * (μ • 1 - diagonal (lam H)) * star U := by
    rw [hspec, mul_sub, sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hU2]
  refine ⟨U * E * star U, ?_, ?_, ?_⟩
  · rw [hM]
    calc U * (μ • 1 - diagonal (lam H)) * star U * (U * E * star U)
        = U * ((μ • 1 - diagonal (lam H)) * (star U * U) * E) * star U := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU1, Matrix.mul_one, hE, Matrix.mul_one, hU2]
  · rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU1, Matrix.one_mul, trace_diagonal]
    rfl
  · have : U * E * star U * (U * E * star U) = U * (E * E) * star U := by
      calc U * E * star U * (U * E * star U) = U * (E * (star U * U) * E) * star U := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hU1, Matrix.mul_one]
    rw [this, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU1, Matrix.one_mul,
      diagonal_mul_diagonal, trace_diagonal]
    unfold s2L
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [div_mul_div_comm, one_mul, sq]

theorem left_inv_unique {M N X : Matrix (Fin d) (Fin d) ℝ} (hMN : M * N = 1) (hX : X * M = 1) :
    X = N := by
  calc X = X * (M * N) := by rw [hMN, Matrix.mul_one]
    _ = N := by rw [← Matrix.mul_assoc, hX, Matrix.one_mul]

theorem resolvent {k : ℕ} (hd : 0 < d) (hH : H.IsRegularOfDegree k) (hvt : IsVertexTransitive H)
    (μ : ℝ) (hμ : (k : ℝ) < μ) :
    ∃ N : Matrix (Fin d) (Fin d) ℝ, (∀ a b, 0 ≤ N a b) ∧ (∀ a b, N a b = N b a) ∧
      (∀ a j, μ * N a j - ∑ b ∈ Finset.univ.filter (fun b => H.Adj a b), N b j =
        if a = j then 1 else 0) ∧
      (∀ a, (d : ℝ) * N a a = psiL (lam H) μ) ∧
      (∀ a, (d : ℝ) * ∑ b, N a b ^ 2 = s2L (lam H) μ) := by
  have hμl : ∀ i, μ ≠ lam H i := fun i h => by
    have := (lam_bound H hH i).2; linarith
  obtain ⟨N, hMN, htr, htr2⟩ := resolvent_spec H μ hμl
  set A := H.adjMatrix ℝ
  set M : Matrix (Fin d) (Fin d) ℝ := μ • 1 - A with hMdef
  have hNM : N * M = 1 := mul_eq_one_comm.1 hMN
  -- symmetry
  have hAT : Aᵀ = A := H.isSymm_adjMatrix
  have hMT : Mᵀ = M := by rw [hMdef, transpose_sub, transpose_smul, transpose_one, hAT]
  have hsymm : Nᵀ = N := by
    apply left_inv_unique hMN
    rw [← hMT, ← transpose_mul, hMN, transpose_one]
  have hsym : ∀ a b, N a b = N b a := fun a b => by
    rw [← transpose_apply N b a, hsymm]
  -- rows
  have hrow : ∀ a j, μ * N a j - ∑ b ∈ Finset.univ.filter (fun b => H.Adj a b), N b j =
      if a = j then 1 else 0 := by
    intro a j
    have e := congrFun (congrFun hMN a) j
    rw [hMdef, sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      one_apply] at e
    have : (A * N) a j = ∑ b ∈ Finset.univ.filter (fun b => H.Adj a b), N b j := by
      rw [← neighborFinset_eq_filter, ← adjMatrix_mulVec_apply]
      rfl
    rw [← this]; exact e
  -- nonnegativity
  have hcard : ∀ a, (Finset.univ.filter (fun b => H.Adj a b)).card = k := fun a => by
    rw [← neighborFinset_eq_filter, card_neighborFinset_eq_degree, hH a]
  have hne : (Finset.univ : Finset (Fin d)).Nonempty := ⟨⟨0, hd⟩, Finset.mem_univ _⟩
  have hnn : ∀ a b, 0 ≤ N a b := by
    intro b j
    obtain ⟨a, -, ha⟩ := Finset.exists_min_image Finset.univ (fun c => N c j) hne
    have e := hrow a j
    have hs : (k : ℝ) * N a j ≤ ∑ c ∈ Finset.univ.filter (fun c => H.Adj a c), N c j := by
      calc (k : ℝ) * N a j = ∑ c ∈ Finset.univ.filter (fun c => H.Adj a c), N a j := by
            rw [Finset.sum_const, hcard, nsmul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum fun c _ => ha c (Finset.mem_univ c)
    have hδ : (0 : ℝ) ≤ if a = j then 1 else 0 := by split_ifs <;> norm_num
    have : 0 ≤ (μ - k) * N a j := by nlinarith
    have h0 : 0 ≤ N a j := by
      by_contra h
      push Not at h
      have := mul_neg_of_pos_of_neg (by linarith : 0 < μ - k) h
      linarith
    exact h0.trans (ha b (Finset.mem_univ b))
  -- invariance under automorphisms
  have hinv : ∀ φ : H ≃g H, N.submatrix φ.toEquiv φ.toEquiv = N := by
    intro φ
    have hAφ : A.submatrix φ.toEquiv φ.toEquiv = A := by
      ext i j
      simp only [submatrix_apply, A, adjMatrix_apply, RelIso.coe_fn_toEquiv, φ.map_adj_iff]
    have hMφ : M.submatrix φ.toEquiv φ.toEquiv = M := by
      ext i j
      have h := congrFun (congrFun hAφ i) j
      simp only [submatrix_apply] at h
      simp only [hMdef, submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, one_apply, h,
        (Equiv.injective _).eq_iff]
    apply left_inv_unique hMN
    rw [← hMφ, submatrix_mul_equiv, hNM, submatrix_one_equiv]
  have hdiag : ∀ a b, N a a = N b b := by
    intro a b
    obtain ⟨φ, hφ⟩ := hvt a b
    have := congrFun (congrFun (hinv φ) a) a
    rw [submatrix_apply, RelIso.coe_fn_toEquiv, hφ] at this
    exact this.symm
  have hdiag2 : ∀ a b, (N * N) a a = (N * N) b b := by
    intro a b
    obtain ⟨φ, hφ⟩ := hvt a b
    have h2 : (N * N).submatrix φ.toEquiv φ.toEquiv = N * N := by
      rw [← submatrix_mul_equiv N N φ.toEquiv φ.toEquiv φ.toEquiv, hinv]
    have := congrFun (congrFun h2 a) a
    rw [submatrix_apply, RelIso.coe_fn_toEquiv, hφ] at this
    exact this.symm
  have hsq : ∀ a, ∑ b, N a b ^ 2 = (N * N) a a := fun a => by
    rw [mul_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [sq, hsym b a]
  refine ⟨N, hnn, hsym, hrow, fun a => ?_, fun a => ?_⟩
  · rw [← htr, trace]
    simp only [diag_apply]
    rw [Finset.sum_congr rfl (fun b _ => hdiag b a), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  · rw [← htr2, trace, hsq]
    simp only [diag_apply]
    rw [Finset.sum_congr rfl (fun b _ => hdiag2 b a), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]

end

end DerandSq.Dev.T47A
end

section
set_option autoImplicit false
namespace DerandSq.Dev.T47A
open DerandSq.Dev.T47

/-- Part A. -/
theorem wdata_exists {d k : ℕ} (hd : 3 ≤ d) (hk : 1 ≤ k) (H : SimpleGraph (Fin d))
    [DecidableRel H.Adj] (hH : H.IsRegularOfDegree k) (hvt : IsVertexTransitive H) :
    Nonempty (WData H) := by
  have hd0 : 0 < d := by omega
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set l := lam H with hl
  have hchi : chi H = chiL l := chi_eq H
  have hroot : rootPoly d H = rootL d l := by unfold rootPoly rootL; rw [hchi]
  have hx0 : x0 d H = sSup {x : ℝ | (rootL d l).eval x = 0} := by unfold x0; rw [hroot]
  obtain ⟨hgt, hzero⟩ := x0_spec hd hk l (lam_bound H hH) (lam_sum H) (lam_top H hd0 hH)
  rw [← hx0] at hgt hzero
  set μ := x0 d H with hμ
  obtain ⟨N, hnn, hsym, hrow, htr, htr2⟩ := resolvent H hd0 hH hvt μ hgt
  have hμl : ∀ i, μ ≠ l i := fun i h => by
    have := (lam_bound H hH i).2; rw [← hl] at this; linarith
  have hχ : (chiL l).eval μ ≠ 0 := chiL_ne l μ hμl
  obtain ⟨h1, -⟩ := chiL_derivs l μ hμl
  set ψ := psiL l μ with hψ
  set S := s2L l μ with hS
  have hterm : ∀ i, 0 < 1 / (μ - l i) := fun i => by
    have := (lam_bound H hH i).2; rw [← hl] at this
    apply one_div_pos.2; linarith
  have hψpos : 0 < ψ := Finset.sum_pos (fun i _ => hterm i) ⟨⟨0, hd0⟩, Finset.mem_univ _⟩
  have hSpos : 0 < S := Finset.sum_pos (fun i _ => by
      have := hterm i; rw [one_div] at this ⊢; rw [← inv_pow]; positivity)
    ⟨⟨0, hd0⟩, Finset.mem_univ _⟩
  have hGS : ψ ^ 2 = ((d : ℝ) - 1) * S := by
    rw [rootL_eval l μ hμl] at hzero
    have := (mul_eq_zero.1 hzero).resolve_left (pow_ne_zero 2 hχ)
    linarith
  have hdpos : (0 : ℝ) < d := by linarith
  have hr : ∀ a, N a a = ψ / d := fun a => by
    rw [eq_div_iff hdpos.ne', mul_comm]; exact htr a
  have hS2 : ∀ a, ∑ b, N a b ^ 2 = S / d := fun a => by
    rw [eq_div_iff hdpos.ne', mul_comm]; exact htr2 a
  have hrpos : 0 < ψ / d := div_pos hψpos hdpos
  refine ⟨{
    W := fun a b => N a b / N a a
    μ := μ
    K := μ - d / ψ
    W_nonneg := fun a b => div_nonneg (hnn a b) (hnn a a)
    W_self := fun a => div_self (by rw [hr a]; exact hrpos.ne')
    eig := ?_
    diag := ?_
    lam := ?_
    μ_pos := by linarith
    K_le := by have : 0 < (d : ℝ) / ψ := div_pos hdpos hψpos; linarith
    shell := ?_ }⟩
  · intro a j hja
    have e := hrow j a
    rw [if_neg hja] at e
    rw [← Finset.sum_div, mul_div_assoc']
    congr 1
    rw [Finset.sum_congr rfl (fun b _ => hsym a b), hsym a j]
    linarith
  · intro a
    have e := hrow a a
    rw [if_pos rfl] at e
    rw [← Finset.sum_div, Finset.sum_congr rfl (fun b _ => hsym a b), hr a]
    have : ∑ b ∈ Finset.univ.filter (fun b => H.Adj a b), N b a = μ * (ψ / d) - 1 := by
      rw [← hr a]; linarith
    rw [this]
    field_simp
  · unfold LambdaH
    rw [← hμ, hchi, h1]
    field_simp
    ring
  · intro a
    rw [Finset.filter_ne', Finset.sum_erase_eq_sub (Finset.mem_univ a)]
    simp only [div_pow]
    rw [← Finset.sum_div, hS2, hr a]
    have hψ2 : ψ ^ 2 ≠ 0 := by positivity
    field_simp
    linear_combination (-(d : ℝ)) * hGS

end DerandSq.Dev.T47A
end

section
set_option autoImplicit false

/-! Normal form of `Gam d`: the reduced word of `g`, reversed (head = last letter). -/

namespace DerandSq.Dev.T47Word
open DerandSq

variable {d : ℕ}

/-- toggle the head letter `i` -/
def tog (i : Fin d) : List (Fin d) → List (Fin d)
  | [] => [i]
  | j :: L => if j = i then L else i :: j :: L

@[simp] theorem tog_nil (i : Fin d) : tog i [] = [i] := rfl
theorem tog_cons (i j : Fin d) (L : List (Fin d)) :
    tog i (j :: L) = if j = i then L else i :: j :: L := rfl
@[simp] theorem tog_cons_self (i : Fin d) (L : List (Fin d)) : tog i (i :: L) = L := by
  simp [tog_cons]
theorem tog_cons_ne (i j : Fin d) (L : List (Fin d)) (h : j ≠ i) :
    tog i (j :: L) = i :: j :: L := by simp [tog_cons, h]

/-- reduced lists -/
def Red (L : List (Fin d)) : Prop := L.IsChain (· ≠ ·)

theorem red_tog (i : Fin d) (L : List (Fin d)) (h : Red L) : Red (tog i L) := by
  unfold Red at *
  cases L with
  | nil => exact List.isChain_singleton _
  | cons j L =>
    by_cases hj : j = i
    · subst hj; simp only [tog_cons_self]; exact h.tail
    · rw [tog_cons_ne _ _ _ hj]
      exact List.isChain_cons_cons.2 ⟨fun h' => hj h'.symm, h⟩

theorem tog_tog (i : Fin d) (L : List (Fin d)) (h : Red L) : tog i (tog i L) = L := by
  cases L with
  | nil => simp
  | cons j L =>
    by_cases hj : j = i
    · subst hj
      simp only [tog_cons_self]
      cases L with
      | nil => simp
      | cons k L =>
        have hk : j ≠ k := by
          unfold Red at h; exact (List.isChain_cons_cons.1 h).1
        rw [tog_cons_ne _ _ _ (Ne.symm hk)]
    · rw [tog_cons_ne _ _ _ hj, tog_cons_self]

abbrev RL (d : ℕ) := {L : List (Fin d) // Red L}

def togP (i : Fin d) : Equiv.Perm (RL d) where
  toFun L := ⟨tog i L.1, red_tog i L.1 L.2⟩
  invFun L := ⟨tog i L.1, red_tog i L.1 L.2⟩
  left_inv L := Subtype.ext (tog_tog i L.1 L.2)
  right_inv L := Subtype.ext (tog_tog i L.1 L.2)

theorem togP_sq (i : Fin d) : togP i * togP i = 1 := by
  ext L
  simp [togP, tog_tog i L.1 L.2]

noncomputable def act : Gam d →* Equiv.Perm (RL d) :=
  Monoid.CoprodI.lift (fun i => DerandSq.Dev.C48b.invHom (togP i) (togP_sq i))

theorem act_mGen (i : Fin d) : act (mGen i) = togP i := by
  unfold act mGen
  rw [Monoid.CoprodI.lift_of]
  exact DerandSq.Dev.C48b.invHom_gen _ _

theorem mGen_inv (i : Fin d) : (mGen i)⁻¹ = mGen i :=
  inv_eq_of_mul_eq_one_right (mGen_mul_self i)

/-- the reversed reduced word of `g` -/
noncomputable def word (g : Gam d) : List (Fin d) := (act g⁻¹ ⟨[], List.isChain_nil⟩).1

theorem word_red (g : Gam d) : Red (word g) := (act g⁻¹ _).2

@[simp] theorem word_one : word (1 : Gam d) = [] := by simp [word]

theorem word_mul_mGen (g : Gam d) (i : Fin d) : word (g * mGen i) = tog i (word g) := by
  simp only [word, mul_inv_rev, mGen_inv, map_mul, Equiv.Perm.coe_mul, Function.comp_apply,
    act_mGen]
  rfl

theorem word_mul2 (g : Gam d) (a b : Fin d) :
    word (g * mGen a * mGen b) = tog b (tog a (word g)) := by
  rw [word_mul_mGen, word_mul_mGen]

/-- inverse of `word` -/
def unword (L : List (Fin d)) : Gam d := (L.reverse.map mGen).prod

@[simp] theorem unword_nil : unword ([] : List (Fin d)) = 1 := rfl
theorem unword_cons (j : Fin d) (L : List (Fin d)) : unword (j :: L) = unword L * mGen j := by
  simp [unword]

theorem unword_tog (i : Fin d) (L : List (Fin d)) : unword (tog i L) = unword L * mGen i := by
  cases L with
  | nil => simp [unword_cons]
  | cons j L =>
    by_cases hj : j = i
    · subst hj; simp [unword_cons, mul_assoc, mGen_mul_self]
    · rw [tog_cons_ne _ _ _ hj, unword_cons]

theorem unword_word (g : Gam d) : unword (word g) = g := by
  suffices h : ∀ h : Gam d, unword (word h) = h → unword (word (h * g)) = h * g by
    simpa using h 1 (by simp)
  induction g using Monoid.CoprodI.induction_left with
  | one => intro h hh; simpa using hh
  | mul m x ih =>
    intro h hh
    rename_i i
    rw [← mul_assoc]
    apply ih
    have hm : ∀ z : Multiplicative (ZMod 2), z = 1 ∨ z = Multiplicative.ofAdd 1 := by decide
    rcases hm m with rfl | rfl
    · simpa using hh
    · change unword (word (h * mGen i)) = h * mGen i
      rw [word_mul_mGen, unword_tog, hh]

theorem word_unword (L : List (Fin d)) (hL : Red L) : word (unword L) = L := by
  induction L with
  | nil => simp
  | cons j L ih =>
    rw [unword_cons, word_mul_mGen, ih hL.tail]
    cases L with
    | nil => simp
    | cons k L =>
      have : j ≠ k := (List.isChain_cons_cons.1 hL).1
      rw [tog_cons_ne _ _ _ (Ne.symm this)]

theorem word_mGen_mGen (a b : Fin d) (h : a ≠ b) : word (mGen a * mGen b) = [b, a] := by
  have : word (1 * mGen a * mGen b) = [b, a] := by
    rw [word_mul2, word_one, tog_nil, tog_cons_ne _ _ _ h]
  simpa using this

/-! Neighbours in `dsTree`. -/

theorem mul_mGen_mGen_inj (g : Gam d) (a b a' b' : Fin d) (h : a ≠ b) (h' : a' ≠ b')
    (e : g * mGen a * mGen b = g * mGen a' * mGen b') : a = a' ∧ b = b' := by
  rw [mul_assoc, mul_assoc] at e
  have e2 := congrArg word (mul_left_cancel e)
  rw [word_mGen_mGen _ _ h, word_mGen_mGen _ _ h'] at e2
  simp only [List.cons.injEq, and_true] at e2
  exact ⟨e2.2, e2.1⟩

theorem ne_mul_mGen_mGen (g : Gam d) (a b : Fin d) (h : a ≠ b) : g ≠ g * mGen a * mGen b := by
  intro e
  have e2 := congrArg word e
  rw [word_mul2] at e2
  have hr := word_red g
  generalize word g = L at e2 hr
  cases L with
  | nil => simp [tog_cons_ne _ _ _ h] at e2
  | cons j L =>
    by_cases hj : j = a
    · subst hj
      simp only [tog_cons_self] at e2
      cases L with
      | nil => simp at e2; exact h e2
      | cons k L =>
        by_cases hk : k = b
        · subst hk
          simp only [tog_cons_self] at e2
          have := congrArg List.length e2; simp at this; omega
        · rw [tog_cons_ne _ _ _ hk] at e2
          simp at e2; exact h e2
    · rw [tog_cons_ne _ _ _ hj, tog_cons_ne _ _ _ h] at e2
      have := congrArg List.length e2; simp at this

theorem dsTree_adj_iff (H : SimpleGraph (Fin d)) (g h : Gam d) :
    (dsTree H).Adj g h ↔ ∃ a b, H.Adj a b ∧ h = g * mGen a * mGen b := by
  constructor
  · rintro ⟨_, h⟩; exact h
  · rintro ⟨a, b, hab, rfl⟩
    exact ⟨ne_mul_mGen_mGen g a b hab.ne, a, b, hab, rfl⟩

/-- the ordered edges of `H` -/
def edges (H : SimpleGraph (Fin d)) [DecidableRel H.Adj] : Finset (Fin d × Fin d) :=
  Finset.univ.filter (fun p => H.Adj p.1 p.2)

theorem nbr_image (H : SimpleGraph (Fin d)) [DecidableRel H.Adj] (g : Gam d) :
    Set.InjOn (fun p : Fin d × Fin d => g * mGen p.1 * mGen p.2) (edges H) := by
  intro p hp q hq e
  simp only [edges, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp hq
  obtain ⟨h1, h2⟩ := mul_mGen_mGen_inj g _ _ _ _ hp.ne hq.ne e
  exact Prod.ext h1 h2

/-- A sum over the neighbours of `g` in a finset `B`, as a sum over the edges of `H`. -/
theorem sum_adj_eq (H : SimpleGraph (Fin d)) [DecidableRel H.Adj] (g : Gam d)
    (B : Finset (Gam d)) (φ : Gam d → ℝ) [DecidablePred (fun v => (dsTree H).Adj g v)]
    [DecidablePred (· ∈ B)] :
    ∑ v ∈ B, (if (dsTree H).Adj g v then φ v else 0) =
      ∑ p ∈ edges H, if g * mGen p.1 * mGen p.2 ∈ B then φ (g * mGen p.1 * mGen p.2) else 0 := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  have : B.filter (fun v => (dsTree H).Adj g v) =
      ((edges H).filter (fun p => g * mGen p.1 * mGen p.2 ∈ B)).image
        (fun p : Fin d × Fin d => g * mGen p.1 * mGen p.2) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_image, dsTree_adj_iff, edges, Finset.mem_univ,
      true_and, Prod.exists]
    constructor
    · rintro ⟨hv, a, b, hab, rfl⟩; exact ⟨a, b, ⟨hab, hv⟩, rfl⟩
    · rintro ⟨a, b, ⟨hab, hv⟩, rfl⟩; exact ⟨hv, a, b, hab, rfl⟩
  rw [this, Finset.sum_image]
  intro p hp q hq e
  exact nbr_image H g (Finset.mem_filter.1 hp).1 (Finset.mem_filter.1 hq).1 e

/-! `prunedX`: deleted edges. -/

theorem deleted_word (i0 : Fin d) (H : SimpleGraph (Fin d)) (u v : Gam d)
    (h : (dsTree H).Adj u v) (hX : ¬ (prunedX H i0).Adj u v) :
    ∃ x, (word u = [x, i0] ∧ x ≠ i0) ∨ (word v = [x, i0] ∧ x ≠ i0) := by
  unfold prunedX at hX
  rw [SimpleGraph.deleteEdges_adj] at hX
  push Not at hX
  obtain ⟨i, j, hij, e⟩ := hX h
  rw [Sym2.eq_iff] at e
  by_cases hi : i = i0
  · subst hi
    refine ⟨j, ?_⟩
    rcases e with ⟨_, rfl⟩ | ⟨rfl, _⟩
    · right; exact ⟨word_mGen_mGen _ _ hij.ne, hij.ne.symm⟩
    · left; exact ⟨word_mGen_mGen _ _ hij.ne, hij.ne.symm⟩
  · refine ⟨i, ?_⟩
    rcases e with ⟨rfl, _⟩ | ⟨_, rfl⟩
    · left; exact ⟨word_mGen_mGen _ _ (Ne.symm hi), hi⟩
    · right; exact ⟨word_mGen_mGen _ _ (Ne.symm hi), hi⟩

end DerandSq.Dev.T47Word
end

section
set_option autoImplicit false

namespace DerandSq.Dev.T47B
open SimpleGraph DerandSq DerandSq.Dev.T47 DerandSq.Dev.T47Word

variable {d : ℕ}

/-- the eigenfunction on reversed words -/
def Fw (W : Fin d → Fin d → ℝ) : List (Fin d) → ℝ
  | [] => 1
  | [_] => 0
  | j :: i :: L => W i j * Fw W L

@[simp] theorem Fw_nil (W : Fin d → Fin d → ℝ) : Fw W [] = 1 := rfl
@[simp] theorem Fw_single (W : Fin d → Fin d → ℝ) (i : Fin d) : Fw W [i] = 0 := rfl
@[simp] theorem Fw_cons2 (W : Fin d → Fin d → ℝ) (i j : Fin d) (L : List (Fin d)) :
    Fw W (j :: i :: L) = W i j * Fw W L := rfl

theorem Fw_nonneg (W : Fin d → Fin d → ℝ) (hW : ∀ a b, 0 ≤ W a b) :
    ∀ L : List (Fin d), 0 ≤ Fw W L
  | [] => by simp
  | [_] => by simp
  | _ :: _ :: L => by rw [Fw_cons2]; exact mul_nonneg (hW _ _) (Fw_nonneg W hW L)

theorem sum_edges (H : SimpleGraph (Fin d)) [DecidableRel H.Adj] (g : Fin d × Fin d → ℝ) :
    ∑ p ∈ edges H, g p = ∑ a, ∑ b ∈ Finset.univ.filter (fun b => H.Adj a b), g (a, b) := by
  rw [edges, Finset.sum_filter, ← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_filter]

theorem card_erase_real (j : Fin d) : ((Finset.univ.erase j).card : ℝ) = (d : ℝ) - 1 := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have : 1 ≤ d := by have := j.2; omega
  push_cast [this]; ring

/-- the eigen-inequality on lists -/
theorem list_step (H : SimpleGraph (Fin d)) [DecidableRel H.Adj] (D : WData H)
    (L : List (Fin d)) (hL : Red L) :
    ∑ p ∈ edges H, Fw D.W (tog p.2 (tog p.1 L)) ≤ (D.μ + ((d : ℝ) - 1) * D.K) * Fw D.W L := by
  rw [sum_edges]
  match L, hL with
  | [], _ =>
    have h1 : ∀ a, ∑ b ∈ Finset.univ.filter (fun b => H.Adj a b),
        Fw D.W (tog (a, b).2 (tog (a, b).1 [])) = D.K := by
      intro a
      rw [← D.diag a]
      refine Finset.sum_congr rfl fun b hb => ?_
      have hab : a ≠ b := (Finset.mem_filter.1 hb).2.ne
      simp [tog_cons_ne _ _ _ hab]
    simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Fw_nil,
      mul_one]
    nlinarith [D.K_le]
  | [i], _ =>
    have h1 : ∀ a, ∑ b ∈ Finset.univ.filter (fun b => H.Adj a b),
        Fw D.W (tog (a, b).2 (tog (a, b).1 [i])) = 0 := by
      intro a
      refine Finset.sum_eq_zero fun b hb => ?_
      have hab : a ≠ b := (Finset.mem_filter.1 hb).2.ne
      by_cases hia : i = a
      · subst hia; simp
      · simp [tog_cons_ne _ _ _ hia, tog_cons_ne _ _ _ hab]
    simp [h1]
  | j :: i :: L, hL =>
    have hji : j ≠ i := (List.isChain_cons_cons.1 hL).1
    have hj : ∑ b ∈ Finset.univ.filter (fun b => H.Adj j b),
        Fw D.W (tog (j, b).2 (tog (j, b).1 (j :: i :: L))) = D.μ * (D.W i j * Fw D.W L) := by
      have : ∀ b, Fw D.W (tog b (i :: L)) = D.W i b * Fw D.W L := by
        intro b
        by_cases hib : i = b
        · subst hib; simp [D.W_self]
        · simp [tog_cons_ne _ _ _ hib]
      simp only [tog_cons_self, this]
      rw [← Finset.sum_mul, D.eig i j hji, mul_assoc]
    have ha : ∀ a ∈ Finset.univ.erase j, ∑ b ∈ Finset.univ.filter (fun b => H.Adj a b),
        Fw D.W (tog (a, b).2 (tog (a, b).1 (j :: i :: L))) = D.K * (D.W i j * Fw D.W L) := by
      intro a ha
      have hja : j ≠ a := Ne.symm (Finset.ne_of_mem_erase ha)
      rw [← D.diag a, Finset.sum_mul]
      refine Finset.sum_congr rfl fun b hb => ?_
      have hab : a ≠ b := (Finset.mem_filter.1 hb).2.ne
      simp [tog_cons_ne _ _ _ hja, tog_cons_ne _ _ _ hab]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), hj, Finset.sum_congr rfl ha,
      Finset.sum_const, nsmul_eq_mul, card_erase_real, Fw_cons2]
    nlinarith

theorem nbr_step (H : SimpleGraph (Fin d)) [DecidableRel H.Adj] (D : WData H) (g : Gam d) :
    ∑ p ∈ edges H, Fw D.W (word (g * mGen p.1 * mGen p.2)) ≤
      (D.μ + ((d : ℝ) - 1) * D.K) * Fw D.W (word g) := by
  simp only [word_mul2]
  exact list_step H D _ (word_red g)

/-- local finiteness of `dsTree H`, via the edge parametrization -/
@[instance_reducible]
noncomputable def lf (H : SimpleGraph (Fin d)) [DecidableRel H.Adj] [DecidableEq (Gam d)] :
    (dsTree H).LocallyFinite := fun x =>
  Fintype.ofFinset ((edges H).image (fun p : Fin d × Fin d => x * mGen p.1 * mGen p.2))
    (fun v => by
      simp only [Finset.mem_image, edges, Finset.mem_filter, Finset.mem_univ, true_and,
        Prod.exists, mem_neighborSet, dsTree_adj_iff]
      constructor
      · rintro ⟨a, b, h, rfl⟩; exact ⟨a, b, h, rfl⟩
      · rintro ⟨a, b, h, rfl⟩; exact ⟨a, b, h, rfl⟩)

theorem walk_bound (H : SimpleGraph (Fin d)) [DecidableRel H.Adj] [DecidableEq (Gam d)]
    (f : Gam d → ℝ) (hf : ∀ v, 0 ≤ f v) (Λ : ℝ) (hΛ : 0 ≤ Λ)
    (hnb : ∀ u, ∑ p ∈ edges H, f (u * mGen p.1 * mGen p.2) ≤ Λ * f u) :
    ∀ (n : ℕ) (u v : Gam d),
      ((@finsetWalkLength _ (dsTree H) _ (lf H) n u v).card : ℝ) * f v ≤ Λ ^ n * f u := by
  let _ := lf H
  intro n
  induction n with
  | zero =>
    intro u v
    by_cases huv : u = v
    · subst huv; simp [finsetWalkLength]
    · simp [finsetWalkLength, huv, hf u]
  | succ n ih =>
    intro u v
    have hc : ((finsetWalkLength (dsTree H) (n + 1) u v).card : ℝ) ≤
        ∑ w : (dsTree H).neighborSet u, ((finsetWalkLength (dsTree H) n w v).card : ℝ) := by
      rw [finsetWalkLength]
      exact_mod_cast (Finset.card_biUnion_le).trans (by simp)
    have hs : ∑ w : (dsTree H).neighborSet u, f w ≤ Λ * f u := by
      refine le_trans (le_of_eq ?_) (hnb u)
      rw [← Finset.sum_coe_sort (edges H)]
      let e : (edges H) → (dsTree H).neighborSet u := fun p =>
        ⟨u * mGen p.1.1 * mGen p.1.2,
          (dsTree_adj_iff H _ _).2 ⟨_, _, (Finset.mem_filter.1 p.2).2, rfl⟩⟩
      have he : Function.Bijective e := by
        constructor
        · rintro p q h
          exact Subtype.ext (nbr_image H u p.2 q.2 (congrArg Subtype.val h))
        · rintro ⟨w, hw⟩
          obtain ⟨a, b, hab, rfl⟩ := (dsTree_adj_iff H _ _).1 hw
          exact ⟨⟨(a, b), Finset.mem_filter.2 ⟨Finset.mem_univ _, hab⟩⟩, rfl⟩
      exact (Fintype.sum_bijective e he _ _ (fun p => rfl)).symm
    calc ((finsetWalkLength (dsTree H) (n + 1) u v).card : ℝ) * f v
        ≤ (∑ w : (dsTree H).neighborSet u,
            ((finsetWalkLength (dsTree H) n w v).card : ℝ)) * f v :=
          mul_le_mul_of_nonneg_right hc (hf v)
      _ = ∑ w : (dsTree H).neighborSet u,
            ((finsetWalkLength (dsTree H) n w v).card : ℝ) * f v := Finset.sum_mul _ _ _
      _ ≤ ∑ w : (dsTree H).neighborSet u, Λ ^ n * f w :=
          Finset.sum_le_sum fun w _ => ih w v
      _ = Λ ^ n * ∑ w : (dsTree H).neighborSet u, f w := (Finset.mul_sum _ _ _).symm
      _ ≤ Λ ^ n * (Λ * f u) := mul_le_mul_of_nonneg_left hs (pow_nonneg hΛ n)
      _ = Λ ^ (n + 1) * f u := by ring

/-- Part B: the upper bound on the full tree. -/
theorem upper_T {d : ℕ} (hd : 3 ≤ d) (H : SimpleGraph (Fin d)) [DecidableRel H.Adj]
    (D : WData H) (n : ℕ) :
    (closedWalks (dsTree H) 1 n : ℝ) ≤ (LambdaH d H) ^ n := by
  classical
  let _ := lf H
  have hK : 0 ≤ D.K := by
    rw [← D.diag ⟨0, by omega⟩]
    exact Finset.sum_nonneg fun b _ => D.W_nonneg _ _
  have hd1 : (0 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hΛ : 0 ≤ LambdaH d H := by
    rw [← D.lam]; have := D.μ_pos; positivity
  have key := walk_bound H (fun g => Fw D.W (word g)) (fun g => Fw_nonneg _ D.W_nonneg _)
    (LambdaH d H) hΛ (fun u => by rw [← D.lam]; exact nbr_step H D u) n 1 1
  simp only [word_one, Fw_nil, mul_one] at key
  have hc : closedWalks (dsTree H) 1 n = (finsetWalkLength (dsTree H) n 1 1).card := by
    rw [closedWalks, Nat.card_eq_fintype_card]
    exact card_set_walk_length_eq (dsTree H) 1 1 n
  rw [hc]
  exact key

end DerandSq.Dev.T47B
end

section
set_option autoImplicit false
namespace DerandSq.Dev.T47C1
open SimpleGraph Matrix

theorem dot_pow {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (x : ι → ℝ) (hM : M.IsSymm)
    (i j : ℕ) : (M ^ i *ᵥ x) ⬝ᵥ (M ^ j *ᵥ x) = x ⬝ᵥ (M ^ (i + j) *ᵥ x) := by
  have hT : (M ^ i)ᵀ = M ^ i := by rw [transpose_pow, hM.eq]
  conv_lhs => rw [← hT, mulVec_transpose, ← dotProduct_mulVec, mulVec_mulVec, ← pow_add]

theorem entry_sq_le {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (hM : M.IsSymm) (p : ℕ)
    (u v : ι) : ((M ^ (2 * p)) u v) ^ 2 ≤ (M ^ (2 * p)) u u * (M ^ (2 * p)) v v := by
  have hT : (M ^ p)ᵀ = M ^ p := by rw [transpose_pow, hM.eq]
  have e : ∀ a b, (M ^ (2 * p)) a b = ∑ w, (M ^ p) a w * (M ^ p) b w := by
    intro a b
    rw [two_mul, pow_add, mul_apply]
    refine Finset.sum_congr rfl fun w _ => ?_
    congr 1
    rw [← hT, transpose_apply, hT]
  rw [e, e, e]
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun w => (M ^ p) u w) (fun w => (M ^ p) v w)
  simpa [sq] using this

theorem cw_mono {V : Type*} {G : SimpleGraph V}
    (hfin : ∀ (u y : V) (n : ℕ), Finite {w : G.Walk u y // w.length = n})
    (e : V) (he : ∃ v, G.Adj e v) (a j : ℕ) :
    closedWalks G e a ≤ closedWalks G e (a + 2 * j) := by
  obtain ⟨v, hv⟩ := he
  have h2 : 1 ≤ closedWalks G e 2 :=
    DerandSq.Dev.C48a.cw_zero_pos hfin e 2 ⟨Walk.cons hv (Walk.cons hv.symm Walk.nil), rfl⟩
  have hp : 1 ≤ closedWalks G e (2 * j) :=
    (Nat.one_le_pow _ _ h2).trans (DerandSq.Dev.C48a.cw_pow hfin e 2 j)
  calc closedWalks G e a = closedWalks G e a * 1 := (mul_one _).symm
    _ ≤ closedWalks G e a * closedWalks G e (2 * j) := Nat.mul_le_mul_left _ hp
    _ ≤ _ := DerandSq.Dev.C48a.cw_mul hfin e _ _

open Classical in
/-- Part C1: a Rayleigh quotient on a finite set bounds closed-walk counts from below. -/
theorem rayleigh_walks {V : Type*} (G : SimpleGraph V)
    (hfin : ∀ (u y : V) (n : ℕ), Finite {w : G.Walk u y // w.length = n})
    (e : V) (he : ∃ v, G.Adj e v) (B : Finset V) (f : V → ℝ) (hf : ∀ v, 0 ≤ f v)
    (R : ℕ) (hreach : ∀ u ∈ B, ∃ w : G.Walk e u, w.length ≤ R) (r : ℝ) (hr : 0 ≤ r)
    (hQ : r * ∑ u ∈ B, f u ^ 2 ≤ ∑ u ∈ B, ∑ v ∈ B, if G.Adj u v then f u * f v else 0)
    (p : ℕ) :
    (∑ u ∈ B, f u ^ 2) * r ^ (2 * p) ≤
      (∑ u ∈ B, f u) ^ 2 * (closedWalks G e (2 * p + 2 * R) : ℝ) := by
  set s := ∑ u ∈ B, f u ^ 2 with hs
  set C := (closedWalks G e (2 * p + 2 * R) : ℝ) with hC
  let G' : SimpleGraph B := G.comap (Function.Embedding.subtype (· ∈ B))
  let φ : G' →g G := ⟨Subtype.val, fun h => h⟩
  have hφ : Function.Injective φ := Subtype.val_injective
  let M : Matrix B B ℝ := G'.adjMatrix ℝ
  have hM : M.IsSymm := G'.isSymm_adjMatrix
  let x : B → ℝ := fun u => f u
  let b : ℕ → ℝ := fun j => x ⬝ᵥ (M ^ j *ᵥ x)
  have hb : ∀ i j, b (i + j) = (M ^ i *ᵥ x) ⬝ᵥ (M ^ j *ᵥ x) :=
    fun i j => (dot_pow M x hM i j).symm
  have hbnn : ∀ m, 0 ≤ b (2 * m) := by
    intro m
    rw [two_mul, hb]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hcs : ∀ m, b (2 * m + 2) ^ 2 ≤ b (2 * m) * b (2 * m + 4) := by
    intro m
    have h1 : 2 * m + 2 = m + (m + 2) := by ring
    have h2 : 2 * m + 4 = (m + 2) + (m + 2) := by ring
    rw [h1, h2, hb, hb, two_mul, hb]
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _ |>.trans_eq (by simp [dotProduct, sq])
  have hb0 : b 0 = s := by
    simp only [b, pow_zero, one_mulVec, dotProduct, x, hs, sq]
    exact Finset.sum_coe_sort B (fun u => f u * f u)
  have hb1 : b 1 = ∑ u ∈ B, ∑ v ∈ B, if G.Adj u v then f u * f v else 0 := by
    simp only [b, pow_one, dotProduct, mulVec, x, M, adjMatrix_apply, Finset.mul_sum]
    rw [← Finset.sum_coe_sort B]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Finset.sum_coe_sort B]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [G', comap_adj, Function.Embedding.subtype_apply]
    split_ifs <;> ring
  have hb2 : b 1 ^ 2 ≤ b 0 * b 2 := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, hb, show (2 : ℕ) = 1 + 1 from rfl, hb, show (0 : ℕ) = 0 + 0 from rfl, hb]
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _ |>.trans_eq (by simp [dotProduct, sq])
  -- lower bound
  have hlow : s * r ^ (2 * p) ≤ b (2 * p) := by
    rcases (Finset.sum_nonneg (fun u _ => sq_nonneg (f u)) : 0 ≤ s).eq_or_lt with h0 | hpos
    · have h0' : s = 0 := h0.symm
      rw [h0', zero_mul]; exact hbnn p
    have step : ∀ m, r ^ 2 * b (2 * m) ≤ b (2 * m + 2) := by
      intro m
      induction m with
      | zero =>
        simp only [mul_zero, zero_add]
        rw [hb0]
        have ha : r * s ≤ b 1 := hb1 ▸ hQ
        have hrs : 0 ≤ r * s := mul_nonneg hr hpos.le
        have : (r * s) ^ 2 ≤ s * b 2 := (pow_le_pow_left₀ hrs ha 2).trans (hb0 ▸ hb2)
        nlinarith
      | succ m ih =>
        have e1 : 2 * (m + 1) = 2 * m + 2 := by ring
        have e2 : 2 * m + 2 + 2 = 2 * m + 4 := by ring
        rw [e1, e2]
        have hc := hcs m
        have hm := hbnn m
        have hm1 : 0 ≤ b (2 * m + 2) := by simpa [e1] using hbnn (m + 1)
        have hm2 : 0 ≤ b (2 * m + 4) := by
          have := hbnn (m + 2); rwa [show 2 * (m + 2) = 2 * m + 4 by ring] at this
        rcases hm.eq_or_lt with h | h
        · rw [← h] at hc
          have : b (2 * m + 2) = 0 := by nlinarith
          rw [this, mul_zero]; exact hm2
        · have : r ^ 2 * b (2 * m + 2) * b (2 * m) ≤ b (2 * m + 4) * b (2 * m) := by
            nlinarith [mul_le_mul_of_nonneg_left ih hm1]
          exact le_of_mul_le_mul_right this h
    have : ∀ m, s * (r ^ 2) ^ m ≤ b (2 * m) := by
      intro m
      induction m with
      | zero => simp [hb0]
      | succ m ih =>
        rw [pow_succ, show 2 * (m + 1) = 2 * m + 2 by ring]
        have := step m
        nlinarith [sq_nonneg r, pow_nonneg (sq_nonneg r) m]
    simpa [pow_mul] using this p
  -- upper bound
  have hdiag : ∀ u : B, (M ^ (2 * p)) u u ≤ C := by
    intro u
    rw [adjMatrix_pow_apply_eq_card_walk]
    have h1 : Fintype.card {q : G'.Walk u u | q.length = 2 * p} = closedWalks G' u (2 * p) := by
      unfold closedWalks; rw [Nat.card_eq_fintype_card]; rfl
    rw [h1]
    obtain ⟨w, hw⟩ := hreach u u.2
    have h2 := DerandSq.Dev.C48a.cw_le_of_hom φ hφ hfin u (2 * p)
    have h3 := DerandSq.Dev.C48a.cw_conj hfin w (2 * p)
    have h4 := cw_mono hfin e he (2 * p + 2 * w.length) (R - w.length)
    have h5 : 2 * p + 2 * w.length + 2 * (R - w.length) = 2 * p + 2 * R := by omega
    rw [h5] at h4
    rw [hC]; exact_mod_cast h2.trans (h3.trans h4)
  have hCnn : 0 ≤ C := Nat.cast_nonneg _
  have hent : ∀ u v : B, (M ^ (2 * p)) u v ≤ C := by
    intro u v
    have := entry_sq_le M hM p u v
    have hu := hdiag u
    have hv := hdiag v
    have hu0 : 0 ≤ (M ^ (2 * p)) u u := by
      rw [adjMatrix_pow_apply_eq_card_walk]; exact Nat.cast_nonneg _
    have hv0 : 0 ≤ (M ^ (2 * p)) v v := by
      rw [adjMatrix_pow_apply_eq_card_walk]; exact Nat.cast_nonneg _
    have : ((M ^ (2 * p)) u v) ^ 2 ≤ C ^ 2 := this.trans (by nlinarith)
    exact abs_le_of_sq_le_sq' this hCnn |>.2
  have hup : b (2 * p) ≤ (∑ u ∈ B, f u) ^ 2 * C := by
    have hx : ∀ u, 0 ≤ x u := fun u => hf u
    calc b (2 * p) = ∑ u, x u * ∑ v, (M ^ (2 * p)) u v * x v := rfl
      _ ≤ ∑ u, x u * ∑ v, C * x v := by
          refine Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left ?_ (hx u)
          exact Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_right (hent u v) (hx v)
      _ = (∑ u, x u) ^ 2 * C := by
          rw [sq, Finset.sum_mul, Finset.sum_mul]
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [← Finset.mul_sum]; ring
      _ = (∑ u ∈ B, f u) ^ 2 * C := by rw [Finset.sum_coe_sort B f]
  exact hlow.trans hup

end DerandSq.Dev.T47C1
end

section
set_option autoImplicit false

/-! Part C2, list level: shells of the component of the root of `X`, masses, inner sums, and the
vanishing of `W` across components of `H`. -/

namespace DerandSq.Dev.T47C2
open SimpleGraph DerandSq DerandSq.Dev.T47 DerandSq.Dev.T47Word DerandSq.Dev.T47B

variable {d : ℕ}

/-- head with default `i0` -/
def hd (i0 : Fin d) : List (Fin d) → Fin d
  | [] => i0
  | x :: _ => x

/-- the reversed words of the component of the root of `X` -/
def Good (i0 : Fin d) (L : List (Fin d)) : Prop := (L ++ [i0]).IsChain (· ≠ ·)

theorem good_nil (i0 : Fin d) : Good i0 [] := List.isChain_singleton _

theorem good_cons2 (i0 j a : Fin d) (L : List (Fin d)) :
    Good i0 (j :: a :: L) ↔ j ≠ a ∧ a ≠ hd i0 L ∧ Good i0 L := by
  unfold Good
  simp only [List.cons_append, List.isChain_cons_cons]
  cases L with
  | nil => simp [hd]
  | cons x L => simp [hd, List.isChain_cons_cons]

theorem good_red (i0 : Fin d) (L : List (Fin d)) (h : Good i0 L) : Red L :=
  (List.isChain_append.1 h).1

theorem not_good_end (i0 x : Fin d) : ¬ Good i0 [x, i0] := by
  intro h
  unfold Good at h
  simp [List.isChain_cons_cons] at h

/-- shells: `S t` = good lists of length `2t` -/
def S (i0 : Fin d) : ℕ → Finset (List (Fin d))
  | 0 => {[]}
  | t + 1 => (((S i0 t) ×ˢ (Finset.univ ×ˢ Finset.univ)).filter
      (fun x : List (Fin d) × Fin d × Fin d => x.2.1 ≠ hd i0 x.1 ∧ x.2.2 ≠ x.2.1)).image
      (fun x => x.2.2 :: x.2.1 :: x.1)

theorem mem_S (i0 : Fin d) (t : ℕ) (L : List (Fin d)) :
    L ∈ S i0 t ↔ L.length = 2 * t ∧ Good i0 L := by
  induction t generalizing L with
  | zero =>
    simp only [S, Finset.mem_singleton, mul_zero, List.length_eq_zero_iff]
    constructor
    · rintro rfl; exact ⟨rfl, good_nil i0⟩
    · exact fun h => h.1
  | succ t ih =>
    simp only [S, Finset.mem_image, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
      and_true, Prod.exists, ih]
    constructor
    · rintro ⟨L', a, j, ⟨⟨hl, hg⟩, ha, hj⟩, rfl⟩
      refine ⟨by simp [hl]; ring, (good_cons2 i0 j a L').2 ⟨hj, ha, hg⟩⟩
    · rintro ⟨hl, hg⟩
      match L, hl, hg with
      | j :: a :: L', hl, hg =>
        obtain ⟨hj, ha, hg'⟩ := (good_cons2 i0 j a L').1 hg
        refine ⟨L', a, j, ⟨⟨?_, hg'⟩, ha, hj⟩, rfl⟩
        simp at hl; omega

/-- the ball: shells `0..n` -/
def BL (i0 : Fin d) (n : ℕ) : Finset (List (Fin d)) :=
  (Finset.range (n + 1)).biUnion (S i0)

theorem mem_BL (i0 : Fin d) (n : ℕ) (L : List (Fin d)) :
    L ∈ BL i0 n ↔ ∃ t, t ≤ n ∧ L.length = 2 * t ∧ Good i0 L := by
  simp only [BL, Finset.mem_biUnion, Finset.mem_range, mem_S]
  constructor
  · rintro ⟨t, ht, h⟩; exact ⟨t, by omega, h⟩
  · rintro ⟨t, ht, h⟩; exact ⟨t, by omega, h⟩

theorem S_disj (i0 : Fin d) (n : ℕ) :
    ((Finset.range (n + 1) : Finset ℕ) : Set ℕ).PairwiseDisjoint (S i0) := by
  intro t _ t' _ htt'
  rw [Function.onFun, Finset.disjoint_left]
  intro L h1 h2
  rw [mem_S] at h1 h2
  exact htt' (by omega)

theorem sum_BL (i0 : Fin d) (n : ℕ) (g : List (Fin d) → ℝ) :
    ∑ L ∈ BL i0 n, g L = ∑ t ∈ Finset.range (n + 1), ∑ L ∈ S i0 t, g L :=
  Finset.sum_biUnion (S_disj i0 n)

/-! Masses. -/

theorem shell_inv {H : SimpleGraph (Fin d)} [DecidableRel H.Adj] (hd3 : 3 ≤ d) (D : WData H)
    (a : Fin d) :
    ∑ b ∈ Finset.univ.filter (fun b => b ≠ a), D.W a b ^ 2 = 1 / ((d : ℝ) - 1) := by
  have h := D.shell a
  have hd1 : (d : ℝ) - 1 ≠ 0 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd3
    linarith
  field_simp
  linarith

theorem mass_succ {H : SimpleGraph (Fin d)} [DecidableRel H.Adj] (hd3 : 3 ≤ d) (D : WData H)
    (i0 : Fin d) (t : ℕ) :
    ∑ L ∈ S i0 (t + 1), Fw D.W L ^ 2 = ∑ L ∈ S i0 t, Fw D.W L ^ 2 := by
  rw [S, Finset.sum_image (fun x _ y _ e => by
    simp only [List.cons.injEq] at e; exact Prod.ext e.2.2 (Prod.ext e.2.1 e.1)),
    Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun L _ => ?_
  rw [Finset.sum_product]
  simp only [Fw_cons2, ite_and]
  have hd1 : (d : ℝ) - 1 ≠ 0 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd3
    linarith
  have : ∀ a : Fin d, (∑ j : Fin d, if a ≠ hd i0 L then (if j ≠ a then
      (D.W a j * Fw D.W L) ^ 2 else 0) else 0) =
      if a ≠ hd i0 L then Fw D.W L ^ 2 / ((d : ℝ) - 1) else 0 := by
    intro a
    split_ifs with ha
    · rw [← Finset.sum_filter]
      simp only [mul_pow]
      rw [← Finset.sum_mul, shell_inv hd3 D a]
      ring
    · simp
  simp only [this]
  rw [← Finset.sum_filter, Finset.sum_const, Finset.filter_ne', nsmul_eq_mul, card_erase_real]
  field_simp

theorem mass {H : SimpleGraph (Fin d)} [DecidableRel H.Adj] (hd3 : 3 ≤ d) (D : WData H)
    (i0 : Fin d) (t : ℕ) : ∑ L ∈ S i0 t, Fw D.W L ^ 2 = 1 := by
  induction t with
  | zero => simp [S]
  | succ t ih => rw [mass_succ hd3 D, ih]

/-! The inner sums. -/

/-- the coefficient of shell `t` in the ball of radius `n` -/
noncomputable def cf {H : SimpleGraph (Fin d)} [DecidableRel H.Adj] (D : WData H) (n t : ℕ) : ℝ :=
  (if t = 0 then 0 else D.μ) + (if t < n then ((d : ℝ) - 1) * D.K else 0)

theorem inner_list {H : SimpleGraph (Fin d)} [DecidableRel H.Adj] (hd3 : 3 ≤ d) (D : WData H)
    (i0 : Fin d) (n t : ℕ) (ht : t ≤ n) (L : List (Fin d)) (hL : L ∈ S i0 t) :
    cf D n t * Fw D.W L ≤ ∑ p ∈ edges H,
      if tog p.2 (tog p.1 L) ∈ BL i0 n then Fw D.W (tog p.2 (tog p.1 L)) else 0 := by
  rw [mem_S] at hL
  obtain ⟨hl, hg⟩ := hL
  have hnn : ∀ L', 0 ≤ Fw D.W L' := Fw_nonneg D.W D.W_nonneg
  have hd1 : (0 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd3
    linarith
  rw [sum_edges]
  match L, hl, hg with
  | [], hl, _ =>
    have ht0 : t = 0 := by simp at hl; omega
    subst ht0
    simp only [cf, if_true, zero_add, Fw_nil, mul_one]
    split_ifs with hn
    · rw [← card_erase_real i0, ← nsmul_eq_mul, ← Finset.sum_const]
      refine le_trans (le_of_eq ?_) (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ (Finset.univ.erase i0)) fun a _ _ =>
          Finset.sum_nonneg fun b _ => by split_ifs <;> simp [hnn])
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [← D.diag a]
      refine Finset.sum_congr rfl fun b hb => ?_
      have hab : a ≠ b := (Finset.mem_filter.1 hb).2.ne
      have hai : a ≠ i0 := Finset.ne_of_mem_erase ha
      simp only [tog_nil, tog_cons_ne _ _ _ hab]
      rw [if_pos]
      · simp
      · rw [mem_BL]
        exact ⟨1, by omega, by simp, (good_cons2 i0 b a []).2 ⟨Ne.symm hab, hai, good_nil i0⟩⟩
    · exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by
        split_ifs <;> simp [hnn]
  | [_], hl, _ => simp at hl; omega
  | j :: i :: L', hl, hg =>
    obtain ⟨hji, hi, hg'⟩ := (good_cons2 i0 j i L').1 hg
    have ht1 : t ≠ 0 := by simp at hl; omega
    have hl' : L'.length = 2 * (t - 1) := by simp at hl; omega
    have hj : ∑ b ∈ Finset.univ.filter (fun b => H.Adj j b),
        (if tog (j, b).2 (tog (j, b).1 (j :: i :: L')) ∈ BL i0 n then
          Fw D.W (tog (j, b).2 (tog (j, b).1 (j :: i :: L'))) else 0) =
          D.μ * Fw D.W (j :: i :: L') := by
      rw [Fw_cons2, ← mul_assoc, ← D.eig i j hji, Finset.sum_mul]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [tog_cons_self]
      by_cases hib : i = b
      · subst hib
        rw [tog_cons_self, if_pos, D.W_self, one_mul]
        rw [mem_BL]; exact ⟨t - 1, by omega, hl', hg'⟩
      · rw [tog_cons_ne _ _ _ hib, if_pos, Fw_cons2]
        rw [mem_BL]
        exact ⟨t, ht, by simp [hl'] at hl ⊢; omega, (good_cons2 i0 b i L').2 ⟨Ne.symm hib, hi, hg'⟩⟩
    have hrest : (if t < n then ((d : ℝ) - 1) * D.K else 0) * Fw D.W (j :: i :: L') ≤
        ∑ a ∈ Finset.univ.erase j, ∑ b ∈ Finset.univ.filter (fun b => H.Adj a b),
        (if tog (a, b).2 (tog (a, b).1 (j :: i :: L')) ∈ BL i0 n then
          Fw D.W (tog (a, b).2 (tog (a, b).1 (j :: i :: L'))) else 0) := by
      split_ifs with htn
      · rw [← card_erase_real j, ← nsmul_eq_mul, ← Finset.sum_const, Finset.sum_mul]
        refine le_of_eq (Finset.sum_congr rfl fun a ha => ?_)
        have hja : j ≠ a := Ne.symm (Finset.ne_of_mem_erase ha)
        rw [← D.diag a, Finset.sum_mul]
        refine Finset.sum_congr rfl fun b hb => ?_
        have hab : a ≠ b := (Finset.mem_filter.1 hb).2.ne
        simp only [tog_cons_ne _ _ _ hja, tog_cons_ne _ _ _ hab]
        rw [if_pos]
        · simp only [Fw_cons2]
        · rw [mem_BL]
          refine ⟨t + 1, htn, by simp at hl ⊢; omega, ?_⟩
          exact (good_cons2 i0 b a _).2 ⟨Ne.symm hab, Ne.symm hja, hg⟩
      · rw [zero_mul]
        exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by
          split_ifs <;> simp [hnn]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), hj]
    simp only [cf, if_neg ht1, add_mul]
    linarith

/-! `W` vanishes across components of `H`. -/

theorem K_lt {H : SimpleGraph (Fin d)} [DecidableRel H.Adj] (hd3 : 3 ≤ d) (D : WData H) :
    D.K < D.μ := by
  rcases lt_or_eq_of_le D.K_le with h | h
  · exact h
  exfalso
  set a : Fin d := ⟨0, by omega⟩
  have hμ := D.μ_pos
  have hb1 : ∀ b ∈ Finset.univ.filter (fun b => H.Adj a b), 1 ≤ D.μ * D.W a b := by
    intro b hb
    have hab : H.Adj a b := (Finset.mem_filter.1 hb).2
    rw [← D.eig a b hab.ne.symm, ← D.W_self a]
    exact Finset.single_le_sum (f := fun c => D.W a c) (fun c _ => D.W_nonneg _ _)
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, hab.symm⟩)
  have h2 : D.μ ≤ D.μ * ∑ b ∈ Finset.univ.filter (fun b => H.Adj a b), D.W a b ^ 2 := by
    calc D.μ = ∑ b ∈ Finset.univ.filter (fun b => H.Adj a b), D.W a b := by rw [D.diag a, h]
      _ ≤ ∑ b ∈ Finset.univ.filter (fun b => H.Adj a b), D.μ * D.W a b ^ 2 :=
          Finset.sum_le_sum fun b hb => by
            have h1 := hb1 b hb
            nlinarith [D.W_nonneg a b]
      _ = _ := (Finset.mul_sum _ _ _).symm
  have h3 : 1 ≤ ∑ b ∈ Finset.univ.filter (fun b => H.Adj a b), D.W a b ^ 2 := by
    by_contra hc; push Not at hc; nlinarith
  have h4 : ∑ b ∈ Finset.univ.filter (fun b => H.Adj a b), D.W a b ^ 2 ≤
      ∑ b ∈ Finset.univ.filter (fun b => b ≠ a), D.W a b ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (fun b hb => Finset.mem_filter.2
      ⟨Finset.mem_univ _, ((Finset.mem_filter.1 hb).2.ne).symm⟩) fun _ _ _ => sq_nonneg _
  have h5 := D.shell a
  have : (3 : ℝ) ≤ d := by exact_mod_cast hd3
  nlinarith

theorem W_zero {H : SimpleGraph (Fin d)} [DecidableRel H.Adj] (hd3 : 3 ≤ d) (D : WData H)
    (a a' : Fin d) (hr : ¬ H.Reachable a a') : D.W a a' = 0 := by
  classical
  set C := Finset.univ.filter (fun j => H.Reachable a' j)
  have hC : ∀ j ∈ C, ∀ b, H.Adj j b → b ∈ C := fun j hj b hjb =>
    Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hj).2.trans hjb.reachable⟩
  have ha : ∀ j ∈ C, j ≠ a := fun j hj e => hr (e ▸ (Finset.mem_filter.1 hj).2).symm
  have hsw : ∀ (g : Fin d → Fin d → ℝ) (j : Fin d), j ∈ C →
      ∑ b ∈ Finset.univ.filter (fun b => H.Adj j b), g j b =
        ∑ b ∈ C, if H.Adj j b then g j b else 0 := by
    intro g j hj
    rw [Finset.sum_filter]
    refine (Finset.sum_subset (Finset.subset_univ C) fun b _ hb => ?_).symm
    rw [if_neg]; exact fun h => hb (hC j hj b h)
  have e1 : ∑ j ∈ C, ∑ b ∈ Finset.univ.filter (fun b => H.Adj j b), D.W a j * D.W a' b =
      ∑ j ∈ C, D.W a j * (if j = a' then D.K else D.μ * D.W a' j) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.mul_sum]
    split_ifs with h
    · subst h; rw [D.diag]
    · rw [D.eig a' j h]
  have e2 : ∑ j ∈ C, ∑ b ∈ Finset.univ.filter (fun b => H.Adj j b), D.W a j * D.W a' b =
      ∑ b ∈ C, D.W a' b * (D.μ * D.W a b) := by
    rw [Finset.sum_congr rfl fun j hj => hsw (fun j b => D.W a j * D.W a' b) j hj,
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [← D.eig a b (ha b hb), Finset.mul_sum, hsw (fun x y => D.W a' x * D.W a y) b hb]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [H.adj_comm j b]
    split_ifs <;> ring
  have ha' : a' ∈ C := Finset.mem_filter.2 ⟨Finset.mem_univ _, Reachable.refl _⟩
  rw [e1, ← Finset.add_sum_erase _ _ ha', ← Finset.add_sum_erase _ _ ha', if_pos rfl] at e2
  have e3 : ∑ j ∈ C.erase a', D.W a j * (if j = a' then D.K else D.μ * D.W a' j) =
      ∑ j ∈ C.erase a', D.W a' j * (D.μ * D.W a j) :=
    Finset.sum_congr rfl fun j hj => by rw [if_neg (Finset.ne_of_mem_erase hj)]; ring
  rw [e3, D.W_self] at e2
  have hK := K_lt hd3 D
  have : D.W a a' * (D.μ - D.K) = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h
  · exact h
  · exact absurd h (by linarith)

end DerandSq.Dev.T47C2
end

section
set_option autoImplicit false

namespace DerandSq.Dev.T47C2
open SimpleGraph DerandSq DerandSq.Dev.T47 DerandSq.Dev.T47Word DerandSq.Dev.T47B

variable {d : ℕ}

theorem mGen_mul_self_assoc (i : Fin d) (z : Gam d) : mGen i * (mGen i * z) = z := by
  rw [← mul_assoc, mGen_mul_self, one_mul]

/-- edges between good words are not deleted -/
theorem notdel (H : SimpleGraph (Fin d)) (i0 : Fin d) (u v : Gam d) (hu : Good i0 (word u))
    (hv : Good i0 (word v)) (h : (dsTree H).Adj u v) : (prunedX H i0).Adj u v := by
  by_contra hX
  obtain ⟨x, ⟨h1, _⟩ | ⟨h1, _⟩⟩ := deleted_word i0 H u v h hX
  · rw [h1] at hu; exact not_good_end i0 x hu
  · rw [h1] at hv; exact not_good_end i0 x hv

theorem good_of_BL (i0 : Fin d) (n : ℕ) (L : List (Fin d)) (h : L ∈ BL i0 n) : Good i0 L := by
  obtain ⟨_, _, _, h⟩ := (mem_BL i0 n L).1 h; exact h

theorem mem_B0 (i0 : Fin d) (n : ℕ) (v : Gam d) :
    v ∈ (BL i0 n).image unword ↔ word v ∈ BL i0 n := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨L, hL, rfl⟩
    rwa [word_unword L (good_red i0 L (good_of_BL i0 n L hL))]
  · intro h; exact ⟨word v, h, unword_word v⟩

theorem tog_good (i0 a : Fin d) (L : List (Fin d)) (h : a ≠ hd i0 L) : tog a L = a :: L := by
  cases L with
  | nil => rfl
  | cons y L => exact tog_cons_ne _ _ _ (fun e => h (by simp [hd, e]))

theorem reach {H : SimpleGraph (Fin d)} [DecidableRel H.Adj] (hd3 : 3 ≤ d) (D : WData H)
    (i0 : Fin d) : ∀ (t : ℕ) (L : List (Fin d)), L ∈ S i0 t → Fw D.W L ≠ 0 →
      ∃ w : (prunedX H i0).Walk 1 (unword L), w.length ≤ t * d := by
  intro t
  induction t with
  | zero =>
    intro L hL _
    rw [mem_S] at hL
    have : L = [] := List.length_eq_zero_iff.1 (by simpa using hL.1)
    subst this
    exact ⟨Walk.nil, by simp⟩
  | succ t ih =>
    intro L hL hF
    rw [mem_S] at hL
    obtain ⟨hl, hg⟩ := hL
    match L, hl, hg, hF with
    | j :: a :: L', hl, hg, hF =>
      obtain ⟨hja, ha, hg'⟩ := (good_cons2 i0 j a L').1 hg
      rw [Fw_cons2] at hF
      obtain ⟨hW, hF'⟩ := mul_ne_zero_iff.1 hF
      obtain ⟨w1, hw1⟩ := ih L' ((mem_S i0 t L').2 ⟨by simp at hl; omega, hg'⟩) hF'
      have hr : H.Reachable a j := by
        by_contra hc; exact hW (W_zero hd3 D a j hc)
      let p := hr.some.bypass
      have hp : p.length < d := by
        have := (hr.some.bypass_isPath).length_lt
        simpa using this
      have hgood : ∀ x, Good i0 (word (unword L' * mGen a * mGen x)) := by
        intro x
        rw [word_mul2, word_unword L' (good_red i0 L' hg'), tog_good i0 a L' ha]
        by_cases hax : a = x
        · subst hax; rw [tog_cons_self]; exact hg'
        · rw [tog_cons_ne _ _ _ hax]
          exact (good_cons2 i0 x a L').2 ⟨Ne.symm hax, ha, hg'⟩
      let φ : H →g prunedX H i0 :=
        { toFun := fun x => unword L' * mGen a * mGen x
          map_rel' := fun {x y} hxy => by
            refine notdel H i0 _ _ (hgood x) (hgood y) ((dsTree_adj_iff H _ _).2 ⟨x, y, hxy, ?_⟩)
            simp only [mul_assoc, mGen_mul_self_assoc] }
      have h1 : φ a = unword L' := by
        change unword L' * mGen a * mGen a = _
        rw [mul_assoc, mGen_mul_self, mul_one]
      have h2 : φ j = unword (j :: a :: L') := by
        rw [unword_cons, unword_cons]; rfl
      refine ⟨w1.append ((p.map φ).copy h1 h2), ?_⟩
      rw [Walk.length_append, Walk.length_copy, Walk.length_map]
      nlinarith

theorem sum_cf {H : SimpleGraph (Fin d)} [DecidableRel H.Adj] (D : WData H) (n : ℕ) :
    ∑ t ∈ Finset.range (n + 1), cf D n t = n * (D.μ + ((d : ℝ) - 1) * D.K) := by
  have a1 : ∑ t ∈ Finset.range (n + 1), (if t = 0 then (0 : ℝ) else D.μ) = n * D.μ := by
    rw [Finset.sum_range_succ']; simp
  have a2 : ∑ t ∈ Finset.range (n + 1), (if t < n then ((d : ℝ) - 1) * D.K else 0) =
      n * (((d : ℝ) - 1) * D.K) := by
    rw [Finset.sum_range_succ, Finset.sum_ite_of_true (fun t ht => Finset.mem_range.1 ht)]
    simp
  simp only [cf, Finset.sum_add_distrib, a1, a2]
  ring

open Classical in
/-- Part C2: the truncated test function on `X`. -/
theorem test_fn {d : ℕ} (hd : 3 ≤ d) (H : SimpleGraph (Fin d)) [DecidableRel H.Adj]
    (D : WData H) (i0 : Fin d) (n : ℕ) :
    ∃ (B : Finset (Gam d)) (f : Gam d → ℝ) (R : ℕ), (∀ v, 0 ≤ f v) ∧
      (∀ u ∈ B, ∃ w : (prunedX H i0).Walk 1 u, w.length ≤ R) ∧
      0 < ∑ u ∈ B, f u ^ 2 ∧
      (LambdaH d H * n / (n + 1)) * ∑ u ∈ B, f u ^ 2 ≤
        ∑ u ∈ B, ∑ v ∈ B, if (prunedX H i0).Adj u v then f u * f v else 0 := by
  set B0 := (BL i0 n).image unword with hB0
  set f : Gam d → ℝ := fun g => Fw D.W (word g) with hf
  have hinj : Set.InjOn unword (BL i0 n : Set (List (Fin d))) := fun L hL L' hL' e => by
    rw [← word_unword L (good_red i0 L (good_of_BL i0 n L hL)),
      ← word_unword L' (good_red i0 L' (good_of_BL i0 n L' hL')), e]
  have hwu : ∀ L ∈ BL i0 n, word (unword L) = L := fun L hL =>
    word_unword L (good_red i0 L (good_of_BL i0 n L hL))
  -- masses
  have hsq : ∑ u ∈ B0, f u ^ 2 = n + 1 := by
    rw [hB0, Finset.sum_image hinj]
    have e : ∀ L ∈ BL i0 n, f (unword L) ^ 2 = Fw D.W L ^ 2 := fun L hL => by
      simp only [hf, hwu L hL]
    rw [Finset.sum_congr rfl e, sum_BL, Finset.sum_congr rfl (fun t _ => mass hd D i0 t)]
    simp
  -- the double sum
  set G : List (Fin d) → ℝ := fun L => ∑ p ∈ edges H, if tog p.2 (tog p.1 L) ∈ BL i0 n then
    Fw D.W (tog p.2 (tog p.1 L)) else 0 with hG
  have hdbl : n * LambdaH d H ≤
      ∑ u ∈ B0, ∑ v ∈ B0, if (prunedX H i0).Adj u v then f u * f v else 0 := by
    have hrow : ∀ u ∈ B0, (∑ v ∈ B0, if (prunedX H i0).Adj u v then f u * f v else 0) =
        Fw D.W (word u) * G (word u) := by
      intro u hu
      have hgu := good_of_BL i0 n _ ((mem_B0 i0 n u).1 hu)
      have e1 : ∀ v ∈ B0, (if (prunedX H i0).Adj u v then f u * f v else 0) =
          f u * (if (dsTree H).Adj u v then f v else 0) := by
        intro v hv
        have hgv := good_of_BL i0 n _ ((mem_B0 i0 n v).1 hv)
        by_cases hT : (dsTree H).Adj u v
        · rw [if_pos (notdel H i0 u v hgu hgv hT), if_pos hT]
        · rw [if_neg (fun h => hT (X_le H i0 h)), if_neg hT, mul_zero]
      rw [Finset.sum_congr rfl e1, ← Finset.mul_sum, sum_adj_eq]
      congr 1
      refine Finset.sum_congr rfl fun p _ => ?_
      simp only [hf, hB0, mem_B0, word_mul2]
    rw [Finset.sum_congr rfl hrow, hB0, Finset.sum_image hinj]
    rw [Finset.sum_congr rfl (fun L hL => by rw [hwu L hL] :
      ∀ L ∈ BL i0 n, Fw D.W (word (unword L)) * G (word (unword L)) = Fw D.W L * G L)]
    rw [sum_BL, ← D.lam, ← sum_cf D n]
    refine Finset.sum_le_sum fun t ht => ?_
    rw [show cf D n t = cf D n t * ∑ L ∈ S i0 t, Fw D.W L ^ 2 by rw [mass hd D i0 t, mul_one],
      Finset.mul_sum]
    refine Finset.sum_le_sum fun L hL => ?_
    have := inner_list hd D i0 n t (by simpa [Nat.lt_succ_iff] using ht) L hL
    have h0 := Fw_nonneg D.W D.W_nonneg L
    nlinarith
  -- restrict to the support of `f`
  set B := B0.filter (fun u => f u ≠ 0) with hB
  have hsqB : ∑ u ∈ B, f u ^ 2 = ∑ u ∈ B0, f u ^ 2 :=
    Finset.sum_filter_of_ne fun u _ h => by intro h'; exact h (by rw [h']; ring)
  have hdblB : (∑ u ∈ B, ∑ v ∈ B, if (prunedX H i0).Adj u v then f u * f v else 0) =
      ∑ u ∈ B0, ∑ v ∈ B0, if (prunedX H i0).Adj u v then f u * f v else 0 := by
    have : ∀ u, (∑ v ∈ B, if (prunedX H i0).Adj u v then f u * f v else 0) =
        ∑ v ∈ B0, if (prunedX H i0).Adj u v then f u * f v else 0 := fun u =>
      Finset.sum_filter_of_ne fun v _ h => by
        intro h'; apply h; simp [h']
    simp only [this]
    exact Finset.sum_filter_of_ne fun u _ h => by
      intro h'; apply h; simp [h']
  refine ⟨B, f, n * d, fun v => Fw_nonneg D.W D.W_nonneg _, ?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨hu0, hfu⟩ := Finset.mem_filter.1 hu
    obtain ⟨t, htn, hl, hg⟩ := (mem_BL i0 n _).1 ((mem_B0 i0 n u).1 hu0)
    obtain ⟨w, hw⟩ := reach hd D i0 t (word u) ((mem_S i0 t _).2 ⟨hl, hg⟩) hfu
    exact ⟨w.copy rfl (unword_word u),
      by rw [Walk.length_copy]; exact hw.trans (Nat.mul_le_mul_right d htn)⟩
  · rw [hsqB, hsq]; positivity
  · rw [hsqB, hsq, hdblB]
    have : LambdaH d H * n / (n + 1) * ((n : ℝ) + 1) = n * LambdaH d H := by
      field_simp
    linarith

/-- Part C2: the root of `X` has a neighbour. -/
theorem X_root_nbr {d k : ℕ} (hd : 3 ≤ d) (hk : 1 ≤ k) (H : SimpleGraph (Fin d))
    [DecidableRel H.Adj] (hH : H.IsRegularOfDegree k) (i0 : Fin d) :
    ∃ v, (prunedX H i0).Adj 1 v := by
  obtain ⟨a, ha⟩ : ∃ a : Fin d, a ≠ i0 := by
    by_cases h : i0 = ⟨0, by omega⟩
    · exact ⟨⟨1, by omega⟩, by rw [h]; simp [Fin.ext_iff]⟩
    · exact ⟨⟨0, by omega⟩, Ne.symm h⟩
  obtain ⟨b, hab⟩ : ∃ b, H.Adj a b := by
    have := hH a
    rw [← H.card_neighborFinset_eq_degree] at this
    obtain ⟨b, hb⟩ := Finset.card_pos.1 (by omega : 0 < (H.neighborFinset a).card)
    exact ⟨b, (H.mem_neighborFinset a b).1 hb⟩
  refine ⟨1 * mGen a * mGen b, notdel H i0 _ _ (by simpa using good_nil i0) ?_
    ((dsTree_adj_iff H _ _).2 ⟨a, b, hab, rfl⟩)⟩
  rw [word_mul2, word_one, tog_nil, tog_cons_ne _ _ _ hab.ne]
  exact (good_cons2 i0 b a []).2 ⟨hab.ne.symm, ha, good_nil i0⟩

end DerandSq.Dev.T47C2
end

section
set_option autoImplicit false

namespace DerandSq

open DerandSq.Dev.T47 in
theorem chk_theorem_4_7 {d k : ℕ} (hd : 3 ≤ d) (hk : 1 ≤ k) (H : SimpleGraph (Fin d))
    [DecidableRel H.Adj] (hH : H.IsRegularOfDegree k) (hvt : IsVertexTransitive H) (i0 : Fin d) :
    Filter.Tendsto
      (fun p : ℕ => (closedWalks (prunedX H i0) 1 (2 * p) : ℝ) ^ ((1 : ℝ) / (2 * p)))
      Filter.atTop (nhds (LambdaH d H)) := by
  obtain ⟨D⟩ := DerandSq.Dev.T47A.wdata_exists hd hk H hH hvt
  set L := LambdaH d H with hLdef
  have hK : 0 ≤ D.K := by
    rw [← D.diag ⟨0, by omega⟩]
    exact Finset.sum_nonneg (fun b _ => D.W_nonneg _ b)
  have hd1 : (0 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hL : 0 < L := by
    rw [hLdef, ← D.lam]
    have := D.μ_pos
    nlinarith
  set c : ℕ → ℝ := fun m => (closedWalks (prunedX H i0) 1 (2 * m) : ℝ) with hc
  have hc0 : ∀ m, 0 ≤ c m := fun m => Nat.cast_nonneg _
  have hup : ∀ m, c m ≤ L ^ (2 * m) := by
    intro m
    have h1 : closedWalks (prunedX H i0) 1 (2 * m) ≤ closedWalks (dsTree H) 1 (2 * m) :=
      DerandSq.Dev.C48a.cw_le_of_hom (SimpleGraph.Hom.ofLE (X_le H i0)) Function.injective_id
        (T_fin H) 1 _
    have h2 := DerandSq.Dev.T47B.upper_T hd H D (2 * m)
    calc c m ≤ (closedWalks (dsTree H) 1 (2 * m) : ℝ) := by
          simp only [hc]; exact_mod_cast h1
      _ ≤ L ^ (2 * m) := h2
  -- `x = (x ^ (2m)) ^ (1/(2m))`
  have hroot : ∀ (x : ℝ), 0 ≤ x → ∀ m : ℕ, 1 ≤ m →
      (x ^ (2 * m)) ^ ((1 : ℝ) / (2 * (m : ℝ))) = x := by
    intro x hx m hm
    have h := Real.pow_rpow_inv_natCast hx (n := 2 * m) (by omega)
    rw [show (1 : ℝ) / (2 * (m : ℝ)) = ((2 * m : ℕ) : ℝ)⁻¹ by push_cast; ring]
    exact h
  rw [tendsto_order]
  constructor
  · intro b hb
    by_cases hb0 : b < 0
    · exact Filter.Eventually.of_forall (fun m => lt_of_lt_of_le hb0 (by
        show (0 : ℝ) ≤ (c m) ^ ((1 : ℝ) / (2 * (m : ℝ)))
        exact Real.rpow_nonneg (hc0 m) _))
    replace hb0 : 0 ≤ b := not_lt.mp hb0
    -- choose `n` with `b < L n / (n + 1)`
    obtain ⟨n, hn⟩ : ∃ n : ℕ, L / (L - b) ≤ n := exists_nat_ge _
    have hLb : 0 < L - b := by linarith
    set r : ℝ := L * n / (n + 1) with hr
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hbr : b < r := by
      rw [hr, lt_div_iff₀ hn1]
      have : L ≤ n * (L - b) := by rwa [div_le_iff₀ hLb] at hn
      nlinarith
    have hr0 : 0 < r := lt_of_le_of_lt hb0 hbr
    obtain ⟨B, f, R, hf, hreach, hs, hQ⟩ := DerandSq.Dev.T47C2.test_fn hd H D i0 n
    have key := fun p => DerandSq.Dev.T47C1.rayleigh_walks (prunedX H i0) (X_fin H i0) 1
      (DerandSq.Dev.T47C2.X_root_nbr hd hk H hH i0) B f hf R hreach r hr0.le hQ p
    set s := ∑ u ∈ B, f u ^ 2
    set T := ∑ u ∈ B, f u
    have hT : 0 < T ^ 2 := by
      rcases (sq_nonneg T).lt_or_eq with h | h
      · exact h
      · exfalso
        have := key 0
        rw [← h] at this
        simp at this
        linarith
    set C : ℝ := s / T ^ 2 / r ^ (2 * R) with hC
    have hCpos : 0 < C := by positivity
    have hlow : ∀ m, R ≤ m → C * r ^ (2 * m) ≤ c m := by
      intro m hm
      have h := key (m - R)
      have he : 2 * (m - R) + 2 * R = 2 * m := by omega
      rw [he] at h
      have hrr : r ^ (2 * m) = r ^ (2 * (m - R)) * r ^ (2 * R) := by
        rw [← pow_add]; congr 1; omega
      rw [hC, hrr]
      have hpos : 0 < r ^ (2 * R) := by positivity
      rw [div_div, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      calc s * (r ^ (2 * (m - R)) * r ^ (2 * R)) = s * r ^ (2 * (m - R)) * r ^ (2 * R) := by ring
        _ ≤ T ^ 2 * c m * r ^ (2 * R) := by
            gcongr
        _ = c m * (T ^ 2 * r ^ (2 * R)) := by ring
    have hq0 : 0 ≤ b / r := div_nonneg hb0 hr0.le
    have hq1 : b / r < 1 := by rw [div_lt_one hr0]; exact hbr
    have htend := tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
    have hev := (htend.eventually (gt_mem_nhds hCpos))
    filter_upwards [hev, Filter.eventually_ge_atTop (max R 1)] with m hm hmR
    have hmR' : R ≤ m := le_of_max_le_left hmR
    have hm1 : 1 ≤ m := le_of_max_le_right hmR
    have hpow : (b / r) ^ (2 * m) ≤ (b / r) ^ m :=
      pow_le_pow_of_le_one hq0 hq1.le (by omega)
    have hbm : b ^ (2 * m) < c m := by
      calc b ^ (2 * m) = (b / r) ^ (2 * m) * r ^ (2 * m) := by
            rw [div_pow, div_mul_cancel₀]; positivity
        _ < C * r ^ (2 * m) := by
            apply mul_lt_mul_of_pos_right (lt_of_le_of_lt hpow hm) (by positivity)
        _ ≤ c m := hlow m hmR'
    have := Real.rpow_lt_rpow (by positivity) hbm (by positivity : (0 : ℝ) < 1 / (2 * (m : ℝ)))
    rw [hroot b hb0 m hm1] at this
    exact this
  · intro b hb
    filter_upwards [Filter.eventually_ge_atTop 1] with m hm
    have := Real.rpow_le_rpow (hc0 m) (hup m) (by positivity : (0 : ℝ) ≤ 1 / (2 * (m : ℝ)))
    rw [hroot L hL.le m hm] at this
    exact lt_of_le_of_lt this hb

end DerandSq
end

theorem solution : type_of% @DerandSq.chk_theorem_4_7 := @DerandSq.chk_theorem_4_7
