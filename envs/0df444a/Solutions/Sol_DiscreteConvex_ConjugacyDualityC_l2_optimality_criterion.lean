-- Prove2me | solution 1 for DiscreteConvex.ConjugacyDualityC.l2_optimality_criterion
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T05:51:21.168981+00:00
-- url     : https://prove2.me/submissions/3080a3dd-5e49-4288-862e-146c1852015e

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_IndicatorVec
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_DomZ
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_L2Convex



namespace DiscreteConvex.ConjugacyDualityC
open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option linter.unusedSectionVars false

lemma l2o_toE_add (x y : WithTop ℝ) : ToEReal (x + y) = ToEReal x + ToEReal y := by
  induction x using WithTop.recTopCoe <;> induction y using WithTop.recTopCoe
  · rfl
  · rfl
  · rfl
  · rfl

lemma l2o_trf_iter (g : (V → ℤ) → WithTop ℝ) (r : ℝ)
    (hr : ∀ p : V → ℤ, g (p + 1) = g p + (r : WithTop ℝ)) (z : V → ℤ) (k : ℤ) :
    g (fun v => z v + k) = g z + ((k * r : ℝ) : WithTop ℝ) := by
  induction k using Int.induction_on with
  | zero => simp
  | succ i ih =>
    have : (fun v => z v + ((i:ℤ) + 1)) = (fun v => z v + (i:ℤ)) + 1 := by
      funext v; simp only [Pi.add_apply, Pi.one_apply]; ring
    rw [this, hr, ih, add_assoc, ← WithTop.coe_add]; congr 2; push_cast; ring
  | pred i ih =>
    have hw : (fun v => z v + (-(i:ℤ) - 1)) + 1 = (fun v => z v + -(i:ℤ)) := by
      funext v; simp only [Pi.add_apply, Pi.one_apply]; ring
    have h := hr (fun v => z v + (-(i:ℤ) - 1))
    rw [hw, ih] at h
    have h2 : g z + ((((-(i:ℤ)) : ℤ) * r : ℝ) : WithTop ℝ)
        = (g z + (((((-(i:ℤ) - 1) : ℤ)) * r : ℝ) : WithTop ℝ)) + (r : WithTop ℝ) := by
      rw [add_assoc, ← WithTop.coe_add]; congr 2; push_cast; ring
    rw [h2] at h
    exact ((WithTop.add_right_inj (WithTop.coe_ne_top)).mp h).symm

lemma l2o_sbf_shift (g : (V → ℤ) → WithTop ℝ) (hS : SBF g) (r : ℝ)
    (hr : ∀ p : V → ℤ, g (p + 1) = g p + (r : WithTop ℝ)) (x y : V → ℤ) (k : ℤ) :
    g (fun v => max (x v) (y v - k)) + g (fun v => min (x v) (y v - k) + k) ≤ g x + g y := by
  have h := hS x (fun v => y v - k)
  have e1 : g y = g (fun v => y v - k) + ((k * r : ℝ) : WithTop ℝ) := by
    rw [← l2o_trf_iter g r hr]; congr 1; funext v; ring
  have e2 : g (fun v => min (x v) (y v - k) + k)
      = g (x ⊓ fun v => y v - k) + ((k * r : ℝ) : WithTop ℝ) := by
    rw [← l2o_trf_iter g r hr]; rfl
  have e3 : (x ⊔ fun v => y v - k) = fun v => max (x v) (y v - k) := rfl
  rw [e1, e2, ← e3, ← add_assoc, ← add_assoc]
  exact add_le_add h le_rfl

lemma l2o_bdd (g1 g2 : (V → ℤ) → WithTop ℝ) (hE : ∀ p, InfConvE g1 g2 p ≠ ⊥) (x : V → ℤ) :
    BddBelow {L : WithTop ℝ | ∃ p1 p2 : V → ℤ, x = p1 + p2 ∧ L = g1 p1 + g2 p2} := by
  have h := hE x
  unfold InfConvE at h
  obtain ⟨β, hβ⟩ := WithBot.ne_bot_iff_exists.mp h
  refine ⟨β, ?_⟩
  rintro L ⟨a, b, hx, rfl⟩
  have : sInf {L : EReal | ∃ p1 p2 : V → ℤ, x = p1 + p2 ∧
      L = ToEReal (g1 p1) + ToEReal (g2 p2)} ≤ ToEReal (g1 a) + ToEReal (g2 b) :=
    sInf_le ⟨a, b, hx, rfl⟩
  rw [← l2o_toE_add, ← hβ] at this
  exact WithBot.coe_le_coe.mp this

lemma l2o_lb (g1 g2 : (V → ℤ) → WithTop ℝ) (hE : ∀ p, InfConvE g1 g2 p ≠ ⊥) (x a b : V → ℤ)
    (h : x = a + b) : InfConv g1 g2 x ≤ g1 a + g2 b :=
  csInf_le (l2o_bdd g1 g2 hE x) ⟨a, b, h, rfl⟩

lemma l2o_glb (g1 g2 : (V → ℤ) → WithTop ℝ) (x : V → ℤ) (c : WithTop ℝ)
    (h : ∀ a b : V → ℤ, x = a + b → c ≤ g1 a + g2 b) : c ≤ InfConv g1 g2 x :=
  le_csInf ⟨_, x, 0, by simp, rfl⟩ (by rintro L ⟨a, b, hx, rfl⟩; exact h a b hx)

lemma l2o_approx (g1 g2 : (V → ℤ) → WithTop ℝ) (x : V → ℤ) (m : ℝ)
    (hm : InfConv g1 g2 x = (m : WithTop ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ a b : V → ℤ, x = a + b ∧ g1 a + g2 b < ((m + ε : ℝ) : WithTop ℝ) := by
  have hlt : InfConv g1 g2 x < ((m + ε : ℝ) : WithTop ℝ) := by
    rw [hm]; exact WithTop.coe_lt_coe.mpr (by linarith)
  unfold InfConv at hlt
  have hne : ({L : WithTop ℝ | ∃ p1 p2 : V → ℤ, x = p1 + p2 ∧ L = g1 p1 + g2 p2}).Nonempty :=
    ⟨g1 x + g2 0, x, 0, by simp, rfl⟩
  obtain ⟨L, ⟨a, b, hx, rfl⟩, hL⟩ := exists_lt_of_csInf_lt hne hlt
  exact ⟨a, b, hx, hL⟩

lemma l2o_key (g1 g2 : (V → ℤ) → WithTop ℝ) (h1S : SBF g1) (r1 : ℝ)
    (h1T : ∀ p : V → ℤ, g1 (p + 1) = g1 p + (r1 : WithTop ℝ))
    (h2S : SBF g2) (r2 : ℝ) (h2T : ∀ p : V → ℤ, g2 (p + 1) = g2 p + (r2 : WithTop ℝ))
    (hE : ∀ p, InfConvE g1 g2 p ≠ ⊥) (p : V → ℤ) (m : ℝ)
    (hm : InfConv g1 g2 p = (m : WithTop ℝ))
    (hloc : ∀ Y : Finset V, InfConv g1 g2 p ≤ InfConv g1 g2 (fun v => p v + IndicatorVec Y v)) :
    ∀ N : ℕ, ∀ d : V → ℤ, (∀ v, 0 ≤ d v) → ∑ v, d v ≤ (N : ℤ) → ∀ q1 q2 : V → ℤ,
      (fun v => p v + d v) = q1 + q2 → (m : WithTop ℝ) ≤ g1 q1 + g2 q2 := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IH =>
  intro d hd0 hdN q1 q2 hq
  by_cases hsmall : ∀ v, d v ≤ 1
  · have hY : (fun v => p v + d v) = (fun v => p v + IndicatorVec (Finset.univ.filter (fun v => d v = 1)) v) := by
      funext v; unfold IndicatorVec
      have := hd0 v; have := hsmall v
      by_cases h : d v = 1 <;> simp [h] <;> omega
    rw [← hm]
    refine le_trans (hloc (Finset.univ.filter (fun v => d v = 1))) ?_
    rw [← hY]
    exact l2o_lb g1 g2 hE _ q1 q2 hq
  push_neg at hsmall
  obtain ⟨v0, hv0⟩ := hsmall
  by_contra hcon
  push_neg at hcon
  obtain ⟨φ, hφ⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hcon)
  rw [← hφ] at hcon
  have hφm : φ < m := WithTop.coe_lt_coe.mp hcon
  obtain ⟨a, b, hab, hablt⟩ := l2o_approx g1 g2 p m hm (m - φ) (by linarith)
  obtain ⟨α, hα⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hablt)
  rw [← hα] at hablt
  have hαlt : α < m + (m - φ) := WithTop.coe_lt_coe.mp hablt
  have hqv : ∀ v, p v + d v = q1 v + q2 v := fun v => congrFun hq v
  have hpv : ∀ v, p v = a v + b v := fun v => congrFun hab v
  set k : ℤ := q1 v0 - a v0 - 1 with hk
  set s : V → ℤ := fun v => max (q1 v - a v - k) 0 with hs
  set t : V → ℤ := fun v => min (q2 v - b v + k) 0 with ht
  set e : V → ℤ := fun v => s v + t v with he
  have he0 : ∀ v, 0 ≤ e v := by
    intro v; simp only [he, hs, ht]; have := hqv v; have := hpv v; have := hd0 v; omega
  have hed : ∀ v, e v ≤ d v := by
    intro v; simp only [he, hs, ht]; have := hqv v; have := hpv v; have := hd0 v; omega
  have hev0 : e v0 = 1 := by
    simp only [he, hs, ht, hk]; have := hqv v0; have := hpv v0; omega
  have hN : 1 ≤ N := by
    have : d v0 ≤ ∑ v, d v := Finset.single_le_sum (fun v _ => hd0 v) (Finset.mem_univ v0)
    omega
  have hsum_e : ∑ v, e v ≤ ((N - 1 : ℕ) : ℤ) := by
    have h1 : ∑ v, (d v - e v) ≥ d v0 - e v0 :=
      Finset.single_le_sum (f := fun v => d v - e v) (fun v _ => by have := hed v; omega)
        (Finset.mem_univ v0)
    rw [Finset.sum_sub_distrib] at h1
    push_cast [hN]; omega
  have hsum_de : ∑ v, (d v - e v) ≤ ((N - 1 : ℕ) : ℤ) := by
    have h1 : ∑ v, e v ≥ e v0 :=
      Finset.single_le_sum (f := fun v => e v) (fun v _ => he0 v) (Finset.mem_univ v0)
    rw [Finset.sum_sub_distrib]
    push_cast [hN]; omega
  have IH1 := IH (N - 1) (by omega) e he0 hsum_e (fun v => a v + s v) (fun v => b v + t v)
    (by funext v; simp only [Pi.add_apply, he]; have := hpv v; omega)
  have IH2 := IH (N - 1) (by omega) (fun v => d v - e v) (fun v => by have := hed v; omega)
    hsum_de (fun v => q1 v - s v) (fun v => q2 v - t v)
    (by funext v; simp only [Pi.add_apply, he]; have := hqv v; omega)
  have S1 := l2o_sbf_shift g1 h1S r1 h1T a q1 k
  have S2 := l2o_sbf_shift g2 h2S r2 h2T q2 b k
  have E1 : (fun v => max (a v) (q1 v - k)) = fun v => a v + s v := by
    funext v; simp only [hs]; omega
  have E2 : (fun v => min (a v) (q1 v - k) + k) = fun v => q1 v - s v := by
    funext v; simp only [hs]; omega
  have E3 : (fun v => max (q2 v) (b v - k)) = fun v => q2 v - t v := by
    funext v; simp only [ht]; omega
  have E4 : (fun v => min (q2 v) (b v - k) + k) = fun v => b v + t v := by
    funext v; simp only [ht]; omega
  rw [E1, E2] at S1
  rw [E3, E4] at S2
  have chain : (m : WithTop ℝ) + (m : WithTop ℝ) ≤ (α : WithTop ℝ) + (φ : WithTop ℝ) := by
    calc (m : WithTop ℝ) + (m : WithTop ℝ)
        ≤ (g1 (fun v => a v + s v) + g2 (fun v => b v + t v)) +
          (g1 (fun v => q1 v - s v) + g2 (fun v => q2 v - t v)) := add_le_add IH1 IH2
      _ = (g1 (fun v => a v + s v) + g1 (fun v => q1 v - s v)) +
          (g2 (fun v => q2 v - t v) + g2 (fun v => b v + t v)) := by
            rw [add_add_add_comm, add_comm (g2 (fun v => b v + t v))]
      _ ≤ (g1 a + g1 q1) + (g2 q2 + g2 b) := add_le_add S1 S2
      _ = (g1 a + g2 b) + (g1 q1 + g2 q2) := by
            rw [add_comm (g2 q2), add_add_add_comm]
      _ = (α : WithTop ℝ) + (φ : WithTop ℝ) := by rw [hα, hφ]
  rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe] at chain
  linarith

theorem l2opt_core (g : (V → ℤ) → WithTop ℝ) (hg : L2Convex g) (p : V → ℤ)
    (hp : p ∈ DomZ g) :
    (∀ q, g p ≤ g q) ↔
      ((∀ Y : Finset V, g p ≤ g (fun v => p v + IndicatorVec Y v)) ∧ g p = g (p + 1)) := by
  obtain ⟨g1, g2, ⟨h1S, r1, h1T⟩, ⟨h2S, r2, h2T⟩, hE, rfl⟩ := hg
  have hp' : InfConv g1 g2 p ≠ ⊤ := hp
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hp'
  have hm' : InfConv g1 g2 p = (m : WithTop ℝ) := hm.symm
  -- upper bound at p + 1
  have U : InfConv g1 g2 (p + 1) ≤ ((m + r1 : ℝ) : WithTop ℝ) := by
    have hfor : ∀ ε : ℝ, 0 < ε → InfConv g1 g2 (p + 1) ≤ ((m + r1 + ε : ℝ) : WithTop ℝ) := by
      intro ε hε
      obtain ⟨a, b, hab, hlt⟩ := l2o_approx g1 g2 p m hm' ε hε
      obtain ⟨α, hα⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hlt)
      rw [← hα] at hlt
      have hα' : α < m + ε := WithTop.coe_lt_coe.mp hlt
      have h1 := l2o_lb g1 g2 hE (p + 1) (a + 1) b (by rw [hab]; abel)
      rw [h1T, add_right_comm, ← hα, ← WithTop.coe_add] at h1
      exact h1.trans (WithTop.coe_le_coe.mpr (by linarith))
    obtain ⟨y, hy⟩ := WithTop.ne_top_iff_exists.mp
      (ne_top_of_le_ne_top WithTop.coe_ne_top (hfor 1 one_pos))
    rw [← hy] at hfor ⊢
    refine WithTop.coe_le_coe.mpr (le_of_forall_pos_le_add fun ε hε => ?_)
    have := WithTop.coe_le_coe.mp (hfor ε hε); linarith
  -- lower bound
  have L : ∀ x : V → ℤ, InfConv g1 g2 x + (r1 : WithTop ℝ) ≤ InfConv g1 g2 (x + 1) := by
    intro x
    refine l2o_glb g1 g2 (x + 1) _ (fun a b hab => ?_)
    have h1 := l2o_lb g1 g2 hE x (a - 1) b (by
      have : x = (x + 1) - 1 := by abel
      rw [this, hab]; abel)
    have h2 : g1 a = g1 (a - 1) + (r1 : WithTop ℝ) := by rw [← h1T, sub_add_cancel]
    rw [h2, add_right_comm]
    exact add_le_add h1 le_rfl
  constructor
  · intro hmin
    refine ⟨fun Y => hmin _, ?_⟩
    have hA := L (p - 1)
    rw [sub_add_cancel] at hA
    have hB := hmin (p - 1)
    have hC := hmin (p + 1)
    have hr1a : r1 ≤ 0 := by
      have := (add_le_add hB (le_refl (r1 : WithTop ℝ))).trans hA
      rw [hm', ← WithTop.coe_add, WithTop.coe_le_coe] at this; linarith
    have hr1b : 0 ≤ r1 := by
      have := hC.trans U
      rw [hm', WithTop.coe_le_coe] at this; linarith
    apply le_antisymm hC
    rw [hm']; convert U using 2; linarith
  · rintro ⟨hloc, hper⟩
    have hr1 : r1 = 0 := by
      have hA := L p
      rw [← hper, hm', ← WithTop.coe_add, WithTop.coe_le_coe] at hA
      have hB := U
      rw [← hper, hm', WithTop.coe_le_coe] at hB
      linarith
    have key := l2o_key g1 g2 h1S r1 h1T h2S r2 h2T hE p m hm' hloc
    intro q
    rw [hm']
    refine l2o_glb g1 g2 q _ (fun q1 q2 hq => ?_)
    set c : ℤ := -∑ v, |q v - p v| with hc
    have hcle : ∀ v, c ≤ q v - p v := by
      intro v
      have h1 : |q v - p v| ≤ ∑ w, |q w - p w| :=
        Finset.single_le_sum (f := fun w => |q w - p w|) (fun w _ => abs_nonneg _) (Finset.mem_univ v)
      have h2 := neg_abs_le (q v - p v)
      simp only [hc]; linarith
    have hshift : g1 q1 = g1 (fun v => q1 v - c) := by
      have := l2o_trf_iter g1 r1 h1T (fun v => q1 v - c) c
      rw [hr1, mul_zero, WithTop.coe_zero, add_zero] at this
      rw [← this]; congr 1; funext v; ring
    rw [hshift]
    have hd0 : ∀ v, 0 ≤ q v - p v - c := fun v => by have := hcle v; omega
    refine key (∑ v, (q v - p v - c)).toNat (fun v => q v - p v - c) hd0
      (by rw [Int.toNat_of_nonneg (Finset.sum_nonneg (fun v _ => hd0 v))]) _ _ ?_
    funext v
    have := congrFun hq v
    simp only [Pi.add_apply] at this ⊢
    omega

end DiscreteConvex.ConjugacyDualityC

open DiscreteConvex.ConjugacyDualityC


theorem solution {V : Type*} [Fintype V] [DecidableEq V] (g : (V → ℤ) → WithTop ℝ) (hg : L2Convex g) (p : V → ℤ)
    (hp : p ∈ DomZ g) :
    (∀ q, g p ≤ g q) ↔
      ((∀ Y : Finset V, g p ≤ g (fun v => p v + IndicatorVec Y v)) ∧ g p = g (p + 1)) := by
  exact l2opt_core g hg p hp
