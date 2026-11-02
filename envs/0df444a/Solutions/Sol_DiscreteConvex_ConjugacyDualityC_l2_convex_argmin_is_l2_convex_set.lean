-- Prove2me | solution 1 for DiscreteConvex.ConjugacyDualityC.l2_convex_argmin_is_l2_convex_set
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T05:01:31.473782+00:00
-- url     : https://prove2.me/submissions/3c130300-0972-4d38-a3ef-4eb7631866ad

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_ArgMin
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_L2Convex
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_LNat2Convex
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_L2ConvexSet
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_LNat2ConvexSet

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace DiscreteConvex.ConjugacyDualityC

open Classical
open scoped Pointwise

section Aux
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma l2a_toE_add (x y : WithTop ℝ) : ToEReal (x + y) = ToEReal x + ToEReal y := by
  induction x using WithTop.recTopCoe <;> induction y using WithTop.recTopCoe <;> rfl

lemma l2a_trf_iter (g : (V → ℤ) → WithTop ℝ) (r : ℝ)
    (hr : ∀ p : V → ℤ, g (p + 1) = g p + (r : WithTop ℝ)) (z : V → ℤ) (k : ℤ) :
    g (fun v => z v + k) = g z + ((k * r : ℝ) : WithTop ℝ) := by
  induction k using Int.induction_on with
  | zero => simp
  | succ i ih =>
    have : (fun v => z v + ((i : ℤ) + 1)) = (fun v => z v + (i : ℤ)) + 1 := by
      funext v; simp only [Pi.add_apply, Pi.one_apply]; ring
    rw [this, hr, ih, add_assoc, ← WithTop.coe_add]; congr 2; push_cast; ring
  | pred i ih =>
    have hw : (fun v => z v + (-(i : ℤ) - 1)) + 1 = (fun v => z v + -(i : ℤ)) := by
      funext v; simp only [Pi.add_apply, Pi.one_apply]; ring
    have h := hr (fun v => z v + (-(i : ℤ) - 1))
    rw [hw, ih] at h
    have h2 : g z + ((((-(i : ℤ)) : ℤ) * r : ℝ) : WithTop ℝ)
        = (g z + (((((-(i : ℤ) - 1) : ℤ)) * r : ℝ) : WithTop ℝ)) + (r : WithTop ℝ) := by
      rw [add_assoc, ← WithTop.coe_add]; congr 2; push_cast; ring
    rw [h2] at h
    exact ((WithTop.add_right_inj (WithTop.coe_ne_top)).mp h).symm

lemma l2a_sbf_shift0 (g : (V → ℤ) → WithTop ℝ) (hS : SBF g)
    (hr0 : ∀ x : V → ℤ, ∀ k : ℤ, g (fun v => x v + k) = g x) (x y : V → ℤ) (k : ℤ) :
    g (fun v => max (x v) (y v - k)) + g (fun v => min (x v) (y v - k) + k) ≤ g x + g y := by
  have h := hS x (fun v => y v - k)
  have e1 : g (fun v => y v - k) = g y := hr0 y (-k)
  have e2 : g (fun v => min (x v) (y v - k) + k) = g (x ⊓ fun v => y v - k) :=
    hr0 (x ⊓ fun v => y v - k) k
  have e3 : (x ⊔ fun v => y v - k) = fun v => max (x v) (y v - k) := rfl
  rw [e2, ← e3, ← e1]
  exact h

lemma l2a_bdd (g1 g2 : (V → ℤ) → WithTop ℝ) (hE : ∀ p, InfConvE g1 g2 p ≠ ⊥) (x : V → ℤ) :
    BddBelow {L : WithTop ℝ | ∃ p1 p2 : V → ℤ, x = p1 + p2 ∧ L = g1 p1 + g2 p2} := by
  have h := hE x
  unfold InfConvE at h
  obtain ⟨β, hβ⟩ := WithBot.ne_bot_iff_exists.mp h
  refine ⟨β, ?_⟩
  rintro L ⟨a, b, hx, rfl⟩
  have : sInf {L : EReal | ∃ p1 p2 : V → ℤ, x = p1 + p2 ∧
      L = ToEReal (g1 p1) + ToEReal (g2 p2)} ≤ ToEReal (g1 a) + ToEReal (g2 b) :=
    sInf_le ⟨a, b, hx, rfl⟩
  rw [← l2a_toE_add, ← hβ] at this
  exact WithBot.coe_le_coe.mp this

lemma l2a_lb (g1 g2 : (V → ℤ) → WithTop ℝ) (hE : ∀ p, InfConvE g1 g2 p ≠ ⊥) (x a b : V → ℤ)
    (h : x = a + b) : InfConv g1 g2 x ≤ g1 a + g2 b :=
  csInf_le (l2a_bdd g1 g2 hE x) ⟨a, b, h, rfl⟩

lemma l2a_glb (g1 g2 : (V → ℤ) → WithTop ℝ) (x : V → ℤ) (c : WithTop ℝ)
    (h : ∀ a b : V → ℤ, x = a + b → c ≤ g1 a + g2 b) : c ≤ InfConv g1 g2 x :=
  le_csInf ⟨_, x, 0, by simp, rfl⟩ (by rintro L ⟨a, b, hx, rfl⟩; exact h a b hx)

lemma l2a_approx (g1 g2 : (V → ℤ) → WithTop ℝ) (x : V → ℤ) (m : ℝ)
    (hm : InfConv g1 g2 x = (m : WithTop ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ a b : V → ℤ, x = a + b ∧ g1 a + g2 b < ((m + ε : ℝ) : WithTop ℝ) := by
  have hlt : InfConv g1 g2 x < ((m + ε : ℝ) : WithTop ℝ) := by
    rw [hm]; exact WithTop.coe_lt_coe.mpr (by linarith)
  unfold InfConv at hlt
  have hne : ({L : WithTop ℝ | ∃ p1 p2 : V → ℤ, x = p1 + p2 ∧ L = g1 p1 + g2 p2}).Nonempty :=
    ⟨g1 x + g2 0, x, 0, by simp, rfl⟩
  obtain ⟨L, ⟨a, b, hx, rfl⟩, hL⟩ := exists_lt_of_csInf_lt hne hlt
  exact ⟨a, b, hx, hL⟩

lemma l2a_infconv_comm (g1 g2 : (V → ℤ) → WithTop ℝ) : InfConv g1 g2 = InfConv g2 g1 := by
  funext x
  unfold InfConv
  congr 1
  ext L
  constructor <;> rintro ⟨a, b, h1, h2⟩ <;> refine ⟨b, a, ?_, ?_⟩
  · rw [add_comm]; exact h1
  · rw [add_comm]; exact h2
  · rw [add_comm]; exact h1
  · rw [add_comm]; exact h2

lemma l2a_infconvE_comm (g1 g2 : (V → ℤ) → WithTop ℝ) (x : V → ℤ) :
    InfConvE g1 g2 x = InfConvE g2 g1 x := by
  unfold InfConvE
  congr 1
  ext L
  constructor <;> rintro ⟨a, b, h1, h2⟩ <;> refine ⟨b, a, ?_, ?_⟩
  · rw [add_comm]; exact h1
  · rw [add_comm]; exact h2
  · rw [add_comm]; exact h1
  · rw [add_comm]; exact h2

lemma l2a_trf_zero_of_argmin (g1 g2 : (V → ℤ) → WithTop ℝ)
    (r1 : ℝ) (h1T : ∀ p : V → ℤ, g1 (p + 1) = g1 p + (r1 : WithTop ℝ))
    (hE : ∀ p, InfConvE g1 g2 p ≠ ⊥)
    (p0 : V → ℤ) (m : ℝ) (hm0 : InfConv g1 g2 p0 = (m : WithTop ℝ))
    (hmin : ∀ q, InfConv g1 g2 p0 ≤ InfConv g1 g2 q) : r1 = 0 := by
  have U : InfConv g1 g2 (p0 + 1) ≤ ((m + r1 : ℝ) : WithTop ℝ) := by
    have hfor : ∀ ε : ℝ, 0 < ε → InfConv g1 g2 (p0 + 1) ≤ ((m + r1 + ε : ℝ) : WithTop ℝ) := by
      intro ε hε
      obtain ⟨a, b, hab, hlt⟩ := l2a_approx g1 g2 p0 m hm0 ε hε
      obtain ⟨α, hα⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hlt)
      rw [← hα] at hlt
      have hα' : α < m + ε := WithTop.coe_lt_coe.mp hlt
      have h1 := l2a_lb g1 g2 hE (p0 + 1) (a + 1) b (by rw [hab]; abel)
      rw [h1T, add_right_comm, ← hα, ← WithTop.coe_add] at h1
      exact h1.trans (WithTop.coe_le_coe.mpr (by linarith))
    obtain ⟨y, hy⟩ := WithTop.ne_top_iff_exists.mp
      (ne_top_of_le_ne_top WithTop.coe_ne_top (hfor 1 one_pos))
    rw [← hy] at hfor ⊢
    refine WithTop.coe_le_coe.mpr (le_of_forall_pos_le_add fun ε hε => ?_)
    have := WithTop.coe_le_coe.mp (hfor ε hε); linarith
  have L : ∀ x : V → ℤ, InfConv g1 g2 x + (r1 : WithTop ℝ) ≤ InfConv g1 g2 (x + 1) := by
    intro x
    refine l2a_glb g1 g2 (x + 1) _ (fun a b hab => ?_)
    have h1 := l2a_lb g1 g2 hE x (a - 1) b (by
      have : x = (x + 1) - 1 := by abel
      rw [this, hab]; abel)
    have h2 : g1 a = g1 (a - 1) + (r1 : WithTop ℝ) := by rw [← h1T, sub_add_cancel]
    rw [h2, add_right_comm]
    exact add_le_add h1 le_rfl
  have hA := L (p0 - 1)
  rw [sub_add_cancel] at hA
  have hB := hmin (p0 - 1)
  have hC := hmin (p0 + 1)
  have hr1a : r1 ≤ 0 := by
    have := (add_le_add hB (le_refl (r1 : WithTop ℝ))).trans hA
    rw [hm0, ← WithTop.coe_add, WithTop.coe_le_coe] at this; linarith
  have hr1b : 0 ≤ r1 := by
    have := hC.trans U
    rw [hm0, WithTop.coe_le_coe] at this; linarith
  linarith

lemma l2a_sbf_cut (g1 g2 : (V → ℤ) → WithTop ℝ)
    (h1S : SBF g1) (h1T0 : ∀ x : V → ℤ, ∀ k : ℤ, g1 (fun v => x v + k) = g1 x)
    (h2S : SBF g2) (h2T0 : ∀ x : V → ℤ, ∀ k : ℤ, g2 (fun v => x v + k) = g2 x)
    (hE : ∀ p, InfConvE g1 g2 p ≠ ⊥)
    (m : ℝ) (hmin : ∀ q, (m : WithTop ℝ) ≤ InfConv g1 g2 q)
    (p d a b q1 q2 : V → ℤ) (hd0 : ∀ v, 0 ≤ d v)
    (hab : p = a + b) (hq : p + d = q1 + q2)
    (ε1 ε2 : ℝ) (hab_lt : g1 a + g2 b < ((m + ε1 : ℝ) : WithTop ℝ))
    (hq_lt : g1 q1 + g2 q2 < ((m + ε2 : ℝ) : WithTop ℝ)) (k : ℤ) :
    let s : V → ℤ := fun v => max (q1 v - a v - k) 0
    let t : V → ℤ := fun v => min (q2 v - b v + k) 0
    let e : V → ℤ := fun v => s v + t v
    (∀ v, 0 ≤ e v ∧ e v ≤ d v) ∧
    p + e = (a + s) + (b + t) ∧
    p + (d - e) = (q1 - s) + (q2 - t) ∧
    g1 (a + s) + g2 (b + t) < ((m + ε1 + ε2 : ℝ) : WithTop ℝ) ∧
    g1 (q1 - s) + g2 (q2 - t) < ((m + ε1 + ε2 : ℝ) : WithTop ℝ) := by
  intro s t e
  have hpv : ∀ v, p v = a v + b v := fun v => congrFun hab v
  have hqv : ∀ v, p v + d v = q1 v + q2 v := fun v => congrFun hq v
  have he_bounds : ∀ v, 0 ≤ e v ∧ e v ≤ d v := by
    intro v
    simp only [e, s, t]
    have := hpv v; have := hqv v; have := hd0 v
    constructor <;> omega
  have hpe1 : p + e = (a + s) + (b + t) := by
    funext v; simp only [Pi.add_apply, e]; have := hpv v; omega
  have hpe2 : p + (d - e) = (q1 - s) + (q2 - t) := by
    funext v; simp only [Pi.add_apply, Pi.sub_apply, e]; have := hqv v; omega
  have S1 := l2a_sbf_shift0 g1 h1S h1T0 a q1 k
  have S2 := l2a_sbf_shift0 g2 h2S h2T0 q2 b k
  have E1 : (fun v => max (a v) (q1 v - k)) = a + s := by
    funext v; simp only [Pi.add_apply, s]; omega
  have E2 : (fun v => min (a v) (q1 v - k) + k) = q1 - s := by
    funext v; simp only [Pi.sub_apply, s]; omega
  have E3 : (fun v => max (q2 v) (b v - k)) = q2 - t := by
    funext v; simp only [Pi.sub_apply, t]; omega
  have E4 : (fun v => min (q2 v) (b v - k) + k) = b + t := by
    funext v; simp only [Pi.add_apply, t]; omega
  rw [E1, E2] at S1
  rw [E3, E4] at S2
  obtain ⟨α, hα⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hab_lt)
  obtain ⟨φ, hφ⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hq_lt)
  have hα_lt : α < m + ε1 := WithTop.coe_lt_coe.mp (hα ▸ hab_lt)
  have hφ_lt : φ < m + ε2 := WithTop.coe_lt_coe.mp (hφ ▸ hq_lt)
  have hsum_le : (g1 (a + s) + g2 (b + t)) + (g1 (q1 - s) + g2 (q2 - t)) ≤
      ((α + φ : ℝ) : WithTop ℝ) := by
    calc (g1 (a + s) + g2 (b + t)) + (g1 (q1 - s) + g2 (q2 - t))
        = (g1 (a + s) + g1 (q1 - s)) + (g2 (q2 - t) + g2 (b + t)) := by
          rw [add_add_add_comm, add_comm (g2 (b + t))]
      _ ≤ (g1 a + g1 q1) + (g2 q2 + g2 b) := add_le_add S1 S2
      _ = (g1 a + g2 b) + (g1 q1 + g2 q2) := by
          rw [add_comm (g2 q2), add_add_add_comm]
      _ = ((α + φ : ℝ) : WithTop ℝ) := by rw [← hα, ← hφ, WithTop.coe_add]
  have hlb1 : (m : WithTop ℝ) ≤ g1 (a + s) + g2 (b + t) :=
    (hmin (p + e)).trans (l2a_lb g1 g2 hE (p + e) (a + s) (b + t) hpe1)
  have hlb2 : (m : WithTop ℝ) ≤ g1 (q1 - s) + g2 (q2 - t) :=
    (hmin (p + (d - e))).trans (l2a_lb g1 g2 hE (p + (d - e)) (q1 - s) (q2 - t) hpe2)
  have hne : (g1 (a + s) + g2 (b + t)) + (g1 (q1 - s) + g2 (q2 - t)) ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top hsum_le
  obtain ⟨hne1, hne2⟩ := WithTop.add_ne_top.mp hne
  obtain ⟨u1, hu1⟩ := WithTop.ne_top_iff_exists.mp hne1
  obtain ⟨u2, hu2⟩ := WithTop.ne_top_iff_exists.mp hne2
  rw [← hu1] at hlb1 hsum_le ⊢
  rw [← hu2] at hlb2 hsum_le ⊢
  rw [← WithTop.coe_add, WithTop.coe_le_coe] at hsum_le
  have hm1 : m ≤ u1 := WithTop.coe_le_coe.mp hlb1
  have hm2 : m ≤ u2 := WithTop.coe_le_coe.mp hlb2
  refine ⟨he_bounds, hpe1, hpe2, ?_, ?_⟩
  · exact WithTop.coe_lt_coe.mpr (by linarith)
  · exact WithTop.coe_lt_coe.mpr (by linarith)

lemma finset_forall_pos_swap {α : Type*} (F : Finset α) (P : α → ℝ → Prop)
    (hmono : ∀ x ε1 ε2, ε1 ≤ ε2 → P x ε1 → P x ε2)
    (h : ∀ ε : ℝ, 0 < ε → ∃ x ∈ F, P x ε) :
    ∃ x ∈ F, ∀ ε : ℝ, 0 < ε → P x ε := by
  by_contra hcon
  push_neg at hcon
  choose εx hεx_pos hnot using hcon
  have hne : F.Nonempty := by obtain ⟨x, hx, -⟩ := h 1 one_pos; exact ⟨x, hx⟩
  obtain ⟨x0, hx0, hmin⟩ := F.exists_min_image (fun x => if hx : x ∈ F then εx x hx else 1) hne
  have hpos0 : 0 < εx x0 hx0 := hεx_pos x0 hx0
  obtain ⟨y, hy, hPy⟩ := h (εx x0 hx0) hpos0
  have hle : εx x0 hx0 ≤ εx y hy := by
    have := hmin y hy
    simpa [hx0, hy] using this
  exact hnot y hy (hmono y _ _ hle hPy)

lemma l2a_exists_split_of_ge_two (g1 g2 : (V → ℤ) → WithTop ℝ)
    (h1S : SBF g1) (h1T0 : ∀ x : V → ℤ, ∀ k : ℤ, g1 (fun v => x v + k) = g1 x)
    (h2S : SBF g2) (h2T0 : ∀ x : V → ℤ, ∀ k : ℤ, g2 (fun v => x v + k) = g2 x)
    (hE : ∀ p, InfConvE g1 g2 p ≠ ⊥)
    (m : ℝ) (hmin : ∀ q, (m : WithTop ℝ) ≤ InfConv g1 g2 q)
    (p d : V → ℤ) (hd0 : ∀ v, 0 ≤ d v)
    (hp : InfConv g1 g2 p = (m : WithTop ℝ))
    (hpd : InfConv g1 g2 (p + d) = (m : WithTop ℝ))
    (v0 : V) (hv0 : 2 ≤ d v0) :
    ∃ e : V → ℤ, (∀ v, 0 ≤ e v ∧ e v ≤ d v) ∧
      1 ≤ ∑ v, e v ∧ ∑ v, e v ≤ (∑ v, d v) - 1 ∧
      InfConv g1 g2 (p + e) = (m : WithTop ℝ) := by
  let F : Finset (V → ℤ) :=
    (Fintype.piFinset (fun v => Finset.Icc 0 (d v))).filter (fun e => e v0 = 1)
  have hF_all : ∀ ε : ℝ, 0 < ε → ∃ e ∈ F, InfConv g1 g2 (p + e) < ((m + ε : ℝ) : WithTop ℝ) := by
    intro ε hε
    obtain ⟨a, b, hab, hab_lt⟩ := l2a_approx g1 g2 p m hp (ε / 2) (by linarith)
    obtain ⟨q1, q2, hq, hq_lt⟩ := l2a_approx g1 g2 (p + d) m hpd (ε / 2) (by linarith)
    let k : ℤ := q1 v0 - a v0 - 1
    have hcut := l2a_sbf_cut g1 g2 h1S h1T0 h2S h2T0 hE m hmin p d a b q1 q2 hd0 hab hq
      (ε / 2) (ε / 2) hab_lt hq_lt k
    let s : V → ℤ := fun v => max (q1 v - a v - k) 0
    let t : V → ℤ := fun v => min (q2 v - b v + k) 0
    let e : V → ℤ := fun v => s v + t v
    have hev0 : e v0 = 1 := by
      have hpv0 : p v0 = a v0 + b v0 := congrFun hab v0
      have hqv0 : p v0 + d v0 = q1 v0 + q2 v0 := congrFun hq v0
      simp only [e, s, t, k]; omega
    have heF : e ∈ F := by
      simp only [F, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc]
      exact ⟨fun v => hcut.1 v, hev0⟩
    refine ⟨e, heF, ?_⟩
    have hle := l2a_lb g1 g2 hE (p + e) (a + s) (b + t) hcut.2.1
    have hlt := hcut.2.2.2.1
    have heq : m + ε / 2 + ε / 2 = m + ε := by ring
    rw [heq] at hlt
    exact lt_of_le_of_lt hle hlt
  obtain ⟨e, heF, he_lt⟩ := finset_forall_pos_swap F
    (fun e ε => InfConv g1 g2 (p + e) < ((m + ε : ℝ) : WithTop ℝ))
    (fun e ε1 ε2 h12 h1 => lt_of_lt_of_le h1 (WithTop.coe_le_coe.mpr (by linarith)))
    hF_all
  simp only [F, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc] at heF
  obtain ⟨heb, hev0⟩ := heF
  refine ⟨e, heb, ?_, ?_, ?_⟩
  · have h1 : e v0 ≤ ∑ v, e v :=
      Finset.single_le_sum (fun v _ => (heb v).1) (Finset.mem_univ v0)
    omega
  · have h1 : d v0 - e v0 ≤ ∑ v, (d v - e v) :=
      Finset.single_le_sum (f := fun v => d v - e v) (fun v _ => by have := (heb v).2; omega)
        (Finset.mem_univ v0)
    rw [Finset.sum_sub_distrib] at h1
    omega
  · apply le_antisymm _ (hmin (p + e))
    have h1 := he_lt 1 one_pos
    obtain ⟨y, hy⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt h1)
    rw [← hy] at he_lt ⊢
    refine WithTop.coe_le_coe.mpr (le_of_forall_pos_le_add fun ε hε => ?_)
    exact le_of_lt (WithTop.coe_lt_coe.mp (he_lt ε hε))

theorem l2a_bounded_decomp (g1 g2 : (V → ℤ) → WithTop ℝ)
    (h1S : SBF g1) (h1T0 : ∀ x : V → ℤ, ∀ k : ℤ, g1 (fun v => x v + k) = g1 x)
    (h2S : SBF g2) (h2T0 : ∀ x : V → ℤ, ∀ k : ℤ, g2 (fun v => x v + k) = g2 x)
    (hE : ∀ p, InfConvE g1 g2 p ≠ ⊥)
    (m : ℝ) (hmin : ∀ q, (m : WithTop ℝ) ≤ InfConv g1 g2 q) :
    ∀ (N : ℕ) (p d : V → ℤ), (∀ v, 0 ≤ d v) → ∑ v, d v ≤ (N : ℤ) →
      InfConv g1 g2 p = (m : WithTop ℝ) →
      InfConv g1 g2 (p + d) = (m : WithTop ℝ) →
      ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
        ∀ a b : V → ℤ, p = a + b → g1 a + g2 b < ((m + ε : ℝ) : WithTop ℝ) →
          ∃ d1 d2 : V → ℤ, d = d1 + d2 ∧ (∀ v, 0 ≤ d1 v ∧ d1 v ≤ (N : ℤ)) ∧
            g1 (a + d1) + g2 (b + d2) < ((m + (3 : ℝ) ^ N * ε : ℝ) : WithTop ℝ) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IH =>
  intro p d hd0 hdN hp hpd
  rcases Nat.eq_zero_or_pos N with rfl | hNpos
  · have hd_zero : d = 0 := by
      funext v
      have hv : d v ≤ ∑ w, d w := Finset.single_le_sum (fun w _ => hd0 w) (Finset.mem_univ v)
      have := hd0 v; simp only [Pi.zero_apply]; omega
    refine ⟨1, one_pos, fun ε hε _ a b _ hab_lt => ⟨0, 0, by simp [hd_zero], by simp, ?_⟩⟩
    simpa using hab_lt
  by_cases hltN : ∑ v, d v < (N : ℤ)
  · have hdN' : ∑ v, d v ≤ ((N - 1 : ℕ) : ℤ) := by omega
    obtain ⟨ε0, hε0, H⟩ := IH (N - 1) (by omega) p d hd0 hdN' hp hpd
    refine ⟨ε0, hε0, fun ε hε hε_lt a b hab hab_lt => ?_⟩
    obtain ⟨d1, d2, hd12, hd1b, hlt⟩ := H ε hε hε_lt a b hab hab_lt
    refine ⟨d1, d2, hd12, fun v => ⟨(hd1b v).1, (hd1b v).2.trans (by omega)⟩, ?_⟩
    refine lt_of_lt_of_le hlt (WithTop.coe_le_coe.mpr ?_)
    have hpow : (3 : ℝ) ^ (N - 1) ≤ (3 : ℝ) ^ N :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    nlinarith
  have hd_eq : ∑ v, d v = (N : ℤ) := by omega
  by_cases hsplit : ∃ e : V → ℤ, (∀ v, 0 ≤ e v ∧ e v ≤ d v) ∧
      1 ≤ ∑ v, e v ∧ ∑ v, e v ≤ (N : ℤ) - 1 ∧
      InfConv g1 g2 (p + e) = (m : WithTop ℝ)
  · obtain ⟨e, heb, he_lo, he_hi, hpe⟩ := hsplit
    let N1 : ℕ := (∑ v, e v).toNat
    let N2 : ℕ := (∑ v, (d v - e v)).toNat
    have hN1_eq : (N1 : ℤ) = ∑ v, e v := Int.toNat_of_nonneg (by omega)
    have hsum_de : ∑ v, (d v - e v) = (N : ℤ) - ∑ v, e v := by
      rw [Finset.sum_sub_distrib, hd_eq]
    have hN2_eq : (N2 : ℤ) = ∑ v, (d v - e v) := Int.toNat_of_nonneg (by omega)
    have hN12 : N1 + N2 = N := by omega
    have hN1_lt : N1 < N := by omega
    have hN2_lt : N2 < N := by omega
    obtain ⟨ε1, hε1_pos, IH1⟩ := IH N1 hN1_lt p e (fun v => (heb v).1) (by omega) hp hpe
    have hpde : InfConv g1 g2 ((p + e) + (d - e)) = (m : WithTop ℝ) := by
      have : (p + e) + (d - e) = p + d := by abel
      rw [this]; exact hpd
    obtain ⟨ε2, hε2_pos, IH2⟩ := IH N2 hN2_lt (p + e) (d - e)
      (fun v => by simp only [Pi.sub_apply]; have := (heb v).2; omega)
      (by show ∑ v, (d v - e v) ≤ (N2 : ℤ); omega) hpe hpde
    have h3N1_pos : (0 : ℝ) < (3 : ℝ) ^ N1 := by positivity
    let ε0 : ℝ := min ε1 (ε2 / (3 : ℝ) ^ N1)
    have hε0_pos : 0 < ε0 := lt_min hε1_pos (div_pos hε2_pos h3N1_pos)
    refine ⟨ε0, hε0_pos, fun ε hε hε_lt a b hab hab_lt => ?_⟩
    have hε_lt1 : ε < ε1 := lt_of_lt_of_le hε_lt (min_le_left _ _)
    have hε_lt2 : (3 : ℝ) ^ N1 * ε < ε2 := by
      have := lt_of_lt_of_le hε_lt (min_le_right _ _)
      rwa [lt_div_iff₀' h3N1_pos] at this
    obtain ⟨e1, e2, he12, he1b, he_lt⟩ := IH1 ε hε hε_lt1 a b hab hab_lt
    have hab' : p + e = (a + e1) + (b + e2) := by rw [hab, he12]; abel
    obtain ⟨f1, f2, hf12, hf1b, hf_lt⟩ := IH2 ((3 : ℝ) ^ N1 * ε) (by positivity) hε_lt2
      (a + e1) (b + e2) hab' he_lt
    refine ⟨e1 + f1, e2 + f2, ?_, ?_, ?_⟩
    · calc d = e + (d - e) := by abel
        _ = (e1 + f1) + (e2 + f2) := by rw [hf12, he12]; abel
    · intro v
      simp only [Pi.add_apply]
      have := he1b v; have := hf1b v
      constructor <;> omega
    · have ha_eq : a + (e1 + f1) = (a + e1) + f1 := by abel
      have hb_eq : b + (e2 + f2) = (b + e2) + f2 := by abel
      have hpow_eq : m + (3 : ℝ) ^ N2 * ((3 : ℝ) ^ N1 * ε) = m + (3 : ℝ) ^ N * ε := by
        rw [← hN12, pow_add]; ring
      rw [ha_eq, hb_eq, ← hpow_eq]
      exact hf_lt
  · have hd_le1 : ∀ v, d v ≤ 1 := by
      intro v
      by_contra hv
      push_neg at hv
      obtain ⟨e, heb, he_lo, he_hi, hpe⟩ :=
        l2a_exists_split_of_ge_two g1 g2 h1S h1T0 h2S h2T0 hE m hmin p d hd0 hp hpd v hv
      rw [hd_eq] at he_hi
      exact hsplit ⟨e, heb, he_lo, he_hi, hpe⟩
    have hv0_ex : ∃ v0 : V, d v0 = 1 := by
      by_contra hcon
      push_neg at hcon
      have hd_zero : ∀ v, d v = 0 := fun v => by
        have := hd0 v; have := hd_le1 v; have := hcon v; omega
      have : ∑ v, d v = 0 := Finset.sum_eq_zero (fun v _ => hd_zero v)
      omega
    obtain ⟨v0, hv0⟩ := hv0_ex
    let F : Finset (V → ℤ) :=
      (Fintype.piFinset (fun v => Finset.Icc 0 (d v))).filter
        (fun e => 1 ≤ ∑ v, e v ∧ ∑ v, e v ≤ (N : ℤ) - 1)
    have hF_gap : ∃ δ0 : ℝ, 0 < δ0 ∧ ∀ e ∈ F,
        ((m + δ0 : ℝ) : WithTop ℝ) ≤ InfConv g1 g2 (p + e) := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨e, heF, he_all⟩ := finset_forall_pos_swap F
        (fun e δ => InfConv g1 g2 (p + e) < ((m + δ : ℝ) : WithTop ℝ))
        (fun e δ1 δ2 h12 h1 => lt_of_lt_of_le h1 (WithTop.coe_le_coe.mpr (by linarith)))
        hcon
      simp only [F, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc] at heF
      have hpe : InfConv g1 g2 (p + e) = (m : WithTop ℝ) := by
        apply le_antisymm _ (hmin (p + e))
        have h1 := he_all 1 one_pos
        obtain ⟨y, hy⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt h1)
        rw [← hy] at he_all ⊢
        refine WithTop.coe_le_coe.mpr (le_of_forall_pos_le_add fun ε hε => ?_)
        exact le_of_lt (WithTop.coe_lt_coe.mp (he_all ε hε))
      exact hsplit ⟨e, heF.1, heF.2.1, heF.2.2, hpe⟩
    obtain ⟨δ0, hδ0_pos, hδ0⟩ := hF_gap
    have hno_F : ∀ e : V → ℤ, (∀ v, 0 ≤ e v ∧ e v ≤ d v) →
        InfConv g1 g2 (p + e) < ((m + δ0 : ℝ) : WithTop ℝ) →
        (∀ v, e v = 0) ∨ (∀ v, e v = d v) := by
      intro e heb hlt
      have hnotF : e ∉ F := fun heF => not_le_of_gt hlt (hδ0 e heF)
      have he_box : e ∈ Fintype.piFinset (fun v => Finset.Icc 0 (d v)) := by
        simp only [Fintype.mem_piFinset, Finset.mem_Icc]
        exact heb
      have hnot_sum : ¬ (1 ≤ ∑ v, e v ∧ ∑ v, e v ≤ (N : ℤ) - 1) := by
        intro hs
        exact hnotF (Finset.mem_filter.mpr ⟨he_box, hs⟩)
      rw [not_and_or, not_le, not_le] at hnot_sum
      rcases hnot_sum with h1 | h2
      · left
        intro v
        have hv : e v ≤ ∑ w, e w := Finset.single_le_sum (fun w _ => (heb w).1) (Finset.mem_univ v)
        have := (heb v).1
        omega
      · right
        intro v
        have hv : d v - e v ≤ ∑ w, (d w - e w) :=
          Finset.single_le_sum (f := fun w => d w - e w)
            (fun w _ => by have := (heb w).2; omega) (Finset.mem_univ v)
        rw [Finset.sum_sub_distrib, hd_eq] at hv
        have := (heb v).2
        omega
    refine ⟨δ0 / 3, by linarith, fun ε hε hε_lt a b hab hab_lt => ?_⟩
    obtain ⟨q1, q2, hq, hq_lt⟩ := l2a_approx g1 g2 (p + d) m hpd ε hε
    let k0 : ℤ := q1 v0 - a v0 - 1
    let q1' : V → ℤ := fun v => q1 v - k0
    let q2' : V → ℤ := fun v => q2 v + k0
    have hq' : p + d = q1' + q2' := by
      funext v; have := congrFun hq v; simp only [Pi.add_apply, q1', q2'] at this ⊢; omega
    have hq'_lt : g1 q1' + g2 q2' < ((m + ε : ℝ) : WithTop ℝ) := by
      have e1 : g1 q1' = g1 q1 := h1T0 q1 (-k0)
      have e2 : g2 q2' = g2 q2 := h2T0 q2 k0
      rw [e1, e2]; exact hq_lt
    -- Cut 1 at k = 0
    have hcut0 := l2a_sbf_cut g1 g2 h1S h1T0 h2S h2T0 hE m hmin p d a b q1' q2' hd0
      hab hq' ε ε hab_lt hq'_lt 0
    let s0 : V → ℤ := fun v => max (q1' v - a v - 0) 0
    let t0 : V → ℤ := fun v => min (q2' v - b v + 0) 0
    let e0 : V → ℤ := fun v => s0 v + t0 v
    have he0_v0 : e0 v0 = 1 := by
      have hpv0 : p v0 = a v0 + b v0 := congrFun hab v0
      have hqv0 : p v0 + d v0 = q1 v0 + q2 v0 := congrFun hq v0
      simp only [e0, s0, t0, q1', q2', k0]; omega
    have he0_lt : InfConv g1 g2 (p + e0) < ((m + δ0 : ℝ) : WithTop ℝ) := by
      have h1 := (l2a_lb g1 g2 hE (p + e0) (a + s0) (b + t0) hcut0.2.1).trans_lt hcut0.2.2.2.1
      exact lt_of_lt_of_le h1 (WithTop.coe_le_coe.mpr (by linarith))
    have he0_eq_d : e0 = d := by
      rcases hno_F e0 hcut0.1 he0_lt with h0 | hd'
      · exfalso; have := h0 v0; omega
      · exact funext hd'
    let a' : V → ℤ := a + s0
    let b' : V → ℤ := b + t0
    have hab' : p + d = a' + b' := by rw [← he0_eq_d]; exact hcut0.2.1
    have hab'_lt : g1 a' + g2 b' < ((m + 2 * ε : ℝ) : WithTop ℝ) := by
      convert hcut0.2.2.2.1 using 2; ring
    -- Cut 2 at k = 1 on (a, b) and (a', b')
    have hcut1 := l2a_sbf_cut g1 g2 h1S h1T0 h2S h2T0 hE m hmin p d a b a' b' hd0
      hab hab' ε (2 * ε) hab_lt hab'_lt 1
    let s1 : V → ℤ := fun v => max (a' v - a v - 1) 0
    let t1 : V → ℤ := fun v => min (b' v - b v + 1) 0
    let e1 : V → ℤ := fun v => s1 v + t1 v
    have he1_v0 : e1 v0 = 0 := by
      have hpv0 : p v0 = a v0 + b v0 := congrFun hab v0
      have hqv0 : p v0 + d v0 = q1 v0 + q2 v0 := congrFun hq v0
      simp only [e1, s1, t1, a', b', s0, t0, q1', q2', k0, Pi.add_apply]; omega
    have he1_lt : InfConv g1 g2 (p + e1) < ((m + δ0 : ℝ) : WithTop ℝ) := by
      have h1 := (l2a_lb g1 g2 hE (p + e1) (a + s1) (b + t1) hcut1.2.1).trans_lt hcut1.2.2.2.1
      exact lt_of_lt_of_le h1 (WithTop.coe_le_coe.mpr (by linarith))
    have he1_eq_0 : e1 = 0 := by
      rcases hno_F e1 hcut1.1 he1_lt with h0 | hd'
      · exact funext h0
      · exfalso; have := hd' v0; omega
    let d1 : V → ℤ := s0 - s1
    let d2 : V → ℤ := t0 - t1
    refine ⟨d1, d2, ?_, ?_, ?_⟩
    · funext v
      have h0v : s0 v + t0 v = d v := congrFun he0_eq_d v
      have h1v : s1 v + t1 v = 0 := congrFun he1_eq_0 v
      simp only [Pi.add_apply, Pi.sub_apply, d1, d2]
      omega
    · intro v
      have : a' v - a v = s0 v := by simp [a']
      simp only [d1, s1, this, s0, Pi.sub_apply]
      constructor <;> omega
    · have ha_eq : a + d1 = a' - s1 := by funext v; simp [a', d1]; ring
      have hb_eq : b + d2 = b' - t1 := by funext v; simp [b', d2]; ring
      rw [ha_eq, hb_eq]
      refine lt_of_lt_of_le hcut1.2.2.2.2 (WithTop.coe_le_coe.mpr ?_)
      have hpow : (3 : ℝ) ^ 1 ≤ (3 : ℝ) ^ N :=
        pow_le_pow_right₀ (by norm_num) hNpos
      nlinarith

lemma uf_finset_exists {ι : Type*} (u : Ultrafilter ℕ) (I : Finset ι) (p : ι → ℕ → Prop)
    (h : ∀ᶠ n in (u : Filter ℕ), ∃ i ∈ I, p i n) :
    ∃ i ∈ I, ∀ᶠ n in (u : Filter ℕ), p i n := by
  by_contra hcon
  have h1 : ∀ i ∈ I, ∀ᶠ n in (u : Filter ℕ), ¬ p i n :=
    fun i hi => Ultrafilter.eventually_not.mpr fun hp => hcon ⟨i, hi, hp⟩
  have h2 : ∀ᶠ n in (u : Filter ℕ), ∀ i ∈ I, ¬ p i n :=
    (Filter.eventually_all_finset I).mpr h1
  rcases (h.and h2).exists with ⟨n, ⟨i, hi, hpi⟩, hall⟩
  exact hall i hi hpi

lemma lconvex_univ : LConvexSet (Set.univ : Set (V → ℤ)) := by
  refine ⟨⟨0, Set.mem_univ 0⟩, ?_, ?_⟩
  · intro p _ q _; exact ⟨Set.mem_univ _, Set.mem_univ _⟩
  · intro p _; exact ⟨Set.mem_univ _, Set.mem_univ _⟩

lemma l2convex_univ : L2ConvexSet (Set.univ : Set (V → ℤ)) := by
  refine ⟨Set.univ, Set.univ, lconvex_univ, lconvex_univ, ?_⟩
  ext x
  simp only [Set.mem_univ, Set.mem_add, true_iff]
  exact ⟨x, trivial, 0, trivial, by simp⟩

theorem l2_argmin_main (g : (V → ℤ) → WithTop ℝ) (hg : L2Convex g)
    (hne : (ArgMin g).Nonempty) : L2ConvexSet (ArgMin g) := by
  by_cases hV : Nonempty V
  · obtain ⟨p0, hp0⟩ := hne
    by_cases htop : g p0 = ⊤
    · have huniv : ArgMin g = Set.univ := by
        ext x
        simp only [ArgMin, Set.mem_setOf_eq, Set.mem_univ, iff_true]
        intro y
        have hy : g y = ⊤ := top_le_iff.mp (htop ▸ hp0 y)
        rw [hy]; exact le_top
      rw [huniv]
      exact l2convex_univ
    obtain ⟨g1, g2, ⟨h1S, r1, h1T⟩, ⟨h2S, r2, h2T⟩, hE, rfl⟩ := hg
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp htop
    have hm0 : InfConv g1 g2 p0 = (m : WithTop ℝ) := hm.symm
    have hmin : ∀ q, (m : WithTop ℝ) ≤ InfConv g1 g2 q := fun q => hm0 ▸ hp0 q
    have hr1 : r1 = 0 := l2a_trf_zero_of_argmin g1 g2 r1 h1T hE p0 m hm0 hp0
    have hr2 : r2 = 0 := by
      have hcomm := l2a_infconv_comm g1 g2
      have hE' : ∀ p, InfConvE g2 g1 p ≠ ⊥ := fun p => by
        rw [← l2a_infconvE_comm]; exact hE p
      exact l2a_trf_zero_of_argmin g2 g1 r2 h2T hE' p0 m (hcomm ▸ hm0) (fun q => hcomm ▸ hp0 q)
    have h1T0 : ∀ x : V → ℤ, ∀ k : ℤ, g1 (fun v => x v + k) = g1 x := by
      intro x k
      rw [l2a_trf_iter g1 r1 h1T x k, hr1, mul_zero, WithTop.coe_zero, add_zero]
    have h2T0 : ∀ x : V → ℤ, ∀ k : ℤ, g2 (fun v => x v + k) = g2 x := by
      intro x k
      rw [l2a_trf_iter g2 r2 h2T x k, hr2, mul_zero, WithTop.coe_zero, add_zero]
    have hseq : ∀ n : ℕ, ∃ a b : V → ℤ, ∃ α β : ℝ,
        p0 = a + b ∧ g1 a = (α : WithTop ℝ) ∧ g2 b = (β : WithTop ℝ) ∧
        m ≤ α + β ∧ α + β < m + 1 / ((n : ℝ) + 1) := by
      intro n
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      obtain ⟨a, b, hab, hlt⟩ := l2a_approx g1 g2 p0 m hm0 (1 / ((n : ℝ) + 1)) hpos
      have hne_ab : g1 a + g2 b ≠ ⊤ := ne_top_of_lt hlt
      obtain ⟨ha_ne, hb_ne⟩ := WithTop.add_ne_top.mp hne_ab
      obtain ⟨α, hα⟩ := WithTop.ne_top_iff_exists.mp ha_ne
      obtain ⟨β, hβ⟩ := WithTop.ne_top_iff_exists.mp hb_ne
      have hlb : (m : WithTop ℝ) ≤ g1 a + g2 b := hm0 ▸ l2a_lb g1 g2 hE p0 a b hab
      rw [← hα, ← hβ, ← WithTop.coe_add] at hlb hlt
      exact ⟨a, b, α, β, hab, hα.symm, hβ.symm,
        WithTop.coe_le_coe.mp hlb, WithTop.coe_lt_coe.mp hlt⟩
    choose a b α β hab ha hb hm_le hab_lt using hseq
    have hlb_g1 : ∀ (n : ℕ) (z : V → ℤ),
        ((α n - 1 / ((n : ℝ) + 1) : ℝ) : WithTop ℝ) < g1 (a n + z) := by
      intro n z
      by_cases hz : g1 (a n + z) = ⊤
      · rw [hz]; exact WithTop.coe_lt_top _
      · obtain ⟨γ, hγ⟩ := WithTop.ne_top_iff_exists.mp hz
        have h1 : (m : WithTop ℝ) ≤ g1 (a n + z) + g2 (b n) := by
          refine (hmin (p0 + z)).trans (l2a_lb g1 g2 hE (p0 + z) (a n + z) (b n) ?_)
          rw [hab n]; abel
        rw [← hγ, hb n, ← WithTop.coe_add, WithTop.coe_le_coe] at h1
        rw [← hγ, WithTop.coe_lt_coe]
        linarith [hab_lt n]
    have hlb_g2 : ∀ (n : ℕ) (z : V → ℤ),
        ((β n - 1 / ((n : ℝ) + 1) : ℝ) : WithTop ℝ) < g2 (b n + z) := by
      intro n z
      by_cases hz : g2 (b n + z) = ⊤
      · rw [hz]; exact WithTop.coe_lt_top _
      · obtain ⟨γ, hγ⟩ := WithTop.ne_top_iff_exists.mp hz
        have h1 : (m : WithTop ℝ) ≤ g1 (a n) + g2 (b n + z) := by
          refine (hmin (p0 + z)).trans (l2a_lb g1 g2 hE (p0 + z) (a n) (b n + z) ?_)
          rw [hab n]; abel
        rw [ha n, ← hγ, ← WithTop.coe_add, WithTop.coe_le_coe] at h1
        rw [← hγ, WithTop.coe_lt_coe]
        linarith [hab_lt n]
    let u : Ultrafilter ℕ := Ultrafilter.of Filter.atTop
    have hu_le : (u : Filter ℕ) ≤ Filter.atTop := Ultrafilter.of_le Filter.atTop
    have hu_inv_lt : ∀ δ : ℝ, 0 < δ → ∀ᶠ (n : ℕ) in (u : Filter ℕ), 1 / ((n : ℝ) + 1) < δ := by
      intro δ hδ
      apply Filter.Eventually.filter_mono hu_le
      rw [Filter.eventually_atTop]
      refine ⟨⌈1 / δ⌉₊, fun n hn => ?_⟩
      have h1 : 1 / δ ≤ (n : ℝ) := by
        calc 1 / δ ≤ (⌈1 / δ⌉₊ : ℝ) := Nat.le_ceil _
          _ ≤ (n : ℝ) := by exact_mod_cast hn
      have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      rw [div_lt_iff₀ hn1]
      have := mul_le_mul_of_nonneg_right h1 hδ.le
      rw [div_mul_cancel₀ 1 (ne_of_gt hδ)] at this
      linarith
    let D1 : Set (V → ℤ) :=
      {d1 | ∀ ε : ℝ, 0 < ε → ∀ᶠ n in (u : Filter ℕ),
        g1 (a n + d1) < ((α n + ε : ℝ) : WithTop ℝ)}
    let D2 : Set (V → ℤ) :=
      {d2 | ∀ ε : ℝ, 0 < ε → ∀ᶠ n in (u : Filter ℕ),
        g2 (b n + d2) < ((β n + ε : ℝ) : WithTop ℝ)}
    have hD1_zero : (0 : V → ℤ) ∈ D1 := by
      intro ε hε
      refine Filter.Eventually.of_forall fun n => ?_
      rw [add_zero, ha n, WithTop.coe_lt_coe]; linarith
    have hD2_zero : (0 : V → ℤ) ∈ D2 := by
      intro ε hε
      refine Filter.Eventually.of_forall fun n => ?_
      rw [add_zero, hb n, WithTop.coe_lt_coe]; linarith
    have hD1_conv : LConvexSet D1 := by
      refine ⟨⟨0, hD1_zero⟩, ?_, ?_⟩
      · intro x hx y hy
        have hxy : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in (u : Filter ℕ),
            g1 (a n + (x ⊔ y)) < ((α n + ε : ℝ) : WithTop ℝ) ∧
            g1 (a n + (x ⊓ y)) < ((α n + ε : ℝ) : WithTop ℝ) := by
          intro ε hε
          have h1 := hx (ε / 3) (by linarith)
          have h2 := hy (ε / 3) (by linarith)
          have h3 := hu_inv_lt (ε / 3) (by linarith)
          refine ((h1.and h2).and h3).mono ?_
          rintro n ⟨⟨hx_n, hy_n⟩, hn_inv⟩
          obtain ⟨γx, hγx⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hx_n)
          obtain ⟨γy, hγy⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hy_n)
          have hx_lt : γx < α n + ε / 3 := WithTop.coe_lt_coe.mp (hγx ▸ hx_n)
          have hy_lt : γy < α n + ε / 3 := WithTop.coe_lt_coe.mp (hγy ▸ hy_n)
          have hsbf := h1S (a n + x) (a n + y)
          have esup : (a n + x) ⊔ (a n + y) = a n + (x ⊔ y) := by
            funext v; show max (a n v + x v) (a n v + y v) = a n v + max (x v) (y v); omega
          have einf : (a n + x) ⊓ (a n + y) = a n + (x ⊓ y) := by
            funext v; show min (a n v + x v) (a n v + y v) = a n v + min (x v) (y v); omega
          rw [esup, einf, ← hγx, ← hγy, ← WithTop.coe_add] at hsbf
          have hne_si : g1 (a n + (x ⊔ y)) + g1 (a n + (x ⊓ y)) ≠ ⊤ :=
            ne_top_of_le_ne_top WithTop.coe_ne_top hsbf
          obtain ⟨hne_s, hne_i⟩ := WithTop.add_ne_top.mp hne_si
          obtain ⟨γs, hγs⟩ := WithTop.ne_top_iff_exists.mp hne_s
          obtain ⟨γi, hγi⟩ := WithTop.ne_top_iff_exists.mp hne_i
          have hls := hlb_g1 n (x ⊔ y)
          have hli := hlb_g1 n (x ⊓ y)
          rw [← hγs, WithTop.coe_lt_coe] at hls
          rw [← hγi, WithTop.coe_lt_coe] at hli
          rw [← hγs, ← hγi, ← WithTop.coe_add, ge_iff_le, WithTop.coe_le_coe] at hsbf
          rw [← hγs, ← hγi, WithTop.coe_lt_coe, WithTop.coe_lt_coe]
          constructor <;> linarith
        exact ⟨fun ε hε => (hxy ε hε).mono fun _ h => h.1,
               fun ε hε => (hxy ε hε).mono fun _ h => h.2⟩
      · intro x hx
        refine ⟨fun ε hε => (hx ε hε).mono fun n hn => ?_,
                fun ε hε => (hx ε hε).mono fun n hn => ?_⟩
        · have e : (a n + fun v => x v + 1) = fun v => (a n + x) v + 1 := by
            funext v; simp [Pi.add_apply]; ring
          rw [e, h1T0 (a n + x) 1]; exact hn
        · have e : (a n + fun v => x v - 1) = fun v => (a n + x) v + (-1) := by
            funext v; simp [Pi.add_apply]; ring
          rw [e, h1T0 (a n + x) (-1)]; exact hn
    have hD2_conv : LConvexSet D2 := by
      refine ⟨⟨0, hD2_zero⟩, ?_, ?_⟩
      · intro x hx y hy
        have hxy : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in (u : Filter ℕ),
            g2 (b n + (x ⊔ y)) < ((β n + ε : ℝ) : WithTop ℝ) ∧
            g2 (b n + (x ⊓ y)) < ((β n + ε : ℝ) : WithTop ℝ) := by
          intro ε hε
          have h1 := hx (ε / 3) (by linarith)
          have h2 := hy (ε / 3) (by linarith)
          have h3 := hu_inv_lt (ε / 3) (by linarith)
          refine ((h1.and h2).and h3).mono ?_
          rintro n ⟨⟨hx_n, hy_n⟩, hn_inv⟩
          obtain ⟨γx, hγx⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hx_n)
          obtain ⟨γy, hγy⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hy_n)
          have hx_lt : γx < β n + ε / 3 := WithTop.coe_lt_coe.mp (hγx ▸ hx_n)
          have hy_lt : γy < β n + ε / 3 := WithTop.coe_lt_coe.mp (hγy ▸ hy_n)
          have hsbf := h2S (b n + x) (b n + y)
          have esup : (b n + x) ⊔ (b n + y) = b n + (x ⊔ y) := by
            funext v; show max (b n v + x v) (b n v + y v) = b n v + max (x v) (y v); omega
          have einf : (b n + x) ⊓ (b n + y) = b n + (x ⊓ y) := by
            funext v; show min (b n v + x v) (b n v + y v) = b n v + min (x v) (y v); omega
          rw [esup, einf, ← hγx, ← hγy, ← WithTop.coe_add] at hsbf
          have hne_si : g2 (b n + (x ⊔ y)) + g2 (b n + (x ⊓ y)) ≠ ⊤ :=
            ne_top_of_le_ne_top WithTop.coe_ne_top hsbf
          obtain ⟨hne_s, hne_i⟩ := WithTop.add_ne_top.mp hne_si
          obtain ⟨γs, hγs⟩ := WithTop.ne_top_iff_exists.mp hne_s
          obtain ⟨γi, hγi⟩ := WithTop.ne_top_iff_exists.mp hne_i
          have hls := hlb_g2 n (x ⊔ y)
          have hli := hlb_g2 n (x ⊓ y)
          rw [← hγs, WithTop.coe_lt_coe] at hls
          rw [← hγi, WithTop.coe_lt_coe] at hli
          rw [← hγs, ← hγi, ← WithTop.coe_add, ge_iff_le, WithTop.coe_le_coe] at hsbf
          rw [← hγs, ← hγi, WithTop.coe_lt_coe, WithTop.coe_lt_coe]
          constructor <;> linarith
        exact ⟨fun ε hε => (hxy ε hε).mono fun _ h => h.1,
               fun ε hε => (hxy ε hε).mono fun _ h => h.2⟩
      · intro x hx
        refine ⟨fun ε hε => (hx ε hε).mono fun n hn => ?_,
                fun ε hε => (hx ε hε).mono fun n hn => ?_⟩
        · have e : (b n + fun v => x v + 1) = fun v => (b n + x) v + 1 := by
            funext v; simp [Pi.add_apply]; ring
          rw [e, h2T0 (b n + x) 1]; exact hn
        · have e : (b n + fun v => x v - 1) = fun v => (b n + x) v + (-1) := by
            funext v; simp [Pi.add_apply]; ring
          rw [e, h2T0 (b n + x) (-1)]; exact hn
    let D1' : Set (V → ℤ) := {x | x - p0 ∈ D1}
    have hD1'_conv : LConvexSet D1' := by
      refine ⟨⟨p0, by simp [D1', hD1_zero]⟩, ?_, ?_⟩
      · intro x hx y hy
        have esup : (fun v => max (x v) (y v)) - p0 = (x - p0) ⊔ (y - p0) := by
          funext v; show max (x v) (y v) - p0 v = max (x v - p0 v) (y v - p0 v); omega
        have einf : (fun v => min (x v) (y v)) - p0 = (x - p0) ⊓ (y - p0) := by
          funext v; show min (x v) (y v) - p0 v = min (x v - p0 v) (y v - p0 v); omega
        simp only [D1', Set.mem_setOf_eq, esup, einf]
        exact hD1_conv.2.1 (x - p0) hx (y - p0) hy
      · intro x hx
        have ep : (fun v => x v + 1) - p0 = fun v => (x - p0) v + 1 := by
          funext v; simp [Pi.sub_apply]; ring
        have em : (fun v => x v - 1) - p0 = fun v => (x - p0) v - 1 := by
          funext v; simp [Pi.sub_apply]; ring
        simp only [D1', Set.mem_setOf_eq, ep, em]
        exact hD1_conv.2.2 (x - p0) hx
    refine ⟨D1', D2, hD1'_conv, hD2_conv, ?_⟩
    ext q
    simp only [Set.mem_add]
    constructor
    · intro hq
      have hqm : InfConv g1 g2 q = (m : WithTop ℝ) := le_antisymm (hm0 ▸ hq p0) (hmin q)
      let c : ℤ := -∑ v, |q v - p0 v|
      have hcle : ∀ v, c ≤ q v - p0 v := by
        intro v
        have h1 : |q v - p0 v| ≤ ∑ w, |q w - p0 w| :=
          Finset.single_le_sum (f := fun w => |q w - p0 w|) (fun w _ => abs_nonneg _)
            (Finset.mem_univ v)
        have h2 := neg_abs_le (q v - p0 v)
        dsimp [c]; linarith
      let d : V → ℤ := fun v => q v - p0 v - c
      have hd0 : ∀ v, 0 ≤ d v := fun v => by have := hcle v; dsimp [d]; omega
      let N : ℕ := (∑ v, d v).toNat
      have hdN : ∑ v, d v ≤ (N : ℤ) := by
        rw [Int.toNat_of_nonneg (Finset.sum_nonneg fun v _ => hd0 v)]
      have hpd : InfConv g1 g2 (p0 + d) = (m : WithTop ℝ) := by
        rw [← hqm]
        unfold InfConv
        congr 1; ext L
        constructor <;> rintro ⟨x1, x2, hx, rfl⟩
        · refine ⟨fun v => x1 v + c, x2, ?_, ?_⟩
          · funext v; have := congrFun hx v; simp only [Pi.add_apply, d] at this ⊢; omega
          · rw [h1T0 x1 c]
        · refine ⟨fun v => x1 v - c, x2, ?_, ?_⟩
          · funext v; have := congrFun hx v; simp only [Pi.add_apply, d] at this ⊢; omega
          · rw [← h1T0 x1 (-c)]; rfl
      obtain ⟨ε0, hε0_pos, Hdecomp⟩ := l2a_bounded_decomp g1 g2 h1S h1T0 h2S h2T0 hE m hmin
        N p0 d hd0 hdN hm0 hpd
      let B : Finset (V → ℤ) := Fintype.piFinset (fun _ => Finset.Icc 0 (N : ℤ))
      have hev_ex : ∀ᶠ n in (u : Filter ℕ), ∃ d1 ∈ B,
          g1 (a n + d1) + g2 (b n + (d - d1)) <
            ((m + (3 : ℝ) ^ N * (1 / ((n : ℝ) + 1)) : ℝ) : WithTop ℝ) := by
        refine (hu_inv_lt ε0 hε0_pos).mono fun n hn => ?_
        have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        have hab_n : g1 (a n) + g2 (b n) < ((m + 1 / ((n : ℝ) + 1) : ℝ) : WithTop ℝ) := by
          rw [ha n, hb n, ← WithTop.coe_add, WithTop.coe_lt_coe]; exact hab_lt n
        obtain ⟨d1, d2, hd12, hd1b, hlt⟩ := Hdecomp (1 / ((n : ℝ) + 1)) hpos hn
          (a n) (b n) (hab n) hab_n
        have hd2_eq : d2 = d - d1 := by rw [hd12]; abel
        rw [hd2_eq] at hlt
        refine ⟨d1, ?_, hlt⟩
        simp only [B, Fintype.mem_piFinset, Finset.mem_Icc]
        exact hd1b
      obtain ⟨d1, hd1B, hd1_ev⟩ := uf_finset_exists u B
        (fun d1 n => g1 (a n + d1) + g2 (b n + (d - d1)) <
          ((m + (3 : ℝ) ^ N * (1 / ((n : ℝ) + 1)) : ℝ) : WithTop ℝ))
        hev_ex
      have hd1_D1 : d1 ∈ D1 := by
        intro ε hε
        have hpow_pos : (0 : ℝ) < (3 : ℝ) ^ N + 2 := by positivity
        have hinv := hu_inv_lt (ε / ((3 : ℝ) ^ N + 2)) (div_pos hε hpow_pos)
        refine (hd1_ev.and hinv).mono fun n ⟨hlt, hn_inv⟩ => ?_
        have hne_s : g1 (a n + d1) + g2 (b n + (d - d1)) ≠ ⊤ := ne_top_of_lt hlt
        obtain ⟨hne1, hne2⟩ := WithTop.add_ne_top.mp hne_s
        obtain ⟨γ1, hγ1⟩ := WithTop.ne_top_iff_exists.mp hne1
        obtain ⟨γ2, hγ2⟩ := WithTop.ne_top_iff_exists.mp hne2
        have hlb2 := hlb_g2 n (d - d1)
        rw [← hγ2, WithTop.coe_lt_coe] at hlb2
        rw [← hγ1, ← hγ2, ← WithTop.coe_add, WithTop.coe_lt_coe] at hlt
        rw [← hγ1, WithTop.coe_lt_coe]
        have hmul := (lt_div_iff₀' hpow_pos).mp hn_inv
        rw [add_mul] at hmul
        have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        have := hm_le n
        linarith
      have hd2_D2 : d - d1 ∈ D2 := by
        intro ε hε
        have hpow_pos : (0 : ℝ) < (3 : ℝ) ^ N + 2 := by positivity
        have hinv := hu_inv_lt (ε / ((3 : ℝ) ^ N + 2)) (div_pos hε hpow_pos)
        refine (hd1_ev.and hinv).mono fun n ⟨hlt, hn_inv⟩ => ?_
        have hne_s : g1 (a n + d1) + g2 (b n + (d - d1)) ≠ ⊤ := ne_top_of_lt hlt
        obtain ⟨hne1, hne2⟩ := WithTop.add_ne_top.mp hne_s
        obtain ⟨γ1, hγ1⟩ := WithTop.ne_top_iff_exists.mp hne1
        obtain ⟨γ2, hγ2⟩ := WithTop.ne_top_iff_exists.mp hne2
        have hlb1 := hlb_g1 n d1
        rw [← hγ1, WithTop.coe_lt_coe] at hlb1
        rw [← hγ1, ← hγ2, ← WithTop.coe_add, WithTop.coe_lt_coe] at hlt
        rw [← hγ2, WithTop.coe_lt_coe]
        have hmul := (lt_div_iff₀' hpow_pos).mp hn_inv
        rw [add_mul] at hmul
        have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        have := hm_le n
        linarith
      have hd1c_D1 : (fun v => d1 v + c) ∈ D1 := by
        intro ε hε
        refine (hd1_D1 ε hε).mono fun n hn => ?_
        have e : (a n + fun v => d1 v + c) = fun v => (a n + d1) v + c := by
          funext v; simp [Pi.add_apply]; ring
        rw [e, h1T0 (a n + d1) c]; exact hn
      refine ⟨p0 + fun v => d1 v + c, ?_, d - d1, hd2_D2, ?_⟩
      · simp [D1', hd1c_D1]
      · funext v; simp only [Pi.add_apply, Pi.sub_apply, d]; omega
    · rintro ⟨x1, hx1, x2, hx2, rfl⟩
      intro y
      refine le_trans ?_ (hmin y)
      have hfor : ∀ ε : ℝ, 0 < ε →
          InfConv g1 g2 (x1 + x2) < ((m + ε : ℝ) : WithTop ℝ) := by
        intro ε hε
        have h1 := hx1 (ε / 3) (by linarith)
        have h2 := hx2 (ε / 3) (by linarith)
        have h3 := hu_inv_lt (ε / 3) (by linarith)
        rcases ((h1.and h2).and h3).exists with ⟨n, ⟨hx1_n, hx2_n⟩, hn_inv⟩
        obtain ⟨γ1, hγ1⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hx1_n)
        obtain ⟨γ2, hγ2⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hx2_n)
        have hγ1_lt : γ1 < α n + ε / 3 := WithTop.coe_lt_coe.mp (hγ1 ▸ hx1_n)
        have hγ2_lt : γ2 < β n + ε / 3 := WithTop.coe_lt_coe.mp (hγ2 ▸ hx2_n)
        have hlb := l2a_lb g1 g2 hE (x1 + x2) (a n + (x1 - p0)) (b n + x2) (by
          rw [hab n]; abel)
        refine lt_of_le_of_lt hlb ?_
        rw [← hγ1, ← hγ2, ← WithTop.coe_add, WithTop.coe_lt_coe]
        have := hab_lt n
        linarith
      have h1 := hfor 1 one_pos
      obtain ⟨z, hz⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt h1)
      rw [← hz] at hfor ⊢
      refine WithTop.coe_le_coe.mpr (le_of_forall_pos_le_add fun ε hε => ?_)
      exact le_of_lt (WithTop.coe_lt_coe.mp (hfor ε hε))
  · haveI : IsEmpty V := not_nonempty_iff.mp hV
    have huniv : ArgMin g = Set.univ := by
      obtain ⟨p0, hp0⟩ := hne
      ext x
      simp only [Set.mem_univ, iff_true]
      convert hp0
    rw [huniv]
    exact l2convex_univ

theorem lnat2_argmin_main (g : (V → ℤ) → WithTop ℝ) (hg : LNat2Convex g)
    (hne : (ArgMin g).Nonempty) : LNat2ConvexSet (ArgMin g) := by
  obtain ⟨g1, g2, h1, h2, hE, rfl⟩ := hg
  let G1 := LiftedFunctionL g1
  let G2 := LiftedFunctionL g2
  let π : (Option V → ℤ) → (V → ℤ) := fun w v => w (some v) - w none
  let lift0 : (V → ℤ) → (Option V → ℤ) := fun p o => Option.elim o 0 p
  have hπ_lift : ∀ p : V → ℤ, π (lift0 p) = p := by
    intro p; funext v; simp [π, lift0]
  have hπ_add : ∀ w1 w2 : Option V → ℤ, π (w1 + w2) = π w1 + π w2 := by
    intro w1 w2; funext v; simp only [π, Pi.add_apply]; omega
  have hG1 : ∀ w, G1 w = g1 (π w) := fun _ => rfl
  have hG2 : ∀ w, G2 w = g2 (π w) := fun _ => rfl
  have hset_eq : ∀ w : Option V → ℤ,
      {L : WithTop ℝ | ∃ w1 w2 : Option V → ℤ, w = w1 + w2 ∧ L = G1 w1 + G2 w2} =
      {L : WithTop ℝ | ∃ p1 p2 : V → ℤ, π w = p1 + p2 ∧ L = g1 p1 + g2 p2} := by
    intro w; ext L
    constructor
    · rintro ⟨w1, w2, rfl, rfl⟩
      exact ⟨π w1, π w2, hπ_add w1 w2, rfl⟩
    · rintro ⟨p1, p2, hp, rfl⟩
      refine ⟨lift0 p1, w - lift0 p1, by abel, ?_⟩
      have e2 : π (w - lift0 p1) = p2 := by
        funext v
        have := congrFun hp v
        simp only [π, lift0, Pi.sub_apply, Pi.add_apply, Option.elim] at this ⊢
        omega
      rw [hG1, hG2, hπ_lift, e2]
  have hsetE_eq : ∀ w : Option V → ℤ,
      {L : EReal | ∃ w1 w2 : Option V → ℤ, w = w1 + w2 ∧ L = ToEReal (G1 w1) + ToEReal (G2 w2)} =
      {L : EReal | ∃ p1 p2 : V → ℤ, π w = p1 + p2 ∧ L = ToEReal (g1 p1) + ToEReal (g2 p2)} := by
    intro w; ext L
    constructor
    · rintro ⟨w1, w2, rfl, rfl⟩
      exact ⟨π w1, π w2, hπ_add w1 w2, rfl⟩
    · rintro ⟨p1, p2, hp, rfl⟩
      refine ⟨lift0 p1, w - lift0 p1, by abel, ?_⟩
      have e2 : π (w - lift0 p1) = p2 := by
        funext v
        have := congrFun hp v
        simp only [π, lift0, Pi.sub_apply, Pi.add_apply, Option.elim] at this ⊢
        omega
      rw [hG1, hG2, hπ_lift, e2]
  have hIC_eq : ∀ w : Option V → ℤ, InfConv G1 G2 w = InfConv g1 g2 (π w) := by
    intro w; unfold InfConv; rw [hset_eq]
  have hICE_eq : ∀ w : Option V → ℤ, InfConvE G1 G2 w = InfConvE g1 g2 (π w) := by
    intro w; unfold InfConvE; rw [hsetE_eq]
  have hG_l2 : L2Convex (InfConv G1 G2) :=
    ⟨G1, G2, h1, h2, fun w => by rw [hICE_eq]; exact hE (π w), rfl⟩
  have hArg_eq : ArgMin (InfConv G1 G2) = LiftedSetL (ArgMin (InfConv g1 g2)) := by
    ext w
    simp only [ArgMin, LiftedSetL, Set.mem_setOf_eq, hIC_eq]
    constructor
    · intro hw y
      have := hw (lift0 y)
      rwa [hπ_lift] at this
    · intro hw w'
      exact hw (π w')
  obtain ⟨p0, hp0⟩ := hne
  have hneG : (ArgMin (InfConv G1 G2)).Nonempty := by
    refine ⟨lift0 p0, ?_⟩
    rw [hArg_eq]
    show π (lift0 p0) ∈ ArgMin (InfConv g1 g2)
    rwa [hπ_lift]
  obtain ⟨E1, E2, hE1, hE2, hE_sum⟩ := l2_argmin_main (InfConv G1 G2) hG_l2 hneG
  let D1 : Set (V → ℤ) := π '' E1
  let D2 : Set (V → ℤ) := π '' E2
  have hshift_mem : ∀ (E : Set (Option V → ℤ)), LConvexSet E →
      ∀ w ∈ E, ∀ k : ℤ, (fun o => w o + k) ∈ E := by
    intro E hE_conv w hw k
    induction k using Int.induction_on with
    | zero => simpa using hw
    | succ i ih =>
      convert (hE_conv.2.2 _ ih).1 using 1
      funext o; push_cast; ring
    | pred i ih =>
      convert (hE_conv.2.2 _ ih).2 using 1
      funext o; push_cast; ring
  have hLift_D1 : LiftedSetL D1 = E1 := by
    ext w
    simp only [LiftedSetL, D1, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨w', hw', hπ⟩
      have heq : w = fun o => w' o + (w none - w' none) := by
        funext o
        cases o with
        | none => omega
        | some v =>
          have := congrFun hπ v
          simp only [π] at this
          omega
      rw [heq]
      exact hshift_mem E1 hE1 w' hw' (w none - w' none)
    · intro hw
      exact ⟨w, hw, rfl⟩
  have hLift_D2 : LiftedSetL D2 = E2 := by
    ext w
    simp only [LiftedSetL, D2, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨w', hw', hπ⟩
      have heq : w = fun o => w' o + (w none - w' none) := by
        funext o
        cases o with
        | none => omega
        | some v =>
          have := congrFun hπ v
          simp only [π] at this
          omega
      rw [heq]
      exact hshift_mem E2 hE2 w' hw' (w none - w' none)
    · intro hw
      exact ⟨w, hw, rfl⟩
  refine ⟨D1, D2, ?_, ?_, ?_⟩
  · unfold LNatConvexSet; rwa [hLift_D1]
  · unfold LNatConvexSet; rwa [hLift_D2]
  · ext p
    simp only [Set.mem_add, D1, D2, Set.mem_image]
    constructor
    · intro hp
      have hmem : lift0 p ∈ ArgMin (InfConv G1 G2) := by
        rw [hArg_eq]; show π (lift0 p) ∈ ArgMin (InfConv g1 g2); rwa [hπ_lift]
      rw [hE_sum] at hmem
      rcases hmem with ⟨w1, hw1, w2, hw2, hw⟩
      have hw' : w1 + w2 = lift0 p := hw
      refine ⟨π w1, ⟨w1, hw1, rfl⟩, π w2, ⟨w2, hw2, rfl⟩, ?_⟩
      rw [← hπ_add, hw', hπ_lift]
    · rintro ⟨p1, ⟨w1, hw1, rfl⟩, p2, ⟨w2, hw2, rfl⟩, rfl⟩
      have hmem : w1 + w2 ∈ ArgMin (InfConv G1 G2) := by
        rw [hE_sum]; exact ⟨w1, hw1, w2, hw2, rfl⟩
      rw [hArg_eq] at hmem
      change π (w1 + w2) ∈ ArgMin (InfConv g1 g2) at hmem
      rwa [hπ_add] at hmem

end Aux
end DiscreteConvex.ConjugacyDualityC

open Classical
open scoped Pointwise
open DiscreteConvex.ConjugacyDualityC

theorem solution {V : Type*} [Fintype V] [DecidableEq V] :
    (∀ g : (V → ℤ) → WithTop ℝ, L2Convex g → (ArgMin g).Nonempty → L2ConvexSet (ArgMin g)) ∧
    (∀ g : (V → ℤ) → WithTop ℝ, LNat2Convex g → (ArgMin g).Nonempty → LNat2ConvexSet (ArgMin g)) :=
  ⟨l2_argmin_main, lnat2_argmin_main⟩
