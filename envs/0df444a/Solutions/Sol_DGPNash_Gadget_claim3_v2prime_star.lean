-- Prove2me | solution 1 for DGPNash.Gadget.claim3_v2prime_star
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T13:20:18.133562+00:00
-- url     : https://prove2.me/submissions/645c4e2f-7cb5-46b1-a940-64ee60d77efa

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_Gadget_EpsNash
import Definitions.Def_DGPNash_Gadget_AffectsGraph
import Definitions.Def_DGPNash_Gadget_AddMulGame

set_option autoImplicit false

namespace Df66664d

open DGPNash.Gadget

abbrev Mix := ∀ r, AddMulStrat r → ℝ

lemma prod_sum_mul (τ g : Mix) :
    ∑ s : (∀ r, AddMulStrat r), (∏ i, τ i (s i)) * ∏ i, g i (s i)
      = ∏ i, ∑ a, τ i a * g i a := by
  rw [Fintype.prod_sum]
  simp_rw [← Finset.prod_mul_distrib]

lemma univ_roles : (Finset.univ : Finset AddMulRole) =
    {.v1, .v2, .v3, .w1, .v1', .w2, .v2', .w3, .w, .u} := by
  ext x; cases x <;> simp

lemma prod10 (f : AddMulRole → ℝ) : ∏ i, f i =
    f .v1 * (f .v2 * (f .v3 * (f .w1 * (f .v1' * (f .w2 * (f .v2' * (f .w3 * (f .w *
      f .u)))))))) := by
  rw [univ_roles]
  simp [Finset.prod_insert]

def one2 : Fin 2 → ℝ := fun _ => 1
def is2 (c : Fin 2) : Fin 2 → ℝ := fun a => if a = c then 1 else 0
def one3 : Tri → ℝ := fun _ => 1
def is3 (c : Tri) : Tri → ℝ := fun a => if a = c then 1 else 0

def fac (f1 f2 f3 f4 f5 f6 : Fin 2 → ℝ) (f7 : Tri → ℝ) (f8 f9 f10 : Fin 2 → ℝ) : Mix
  | .v1 => f1 | .v2 => f2 | .v3 => f3 | .w1 => f4 | .v1' => f5 | .w2 => f6 | .v2' => f7
  | .w3 => f8 | .w => f9 | .u => f10

lemma P_fac (f1 f2 f3 f4 f5 f6 : Fin 2 → ℝ) (f7 : Tri → ℝ) (f8 f9 f10 : Fin 2 → ℝ)
    (s : ∀ r, AddMulStrat r) :
    ∏ i, fac f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 i (s i) =
      f1 (s .v1) * (f2 (s .v2) * (f3 (s .v3) * (f4 (s .w1) * (f5 (s .v1') * (f6 (s .w2) *
        (f7 (s .v2') * (f8 (s .w3) * (f9 (s .w) * f10 (s .u))))))))) := by
  rw [prod10]; rfl

def Tv1 (τ : Mix) : Fin 2 → ℝ := τ .v1
def Tv2 (τ : Mix) : Fin 2 → ℝ := τ .v2
def Tv3 (τ : Mix) : Fin 2 → ℝ := τ .v3
def Tw1 (τ : Mix) : Fin 2 → ℝ := τ .w1
def Tv1' (τ : Mix) : Fin 2 → ℝ := τ .v1'
def Tw2 (τ : Mix) : Fin 2 → ℝ := τ .w2
def Tv2' (τ : Mix) : Tri → ℝ := τ .v2'
def Tw3 (τ : Mix) : Fin 2 → ℝ := τ .w3
def Tw (τ : Mix) : Fin 2 → ℝ := τ .w
def Tu (τ : Mix) : Fin 2 → ℝ := τ .u

lemma Tv1_ne (σ : Mix) (p : AddMulRole) (hp : AddMulRole.v1 ≠ p) (v : AddMulStrat p → ℝ) :
    Tv1 (Function.update σ p v) = Tv1 σ := by
  funext k; exact congrFun (Function.update_of_ne hp v σ) k
lemma Tv2_ne (σ : Mix) (p : AddMulRole) (hp : AddMulRole.v2 ≠ p) (v : AddMulStrat p → ℝ) :
    Tv2 (Function.update σ p v) = Tv2 σ := by
  funext k; exact congrFun (Function.update_of_ne hp v σ) k
lemma Tv3_ne (σ : Mix) (p : AddMulRole) (hp : AddMulRole.v3 ≠ p) (v : AddMulStrat p → ℝ) :
    Tv3 (Function.update σ p v) = Tv3 σ := by
  funext k; exact congrFun (Function.update_of_ne hp v σ) k
lemma Tw1_ne (σ : Mix) (p : AddMulRole) (hp : AddMulRole.w1 ≠ p) (v : AddMulStrat p → ℝ) :
    Tw1 (Function.update σ p v) = Tw1 σ := by
  funext k; exact congrFun (Function.update_of_ne hp v σ) k
lemma Tv1'_ne (σ : Mix) (p : AddMulRole) (hp : AddMulRole.v1' ≠ p) (v : AddMulStrat p → ℝ) :
    Tv1' (Function.update σ p v) = Tv1' σ := by
  funext k; exact congrFun (Function.update_of_ne hp v σ) k
lemma Tw2_ne (σ : Mix) (p : AddMulRole) (hp : AddMulRole.w2 ≠ p) (v : AddMulStrat p → ℝ) :
    Tw2 (Function.update σ p v) = Tw2 σ := by
  funext k; exact congrFun (Function.update_of_ne hp v σ) k
lemma Tv2'_ne (σ : Mix) (p : AddMulRole) (hp : AddMulRole.v2' ≠ p) (v : AddMulStrat p → ℝ) :
    Tv2' (Function.update σ p v) = Tv2' σ := by
  funext k; exact congrFun (Function.update_of_ne hp v σ) k
lemma Tw3_ne (σ : Mix) (p : AddMulRole) (hp : AddMulRole.w3 ≠ p) (v : AddMulStrat p → ℝ) :
    Tw3 (Function.update σ p v) = Tw3 σ := by
  funext k; exact congrFun (Function.update_of_ne hp v σ) k
lemma Tw_ne (σ : Mix) (p : AddMulRole) (hp : AddMulRole.w ≠ p) (v : AddMulStrat p → ℝ) :
    Tw (Function.update σ p v) = Tw σ := by
  funext k; exact congrFun (Function.update_of_ne hp v σ) k
lemma Tu_ne (σ : Mix) (p : AddMulRole) (hp : AddMulRole.u ≠ p) (v : AddMulStrat p → ℝ) :
    Tu (Function.update σ p v) = Tu σ := by
  funext k; exact congrFun (Function.update_of_ne hp v σ) k
lemma Tw1_same (σ : Mix) (j : Fin 2) :
    Tw1 (Function.update σ .w1
      (fun k => @ite ℝ (k = j) (AddMulStrat.instDecidableEq AddMulRole.w1 k j) 1 0)) =
      fun k => if k = j then 1 else 0 := by
  funext k; fin_cases j <;> fin_cases k <;> rfl
lemma Tv1'_same (σ : Mix) (j : Fin 2) :
    Tv1' (Function.update σ .v1'
      (fun k => @ite ℝ (k = j) (AddMulStrat.instDecidableEq AddMulRole.v1' k j) 1 0)) =
      fun k => if k = j then 1 else 0 := by
  funext k; fin_cases j <;> fin_cases k <;> rfl
lemma Tw2_same (σ : Mix) (j : Fin 2) :
    Tw2 (Function.update σ .w2
      (fun k => @ite ℝ (k = j) (AddMulStrat.instDecidableEq AddMulRole.w2 k j) 1 0)) =
      fun k => if k = j then 1 else 0 := by
  funext k; fin_cases j <;> fin_cases k <;> rfl
lemma Tv2'_same (σ : Mix) (j : Tri) :
    Tv2' (Function.update σ .v2'
      (fun k => @ite ℝ (k = j) (AddMulStrat.instDecidableEq AddMulRole.v2' k j) 1 0)) =
      fun k => if k = j then 1 else 0 := by
  funext k; cases j <;> cases k <;> rfl
lemma Tw_same (σ : Mix) (j : Fin 2) :
    Tw (Function.update σ .w
      (fun k => @ite ℝ (k = j) (AddMulStrat.instDecidableEq AddMulRole.w k j) 1 0)) =
      fun k => if k = j then 1 else 0 := by
  funext k; fin_cases j <;> fin_cases k <;> rfl
lemma Tu_same (σ : Mix) (j : Fin 2) :
    Tu (Function.update σ .u
      (fun k => @ite ℝ (k = j) (AddMulStrat.instDecidableEq AddMulRole.u k j) 1 0)) =
      fun k => if k = j then 1 else 0 := by
  funext k; fin_cases j <;> fin_cases k <;> rfl

lemma E_fac (τ : Mix) (f1 f2 f3 f4 f5 f6 : Fin 2 → ℝ) (f7 : Tri → ℝ) (f8 f9 f10 : Fin 2 → ℝ) :
    ∑ s : (∀ r, AddMulStrat r), (∏ i, τ i (s i)) * ∏ i, fac f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 i (s i)
      = (∑ a : Fin 2, Tv1 τ a * f1 a) * ((∑ a : Fin 2, Tv2 τ a * f2 a) * ((∑ a : Fin 2, Tv3 τ a * f3 a) *
        ((∑ a : Fin 2, Tw1 τ a * f4 a) * ((∑ a : Fin 2, Tv1' τ a * f5 a) * ((∑ a : Fin 2, Tw2 τ a * f6 a) *
        ((∑ a : Tri, Tv2' τ a * f7 a) * ((∑ a : Fin 2, Tw3 τ a * f8 a) * ((∑ a : Fin 2, Tw τ a * f9 a) *
        (∑ a : Fin 2, Tu τ a * f10 a))))))))) := by
  rw [prod_sum_mul, prod10]; rfl

lemma s_one2 {α : Type*} [Fintype α] (g : α → ℝ) (h : ∑ a, g a = 1) :
    ∑ a, g a * (fun _ => (1 : ℝ)) a = 1 := by simpa using h


lemma fin2 (a : Fin 2) : a = 0 ∨ a = 1 := by fin_cases a <;> simp
lemma tri3 (a : Tri) : a = .zero ∨ a = .one ∨ a = .star := by cases a <;> simp

lemma sum_cmul {X : Type*} [Fintype X] (P A : X → ℝ) (c : ℝ) :
    ∑ s, P s * (c * A s) = c * ∑ s, P s * A s := by
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun s _ => by ring

lemma sum_is {α : Type*} [Fintype α] [DecidableEq α] (g : α → ℝ) (c : α) :
    ∑ a, g a * (if a = c then 1 else 0) = g c := by
  simp [mul_ite]

variable (α β γ : ℕ)

lemma sum_three_of {X : Type*} [Fintype X] [DecidableEq X] (f : X → ℝ) (a b c : X)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hall : ∀ d, d = a ∨ d = b ∨ d = c) : ∑ d, f d = f a + f b + f c := by
  have : (Finset.univ : Finset X) = {a, b, c} := by
    ext d; simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact hall d
  rw [this, Finset.sum_insert (by simp [hab, hac]), Finset.sum_pair hbc, add_assoc]

lemma s1 (g : Fin 2 → ℝ) : ∑ a, g a * one2 a = ∑ a, g a := by simp [one2]
lemma s1t (g : Tri → ℝ) : ∑ a, g a * one3 a = ∑ a, g a := by simp [one3]
lemma s2 (g : Fin 2 → ℝ) (c : Fin 2) : ∑ a, g a * is2 c a = g c := by
  fin_cases c <;> simp [is2, Fin.sum_univ_two]
lemma s3 (g : Tri → ℝ) (c : Tri) : ∑ a, g a * is3 c a = g c := by
  rw [sum_three_of _ Tri.zero Tri.one Tri.star (by decide) (by decide) (by decide) tri3]
  cases c <;> simp [is3]

lemma lots (τ : Mix) (hτ : ∀ r, ∑ a, τ r a = 1) :
    (∑ a, Tv1 τ a = 1) ∧ (∑ a, Tv2 τ a = 1) ∧ (∑ a, Tv3 τ a = 1) ∧
    (∑ a, Tw1 τ a = 1) ∧ (∑ a, Tv1' τ a = 1) ∧ (∑ a, Tw2 τ a = 1) ∧
    (∑ a, Tv2' τ a = 1) ∧ (∑ a, Tw3 τ a = 1) ∧ (∑ a, Tw τ a = 1) ∧
    (∑ a, Tu τ a = 1) :=
  ⟨hτ .v1, hτ .v2, hτ .v3, hτ .w1, hτ .v1', hτ .w2, hτ .v2', hτ .w3, hτ .w, hτ .u⟩

lemma pay_w1 (s : ∀ r, AddMulStrat r) : addMulPayoff α β γ .w1 s =
    (1/8 : ℝ) * ∏ i, fac (is2 1) one2 one2 (is2 0) one2 one2 one3 one2 one2 one2 i (s i)
    + ∏ i, fac one2 one2 one2 (is2 1) (is2 1) one2 one3 one2 one2 one2 i (s i) := by
  rw [P_fac, P_fac]
  simp only [one2, is2, one3, addMulPayoff, ind]
  rcases fin2 (s .w1) with h | h <;> rcases fin2 (s .v1) with h' | h' <;>
    rcases fin2 (s .v1') with h'' | h'' <;> simp [h, h', h'']

lemma E_w1 (τ : Mix) (hτ : ∀ r, ∑ a, τ r a = 1) :
    AGT.expectedPayoff (addMulPayoff α β γ) τ .w1 =
      (1/8 : ℝ) * (Tv1 τ 1 * Tw1 τ 0) + Tw1 τ 1 * Tv1' τ 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := lots τ hτ
  unfold AGT.expectedPayoff AGT.profileProb
  simp only [pay_w1, mul_add, Finset.sum_add_distrib, sum_cmul, E_fac]
  simp only [s1, s1t, s2, s3, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  ring

lemma pay_v1' (s : ∀ r, AddMulStrat r) : addMulPayoff α β γ .v1' s =
    ∏ i, fac one2 one2 one2 (is2 1) (is2 0) one2 one3 one2 one2 one2 i (s i)
    + ∏ i, fac one2 one2 one2 (is2 0) (is2 1) one2 one3 one2 one2 one2 i (s i) := by
  rw [P_fac, P_fac]
  simp only [one2, is2, one3, addMulPayoff, ind]
  rcases fin2 (s .w1) with h | h <;> rcases fin2 (s .v1') with h'' | h'' <;> simp [h, h'']

lemma E_v1' (τ : Mix) (hτ : ∀ r, ∑ a, τ r a = 1) :
    AGT.expectedPayoff (addMulPayoff α β γ) τ .v1' =
      Tw1 τ 1 * Tv1' τ 0 + Tw1 τ 0 * Tv1' τ 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := lots τ hτ
  unfold AGT.expectedPayoff AGT.profileProb
  simp only [pay_v1', mul_add, Finset.sum_add_distrib, sum_cmul, E_fac]
  simp only [s1, s1t, s2, s3, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  ring

lemma pay_w2 (s : ∀ r, AddMulStrat r) : addMulPayoff α β γ .w2 s =
    (1/8 : ℝ) * ∏ i, fac one2 (is2 1) one2 one2 one2 (is2 0) one3 one2 one2 one2 i (s i)
    + ∏ i, fac one2 one2 one2 one2 one2 (is2 1) (is3 .one) one2 one2 one2 i (s i) := by
  rw [P_fac, P_fac]
  simp only [one2, is2, one3, is3, addMulPayoff, ind]
  rcases fin2 (s .w2) with h | h <;> rcases fin2 (s .v2) with h' | h' <;>
    rcases tri3 (s .v2') with h'' | h'' | h'' <;> simp [h, h', h'']

lemma E_w2 (τ : Mix) (hτ : ∀ r, ∑ a, τ r a = 1) :
    AGT.expectedPayoff (addMulPayoff α β γ) τ .w2 =
      (1/8 : ℝ) * (Tv2 τ 1 * Tw2 τ 0) + Tw2 τ 1 * Tv2' τ .one := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := lots τ hτ
  unfold AGT.expectedPayoff AGT.profileProb
  simp only [pay_w2, mul_add, Finset.sum_add_distrib, sum_cmul, E_fac]
  simp only [s1, s1t, s2, s3, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  ring

lemma pay_v2' (s : ∀ r, AddMulStrat r) : addMulPayoff α β γ .v2' s =
    ∏ i, fac one2 one2 one2 one2 one2 (is2 1) (is3 .zero) one2 one2 (is2 0) i (s i)
    + ∏ i, fac one2 one2 one2 one2 one2 (is2 0) (is3 .one) one2 one2 one2 i (s i)
    + ∏ i, fac one2 one2 one2 one2 one2 (is2 1) (is3 .star) one2 one2 (is2 1) i (s i) := by
  rw [P_fac, P_fac, P_fac]
  simp only [one2, is2, one3, is3, addMulPayoff, ind]
  rcases fin2 (s .w2) with h | h <;> rcases fin2 (s .u) with h' | h' <;>
    rcases tri3 (s .v2') with h'' | h'' | h'' <;> simp [h, h', h'']

lemma E_v2' (τ : Mix) (hτ : ∀ r, ∑ a, τ r a = 1) :
    AGT.expectedPayoff (addMulPayoff α β γ) τ .v2' =
      Tw2 τ 1 * Tv2' τ .zero * Tu τ 0 + Tw2 τ 0 * Tv2' τ .one
        + Tw2 τ 1 * Tv2' τ .star * Tu τ 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := lots τ hτ
  unfold AGT.expectedPayoff AGT.profileProb
  simp only [pay_v2', mul_add, Finset.sum_add_distrib, sum_cmul, E_fac]
  simp only [s1, s1t, s2, s3, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  ring

lemma pay_w (s : ∀ r, AddMulStrat r) : addMulPayoff α β γ .w s =
    (α : ℝ) * ∏ i, fac one2 one2 one2 one2 (is2 1) one2 one3 one2 (is2 0) one2 i (s i)
    + (1 + (β : ℝ)) * ∏ i, fac one2 one2 one2 one2 one2 one2 (is3 .one) one2 (is2 0) one2 i (s i)
    + (8 * (γ : ℝ)) * ∏ i, fac one2 one2 one2 one2 (is2 1) one2 (is3 .one) one2 (is2 0) one2 i (s i)
    + ∏ i, fac one2 one2 one2 one2 one2 one2 (is3 .one) one2 (is2 1) one2 i (s i)
    + ∏ i, fac one2 one2 one2 one2 one2 one2 (is3 .star) one2 (is2 1) one2 i (s i) := by
  rw [P_fac, P_fac, P_fac, P_fac, P_fac]
  simp only [one2, is2, one3, is3, addMulPayoff, ind]
  rcases fin2 (s .w) with h | h <;> rcases fin2 (s .v1') with h' | h' <;>
    rcases tri3 (s .v2') with h'' | h'' | h'' <;> simp [h, h', h''] <;> ring

lemma E_w (τ : Mix) (hτ : ∀ r, ∑ a, τ r a = 1) :
    AGT.expectedPayoff (addMulPayoff α β γ) τ .w =
      (α : ℝ) * (Tv1' τ 1 * Tw τ 0) + (1 + (β : ℝ)) * (Tv2' τ .one * Tw τ 0)
        + 8 * (γ : ℝ) * (Tv1' τ 1 * Tv2' τ .one * Tw τ 0)
        + Tv2' τ .one * Tw τ 1 + Tv2' τ .star * Tw τ 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := lots τ hτ
  unfold AGT.expectedPayoff AGT.profileProb
  simp only [pay_w, mul_add, Finset.sum_add_distrib, sum_cmul, E_fac]
  simp only [s1, s1t, s2, s3, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  ring

lemma pay_u (s : ∀ r, AddMulStrat r) : addMulPayoff α β γ .u s =
    ∏ i, fac one2 one2 one2 one2 one2 one2 one3 one2 (is2 1) (is2 0) i (s i)
    + ∏ i, fac one2 one2 one2 one2 one2 one2 one3 one2 (is2 0) (is2 1) i (s i) := by
  rw [P_fac, P_fac]
  simp only [one2, is2, one3, addMulPayoff, ind]
  rcases fin2 (s .w) with h | h <;> rcases fin2 (s .u) with h'' | h'' <;> simp [h, h'']

lemma E_u (τ : Mix) (hτ : ∀ r, ∑ a, τ r a = 1) :
    AGT.expectedPayoff (addMulPayoff α β γ) τ .u =
      Tw τ 1 * Tu τ 0 + Tw τ 0 * Tu τ 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := lots τ hτ
  unfold AGT.expectedPayoff AGT.profileProb
  simp only [pay_u, mul_add, Finset.sum_add_distrib, sum_cmul, E_fac]
  simp only [s1, s1t, s2, s3, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  ring

lemma upd_lot (σ : Mix) (hσ : AGT.IsMixedProfile σ) (p : AddMulRole) (j : AddMulStrat p)
    (r : AddMulRole) :
    ∑ a, (Function.update σ p (fun k => if k = j then (1 : ℝ) else 0)) r a = 1 := by
  by_cases h : r = p
  · subst h; simp
  · rw [Function.update_of_ne h]; exact (hσ r).2

lemma sum_two_of {X : Type*} [Fintype X] (f : X → ℝ) (a b : X) (hab : a ≠ b)
    (hall : ∀ c, c = a ∨ c = b) : ∑ c, f c = f a + f b :=
  Fintype.sum_eq_add a b hab (fun c hc => absurd (hall c) (by tauto))


theorem main (α β γ : ℕ) (hαβγ : α + β + γ ≤ 3) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / 100) (σ : ∀ r, AddMulStrat r → ℝ) (hσ : IsEpsNash (addMulPayoff α β γ) ε σ) :
    |σ .v2' Tri.star - ((α : ℝ) / 8 * σ .v1 (1 : Fin 2) + (β : ℝ) / 8 * σ .v2 (1 : Fin 2)
        + (γ : ℝ) / 8 * σ .v1 (1 : Fin 2) * σ .v2 (1 : Fin 2))| ≤ 10 * ε := by
  obtain ⟨hmix, hws⟩ := hσ
  have nn : ∀ r a, 0 ≤ σ r a := fun r => (hmix r).1
  have Pw1_0 : DGPNash.NashMap.purePayoff (addMulPayoff α β γ) σ .w1 (0 : Fin 2) = σ .v1 (1 : Fin 2) / 8 := by
    unfold DGPNash.NashMap.purePayoff
    refine (E_w1 α β γ _ (upd_lot σ hmix _ _)).trans ?_
    rw [Tw1_same σ (0 : Fin 2)]
    simp only [Tv1_ne, Tv2_ne, Tv3_ne, Tw1_ne, Tv1'_ne, Tw2_ne, Tv2'_ne, Tw3_ne, Tw_ne, Tu_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    simp [Tv1, Tv2, Tv3, Tw1, Tv1', Tw2, Tv2', Tw3, Tw, Tu] <;> ring
  have Pw1_1 : DGPNash.NashMap.purePayoff (addMulPayoff α β γ) σ .w1 (1 : Fin 2) = σ .v1' (1 : Fin 2) := by
    unfold DGPNash.NashMap.purePayoff
    refine (E_w1 α β γ _ (upd_lot σ hmix _ _)).trans ?_
    rw [Tw1_same σ (1 : Fin 2)]
    simp only [Tv1_ne, Tv2_ne, Tv3_ne, Tw1_ne, Tv1'_ne, Tw2_ne, Tv2'_ne, Tw3_ne, Tw_ne, Tu_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    simp [Tv1, Tv2, Tv3, Tw1, Tv1', Tw2, Tv2', Tw3, Tw, Tu] <;> ring
  have Pv1_0 : DGPNash.NashMap.purePayoff (addMulPayoff α β γ) σ .v1' (0 : Fin 2) = σ .w1 (1 : Fin 2) := by
    unfold DGPNash.NashMap.purePayoff
    refine (E_v1' α β γ _ (upd_lot σ hmix _ _)).trans ?_
    rw [Tv1'_same σ (0 : Fin 2)]
    simp only [Tv1_ne, Tv2_ne, Tv3_ne, Tw1_ne, Tv1'_ne, Tw2_ne, Tv2'_ne, Tw3_ne, Tw_ne, Tu_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    simp [Tv1, Tv2, Tv3, Tw1, Tv1', Tw2, Tv2', Tw3, Tw, Tu] <;> ring
  have Pv1_1 : DGPNash.NashMap.purePayoff (addMulPayoff α β γ) σ .v1' (1 : Fin 2) = σ .w1 (0 : Fin 2) := by
    unfold DGPNash.NashMap.purePayoff
    refine (E_v1' α β γ _ (upd_lot σ hmix _ _)).trans ?_
    rw [Tv1'_same σ (1 : Fin 2)]
    simp only [Tv1_ne, Tv2_ne, Tv3_ne, Tw1_ne, Tv1'_ne, Tw2_ne, Tv2'_ne, Tw3_ne, Tw_ne, Tu_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    simp [Tv1, Tv2, Tv3, Tw1, Tv1', Tw2, Tv2', Tw3, Tw, Tu] <;> ring
  have Pw2_0 : DGPNash.NashMap.purePayoff (addMulPayoff α β γ) σ .w2 (0 : Fin 2) = σ .v2 (1 : Fin 2) / 8 := by
    unfold DGPNash.NashMap.purePayoff
    refine (E_w2 α β γ _ (upd_lot σ hmix _ _)).trans ?_
    rw [Tw2_same σ (0 : Fin 2)]
    simp only [Tv1_ne, Tv2_ne, Tv3_ne, Tw1_ne, Tv1'_ne, Tw2_ne, Tv2'_ne, Tw3_ne, Tw_ne, Tu_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    simp [Tv1, Tv2, Tv3, Tw1, Tv1', Tw2, Tv2', Tw3, Tw, Tu] <;> ring
  have Pw2_1 : DGPNash.NashMap.purePayoff (addMulPayoff α β γ) σ .w2 (1 : Fin 2) = σ .v2' Tri.one := by
    unfold DGPNash.NashMap.purePayoff
    refine (E_w2 α β γ _ (upd_lot σ hmix _ _)).trans ?_
    rw [Tw2_same σ (1 : Fin 2)]
    simp only [Tv1_ne, Tv2_ne, Tv3_ne, Tw1_ne, Tv1'_ne, Tw2_ne, Tv2'_ne, Tw3_ne, Tw_ne, Tu_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    simp [Tv1, Tv2, Tv3, Tw1, Tv1', Tw2, Tv2', Tw3, Tw, Tu] <;> ring
  have Pz : DGPNash.NashMap.purePayoff (addMulPayoff α β γ) σ .v2' Tri.zero = σ .w2 (1 : Fin 2) * σ .u (0 : Fin 2) := by
    unfold DGPNash.NashMap.purePayoff
    refine (E_v2' α β γ _ (upd_lot σ hmix _ _)).trans ?_
    rw [Tv2'_same σ Tri.zero]
    simp only [Tv1_ne, Tv2_ne, Tv3_ne, Tw1_ne, Tv1'_ne, Tw2_ne, Tv2'_ne, Tw3_ne, Tw_ne, Tu_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    simp [Tv1, Tv2, Tv3, Tw1, Tv1', Tw2, Tv2', Tw3, Tw, Tu] <;> ring
  have Po : DGPNash.NashMap.purePayoff (addMulPayoff α β γ) σ .v2' Tri.one = σ .w2 (0 : Fin 2) := by
    unfold DGPNash.NashMap.purePayoff
    refine (E_v2' α β γ _ (upd_lot σ hmix _ _)).trans ?_
    rw [Tv2'_same σ Tri.one]
    simp only [Tv1_ne, Tv2_ne, Tv3_ne, Tw1_ne, Tv1'_ne, Tw2_ne, Tv2'_ne, Tw3_ne, Tw_ne, Tu_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    simp [Tv1, Tv2, Tv3, Tw1, Tv1', Tw2, Tv2', Tw3, Tw, Tu] <;> ring
  have Ps : DGPNash.NashMap.purePayoff (addMulPayoff α β γ) σ .v2' Tri.star = σ .w2 (1 : Fin 2) * σ .u (1 : Fin 2) := by
    unfold DGPNash.NashMap.purePayoff
    refine (E_v2' α β γ _ (upd_lot σ hmix _ _)).trans ?_
    rw [Tv2'_same σ Tri.star]
    simp only [Tv1_ne, Tv2_ne, Tv3_ne, Tw1_ne, Tv1'_ne, Tw2_ne, Tv2'_ne, Tw3_ne, Tw_ne, Tu_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    simp [Tv1, Tv2, Tv3, Tw1, Tv1', Tw2, Tv2', Tw3, Tw, Tu] <;> ring
  have Pw_0 : DGPNash.NashMap.purePayoff (addMulPayoff α β γ) σ .w (0 : Fin 2) = (α : ℝ) * σ .v1' (1 : Fin 2) + (1 + (β : ℝ)) * σ .v2' Tri.one + 8 * (γ : ℝ) * (σ .v1' (1 : Fin 2) * σ .v2' Tri.one) := by
    unfold DGPNash.NashMap.purePayoff
    refine (E_w α β γ _ (upd_lot σ hmix _ _)).trans ?_
    rw [Tw_same σ (0 : Fin 2)]
    simp only [Tv1_ne, Tv2_ne, Tv3_ne, Tw1_ne, Tv1'_ne, Tw2_ne, Tv2'_ne, Tw3_ne, Tw_ne, Tu_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    simp [Tv1, Tv2, Tv3, Tw1, Tv1', Tw2, Tv2', Tw3, Tw, Tu] <;> ring
  have Pw_1 : DGPNash.NashMap.purePayoff (addMulPayoff α β γ) σ .w (1 : Fin 2) = σ .v2' Tri.one + σ .v2' Tri.star := by
    unfold DGPNash.NashMap.purePayoff
    refine (E_w α β γ _ (upd_lot σ hmix _ _)).trans ?_
    rw [Tw_same σ (1 : Fin 2)]
    simp only [Tv1_ne, Tv2_ne, Tv3_ne, Tw1_ne, Tv1'_ne, Tw2_ne, Tv2'_ne, Tw3_ne, Tw_ne, Tu_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    simp [Tv1, Tv2, Tv3, Tw1, Tv1', Tw2, Tv2', Tw3, Tw, Tu] <;> ring
  have Pu_0 : DGPNash.NashMap.purePayoff (addMulPayoff α β γ) σ .u (0 : Fin 2) = σ .w (1 : Fin 2) := by
    unfold DGPNash.NashMap.purePayoff
    refine (E_u α β γ _ (upd_lot σ hmix _ _)).trans ?_
    rw [Tu_same σ (0 : Fin 2)]
    simp only [Tv1_ne, Tv2_ne, Tv3_ne, Tw1_ne, Tv1'_ne, Tw2_ne, Tv2'_ne, Tw3_ne, Tw_ne, Tu_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    simp [Tv1, Tv2, Tv3, Tw1, Tv1', Tw2, Tv2', Tw3, Tw, Tu] <;> ring
  have Pu_1 : DGPNash.NashMap.purePayoff (addMulPayoff α β γ) σ .u (1 : Fin 2) = σ .w (0 : Fin 2) := by
    unfold DGPNash.NashMap.purePayoff
    refine (E_u α β γ _ (upd_lot σ hmix _ _)).trans ?_
    rw [Tu_same σ (1 : Fin 2)]
    simp only [Tv1_ne, Tv2_ne, Tv3_ne, Tw1_ne, Tv1'_ne, Tw2_ne, Tv2'_ne, Tw3_ne, Tw_ne, Tu_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    simp [Tv1, Tv2, Tv3, Tw1, Tv1', Tw2, Tv2', Tw3, Tw, Tu] <;> ring

  have sv1 : σ .v1 (0 : Fin 2) + σ .v1 (1 : Fin 2) = 1 := by
    rw [← sum_two_of (σ .v1) (0 : Fin 2) (1 : Fin 2) (show (0 : Fin 2) ≠ 1 by decide) fin2]; exact (hmix .v1).2
  have sv2 : σ .v2 (0 : Fin 2) + σ .v2 (1 : Fin 2) = 1 := by
    rw [← sum_two_of (σ .v2) (0 : Fin 2) (1 : Fin 2) (show (0 : Fin 2) ≠ 1 by decide) fin2]; exact (hmix .v2).2
  have sw1 : σ .w1 (0 : Fin 2) + σ .w1 (1 : Fin 2) = 1 := by
    rw [← sum_two_of (σ .w1) (0 : Fin 2) (1 : Fin 2) (show (0 : Fin 2) ≠ 1 by decide) fin2]; exact (hmix .w1).2
  have sv1' : σ .v1' (0 : Fin 2) + σ .v1' (1 : Fin 2) = 1 := by
    rw [← sum_two_of (σ .v1') (0 : Fin 2) (1 : Fin 2) (show (0 : Fin 2) ≠ 1 by decide) fin2]; exact (hmix .v1').2
  have sw2 : σ .w2 (0 : Fin 2) + σ .w2 (1 : Fin 2) = 1 := by
    rw [← sum_two_of (σ .w2) (0 : Fin 2) (1 : Fin 2) (show (0 : Fin 2) ≠ 1 by decide) fin2]; exact (hmix .w2).2
  have sw : σ .w (0 : Fin 2) + σ .w (1 : Fin 2) = 1 := by
    rw [← sum_two_of (σ .w) (0 : Fin 2) (1 : Fin 2) (show (0 : Fin 2) ≠ 1 by decide) fin2]; exact (hmix .w).2
  have su : σ .u (0 : Fin 2) + σ .u (1 : Fin 2) = 1 := by
    rw [← sum_two_of (σ .u) (0 : Fin 2) (1 : Fin 2) (show (0 : Fin 2) ≠ 1 by decide) fin2]; exact (hmix .u).2
  have sv2' : σ .v2' Tri.zero + σ .v2' Tri.one + σ .v2' Tri.star = 1 := by
    rw [← sum_three_of (σ .v2') Tri.zero Tri.one Tri.star (show Tri.zero ≠ Tri.one by decide)
      (show Tri.zero ≠ Tri.star by decide) (show Tri.one ≠ Tri.star by decide) tri3]
    exact (hmix .v2').2
  have x0 := nn .v1 (0 : Fin 2); have x1 := nn .v1 (1 : Fin 2)
  have y0 := nn .v2 (0 : Fin 2); have y1 := nn .v2 (1 : Fin 2)
  have a0 := nn .v1' (0 : Fin 2); have a1 := nn .v1' (1 : Fin 2)
  have w10 := nn .w1 (0 : Fin 2); have w11 := nn .w1 (1 : Fin 2)
  have w20 := nn .w2 (0 : Fin 2); have w21 := nn .w2 (1 : Fin 2)
  have ww0 := nn .w (0 : Fin 2); have ww1 := nn .w (1 : Fin 2)
  have u0 := nn .u (0 : Fin 2); have u1 := nn .u (1 : Fin 2)
  have tz := nn .v2' Tri.zero; have hto := nn .v2' Tri.one; have ts := nn .v2' Tri.star
  have hA : (0 : ℝ) ≤ α := Nat.cast_nonneg α
  have hB : (0 : ℝ) ≤ β := Nat.cast_nonneg β
  have hC : (0 : ℝ) ≤ γ := Nat.cast_nonneg γ
  have h3 : (α : ℝ) + β + γ ≤ 3 := by exact_mod_cast hαβγ
  -- Claim 1
  have c1 : |σ .v1' (1 : Fin 2) - σ .v1 (1 : Fin 2) / 8| ≤ ε := by
    rw [abs_le]; constructor
    · by_contra hc; push_neg at hc
      have e1 : σ .w1 (1 : Fin 2) = 0 :=
        hws .w1 (0 : Fin 2) (1 : Fin 2) (by rw [Pw1_0, Pw1_1]; linarith)
      have e2 : σ .v1' (0 : Fin 2) = 0 :=
        hws .v1' (1 : Fin 2) (0 : Fin 2) (by rw [Pv1_0, Pv1_1]; linarith)
      linarith
    · by_contra hc; push_neg at hc
      have e1 : σ .w1 (0 : Fin 2) = 0 :=
        hws .w1 (1 : Fin 2) (0 : Fin 2) (by rw [Pw1_0, Pw1_1]; linarith)
      have e2 : σ .v1' (1 : Fin 2) = 0 :=
        hws .v1' (0 : Fin 2) (1 : Fin 2) (by rw [Pv1_0, Pv1_1]; linarith)
      linarith
  -- Claim 2
  have c2 : |σ .v2' Tri.one - σ .v2 (1 : Fin 2) / 8| ≤ ε := by
    rw [abs_le]; constructor
    · by_contra hc; push_neg at hc
      have e1 : σ .w2 (1 : Fin 2) = 0 :=
        hws .w2 (0 : Fin 2) (1 : Fin 2) (by rw [Pw2_0, Pw2_1]; linarith)
      have e2 : σ .v2' Tri.zero = 0 :=
        hws .v2' Tri.one Tri.zero (by rw [Po, Pz, e1]; linarith)
      have e3 : σ .v2' Tri.star = 0 :=
        hws .v2' Tri.one Tri.star (by rw [Po, Ps, e1]; linarith)
      linarith
    · by_contra hc; push_neg at hc
      have e1 : σ .w2 (0 : Fin 2) = 0 :=
        hws .w2 (1 : Fin 2) (0 : Fin 2) (by rw [Pw2_0, Pw2_1]; linarith)
      have e1' : σ .w2 (1 : Fin 2) = 1 := by linarith
      rcases le_or_gt (1 / 2) (σ .u (0 : Fin 2)) with hu | hu
      · have e2 : σ .v2' Tri.one = 0 :=
          hws .v2' Tri.zero Tri.one (by rw [Po, Pz, e1, e1']; linarith)
        linarith
      · have e2 : σ .v2' Tri.one = 0 :=
          hws .v2' Tri.star Tri.one (by rw [Po, Ps, e1, e1']; linarith)
        linarith
  have c1' := abs_le.mp c1
  have c2' := abs_le.mp c2
  have ha : σ .v1' (1 : Fin 2) ≤ 27 / 200 := by linarith
  have hb : σ .v2' Tri.one ≤ 27 / 200 := by linarith
  have Aa : (α : ℝ) * σ .v1' (1 : Fin 2) ≤ (α : ℝ) * (27 / 200) := mul_le_mul_of_nonneg_left ha hA
  have Bb : (β : ℝ) * σ .v2' Tri.one ≤ (β : ℝ) * (27 / 200) := mul_le_mul_of_nonneg_left hb hB
  have ab : σ .v1' (1 : Fin 2) * σ .v2' Tri.one ≤ (27 / 200) * (27 / 200) :=
    mul_le_mul ha hb hto (by norm_num)
  have Cab : (γ : ℝ) * (σ .v1' (1 : Fin 2) * σ .v2' Tri.one) ≤ (γ : ℝ) * ((27 / 200) * (27 / 200)) :=
    mul_le_mul_of_nonneg_left ab hC
  have Aa0 : 0 ≤ (α : ℝ) * σ .v1' (1 : Fin 2) := mul_nonneg hA a1
  have Bb0 : 0 ≤ (β : ℝ) * σ .v2' Tri.one := mul_nonneg hB hto
  have Cab0 : 0 ≤ (γ : ℝ) * (σ .v1' (1 : Fin 2) * σ .v2' Tri.one) := mul_nonneg hC (mul_nonneg a1 hto)
  -- Claim 3
  have c3 : |σ .v2' Tri.star - ((α : ℝ) * σ .v1' (1 : Fin 2) + (β : ℝ) * σ .v2' Tri.one
      + 8 * (γ : ℝ) * (σ .v1' (1 : Fin 2) * σ .v2' Tri.one))| ≤ ε := by
    rw [abs_le]; constructor
    · by_contra hc; push_neg at hc
      have e1 : σ .w (1 : Fin 2) = 0 :=
        hws .w (0 : Fin 2) (1 : Fin 2) (by rw [Pw_0, Pw_1]; linarith)
      have e1' : σ .w (0 : Fin 2) = 1 := by linarith
      have e2 : σ .u (0 : Fin 2) = 0 :=
        hws .u (1 : Fin 2) (0 : Fin 2) (by rw [Pu_0, Pu_1, e1, e1']; linarith)
      have e2' : σ .u (1 : Fin 2) = 1 := by linarith
      have e3 : σ .v2' Tri.zero = 0 := by
        rcases le_or_gt (1 / 2) (σ .w2 (0 : Fin 2)) with hw | hw
        · exact hws .v2' Tri.one Tri.zero (by rw [Po, Pz, e2]; linarith)
        · exact hws .v2' Tri.star Tri.zero (by rw [Ps, Pz, e2, e2']; linarith)
      linarith
    · by_contra hc; push_neg at hc
      have e1 : σ .w (0 : Fin 2) = 0 :=
        hws .w (1 : Fin 2) (0 : Fin 2) (by rw [Pw_0, Pw_1]; linarith)
      have e1' : σ .w (1 : Fin 2) = 1 := by linarith
      have e2 : σ .u (1 : Fin 2) = 0 :=
        hws .u (0 : Fin 2) (1 : Fin 2) (by rw [Pu_0, Pu_1, e1, e1']; linarith)
      have e2' : σ .u (0 : Fin 2) = 1 := by linarith
      have e3 : σ .v2' Tri.star = 0 := by
        rcases le_or_gt (1 / 2) (σ .w2 (0 : Fin 2)) with hw | hw
        · exact hws .v2' Tri.one Tri.star (by rw [Po, Ps, e2]; linarith)
        · exact hws .v2' Tri.zero Tri.star (by rw [Ps, Pz, e2, e2']; linarith)
      linarith
  have c3' := abs_le.mp c3
  -- combine
  have x1le : σ .v1 (1 : Fin 2) ≤ 1 := by linarith
  have y1le : σ .v2 (1 : Fin 2) ≤ 1 := by linarith
  have e1 := mul_le_mul_of_nonneg_left c1'.2 hA
  have e1' := mul_le_mul_of_nonneg_left c1'.1 hA
  have e2 := mul_le_mul_of_nonneg_left c2'.2 hB
  have e2' := mul_le_mul_of_nonneg_left c2'.1 hB
  have Ca0 : 0 ≤ (γ : ℝ) * σ .v1' (1 : Fin 2) := mul_nonneg hC a1
  have Cy0 : 0 ≤ (γ : ℝ) * σ .v2 (1 : Fin 2) := mul_nonneg hC y1
  have e3 := mul_le_mul_of_nonneg_left c2'.2 Ca0
  have e3' := mul_le_mul_of_nonneg_left c2'.1 Ca0
  have e4 := mul_le_mul_of_nonneg_left c1'.2 Cy0
  have e4' := mul_le_mul_of_nonneg_left c1'.1 Cy0
  have e5 : (γ : ℝ) * σ .v1' (1 : Fin 2) * ε ≤ (γ : ℝ) * (27 / 200) * ε :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ha hC) hε0
  have e6 : (γ : ℝ) * σ .v2 (1 : Fin 2) * ε ≤ (γ : ℝ) * 1 * ε :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left y1le hC) hε0
  have e7 : ((α : ℝ) + β + γ) * ε ≤ 3 * ε := mul_le_mul_of_nonneg_right h3 hε0
  have Ae : 0 ≤ (α : ℝ) * ε := mul_nonneg hA hε0
  have Be : 0 ≤ (β : ℝ) * ε := mul_nonneg hB hε0
  have Ce : 0 ≤ (γ : ℝ) * ε := mul_nonneg hC hε0
  rw [abs_le]; constructor <;> linarith

end Df66664d

open DGPNash.Gadget in
theorem solution (α β γ : ℕ) (hαβγ : α + β + γ ≤ 3) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / 100) (σ : ∀ r, AddMulStrat r → ℝ) (hσ : IsEpsNash (addMulPayoff α β γ) ε σ) :
    |σ .v2' Tri.star - ((α : ℝ) / 8 * σ .v1 (1 : Fin 2) + (β : ℝ) / 8 * σ .v2 (1 : Fin 2)
        + (γ : ℝ) / 8 * σ .v1 (1 : Fin 2) * σ .v2 (1 : Fin 2))| ≤ 10 * ε := by
  exact Df66664d.main α β γ hαβγ ε hε0 hε σ hσ

