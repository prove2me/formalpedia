-- Prove2me | solution 2 for DGPNash.Gadget.addMulGadget_error_amplification
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T07:10:53.734191+00:00
-- url     : https://prove2.me/submissions/f1895545-9692-4784-bcc9-e00cefbe933e

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_Gadget_EpsNash
import Definitions.Def_DGPNash_Gadget_AffectsGraph
import Definitions.Def_DGPNash_Gadget_AddMulGame
import Theorems.Thm_DGPNash_Gadget_claim3_v2prime_star

-- carved verbatim out of submission a62c2782-4252-4629-a1f2-9dd290feceb5, lines 691-698

section
set_option autoImplicit false
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

lemma E_fac (τ : Mix) (f1 f2 f3 f4 f5 f6 : Fin 2 → ℝ) (f7 : Tri → ℝ) (f8 f9 f10 : Fin 2 → ℝ) :
    ∑ s : (∀ r, AddMulStrat r), (∏ i, τ i (s i)) * ∏ i, fac f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 i (s i)
      = (∑ a : Fin 2, Tv1 τ a * f1 a) * ((∑ a : Fin 2, Tv2 τ a * f2 a) * ((∑ a : Fin 2, Tv3 τ a * f3 a) *
        ((∑ a : Fin 2, Tw1 τ a * f4 a) * ((∑ a : Fin 2, Tv1' τ a * f5 a) * ((∑ a : Fin 2, Tw2 τ a * f6 a) *
        ((∑ a : Tri, Tv2' τ a * f7 a) * ((∑ a : Fin 2, Tw3 τ a * f8 a) * ((∑ a : Fin 2, Tw τ a * f9 a) *
        (∑ a : Fin 2, Tu τ a * f10 a))))))))) := by
  rw [prod_sum_mul, prod10]; rfl

lemma fin2 (a : Fin 2) : a = 0 ∨ a = 1 := by fin_cases a <;> simp

lemma tri3 (a : Tri) : a = .zero ∨ a = .one ∨ a = .star := by cases a <;> simp

lemma sum_cmul {X : Type*} [Fintype X] (P A : X → ℝ) (c : ℝ) :
    ∑ s, P s * (c * A s) = c * ∑ s, P s * A s := by
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun s _ => by ring

end

section
set_option autoImplicit false
open DGPNash.Gadget
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

lemma upd_lot (σ : Mix) (hσ : AGT.IsMixedProfile σ) (p : AddMulRole) (j : AddMulStrat p)
    (r : AddMulRole) :
    ∑ a, (Function.update σ p (fun k => if k = j then (1 : ℝ) else 0)) r a = 1 := by
  by_cases h : r = p
  · subst h; simp
  · rw [Function.update_of_ne h]; exact (hσ r).2

lemma sum_two_of {X : Type*} [Fintype X] (f : X → ℝ) (a b : X) (hab : a ≠ b)
    (hall : ∀ c, c = a ∨ c = b) : ∑ c, f c = f a + f b :=
  Fintype.sum_eq_add a b hab (fun c hc => absurd (hall c) (by tauto))

end

section
set_option autoImplicit false
open DGPNash.Gadget

lemma Tw3_same (σ : Mix) (j : Fin 2) :
    Tw3 (Function.update σ .w3
      (fun k => @ite ℝ (k = j) (AddMulStrat.instDecidableEq AddMulRole.w3 k j) 1 0)) =
      fun k => if k = j then 1 else 0 := by
  funext k; fin_cases j <;> fin_cases k <;> rfl

lemma Tv3_same (σ : Mix) (j : Fin 2) :
    Tv3 (Function.update σ .v3
      (fun k => @ite ℝ (k = j) (AddMulStrat.instDecidableEq AddMulRole.v3 k j) 1 0)) =
      fun k => if k = j then 1 else 0 := by
  funext k; fin_cases j <;> fin_cases k <;> rfl

end

section
set_option autoImplicit false
open DGPNash.Gadget
variable (α β γ : ℕ)

lemma pay_w3 (s : ∀ r, AddMulStrat r) : addMulPayoff α β γ .w3 s =
    (8 : ℝ) * ∏ i, fac one2 one2 one2 one2 one2 one2 (is3 .star) (is2 0) one2 one2 i (s i)
    + ∏ i, fac one2 one2 (is2 1) one2 one2 one2 one3 (is2 1) one2 one2 i (s i) := by
  rw [P_fac, P_fac]
  simp only [one2, is2, one3, is3, addMulPayoff, ind]
  rcases fin2 (s .w3) with h | h <;> rcases fin2 (s .v3) with h' | h' <;>
    rcases tri3 (s .v2') with h'' | h'' | h'' <;> simp [h, h', h'']

lemma E_w3 (τ : Mix) (hτ : ∀ r, ∑ a, τ r a = 1) :
    AGT.expectedPayoff (addMulPayoff α β γ) τ .w3 =
      (8 : ℝ) * (Tv2' τ .star * Tw3 τ 0) + Tv3 τ 1 * Tw3 τ 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := lots τ hτ
  unfold AGT.expectedPayoff AGT.profileProb
  simp only [pay_w3, mul_add, Finset.sum_add_distrib, sum_cmul, E_fac]
  simp only [s1, s1t, s2, s3, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  ring

lemma pay_v3 (s : ∀ r, AddMulStrat r) : addMulPayoff α β γ .v3 s =
    ∏ i, fac one2 one2 (is2 0) one2 one2 one2 one3 (is2 1) one2 one2 i (s i)
    + ∏ i, fac one2 one2 (is2 1) one2 one2 one2 one3 (is2 0) one2 one2 i (s i) := by
  rw [P_fac, P_fac]
  simp only [one2, is2, one3, addMulPayoff, ind]
  rcases fin2 (s .w3) with h | h <;> rcases fin2 (s .v3) with h'' | h'' <;> simp [h, h'']

lemma E_v3 (τ : Mix) (hτ : ∀ r, ∑ a, τ r a = 1) :
    AGT.expectedPayoff (addMulPayoff α β γ) τ .v3 =
      Tw3 τ 1 * Tv3 τ 0 + Tw3 τ 0 * Tv3 τ 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := lots τ hτ
  unfold AGT.expectedPayoff AGT.profileProb
  simp only [pay_v3, mul_add, Finset.sum_add_distrib, sum_cmul, E_fac]
  simp only [s1, s1t, s2, s3, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  ring

theorem claim4 (ε : ℝ) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 100) (σ : ∀ r, AddMulStrat r → ℝ)
    (hσ : IsEpsNash (addMulPayoff α β γ) ε σ) :
    |σ .v3 (1 : Fin 2) - min 1 (8 * σ .v2' Tri.star)| ≤ ε := by
  obtain ⟨hmix, hws⟩ := hσ
  have nn : ∀ r a, 0 ≤ σ r a := fun r => (hmix r).1
  have Pw3_0 : DGPNash.NashMap.purePayoff (addMulPayoff α β γ) σ .w3 (0 : Fin 2) = 8 * σ .v2' Tri.star := by
    unfold DGPNash.NashMap.purePayoff
    refine (E_w3 α β γ _ (upd_lot σ hmix _ _)).trans ?_
    rw [Tw3_same σ (0 : Fin 2)]
    simp only [Tv1_ne, Tv2_ne, Tv3_ne, Tw1_ne, Tv1'_ne, Tw2_ne, Tv2'_ne, Tw3_ne, Tw_ne, Tu_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    simp [Tv1, Tv2, Tv3, Tw1, Tv1', Tw2, Tv2', Tw3, Tw, Tu] <;> ring
  have Pw3_1 : DGPNash.NashMap.purePayoff (addMulPayoff α β γ) σ .w3 (1 : Fin 2) = σ .v3 (1 : Fin 2) := by
    unfold DGPNash.NashMap.purePayoff
    refine (E_w3 α β γ _ (upd_lot σ hmix _ _)).trans ?_
    rw [Tw3_same σ (1 : Fin 2)]
    simp only [Tv1_ne, Tv2_ne, Tv3_ne, Tw1_ne, Tv1'_ne, Tw2_ne, Tv2'_ne, Tw3_ne, Tw_ne, Tu_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    simp [Tv1, Tv2, Tv3, Tw1, Tv1', Tw2, Tv2', Tw3, Tw, Tu] <;> ring
  have Pv3_0 : DGPNash.NashMap.purePayoff (addMulPayoff α β γ) σ .v3 (0 : Fin 2) = σ .w3 (1 : Fin 2) := by
    unfold DGPNash.NashMap.purePayoff
    refine (E_v3 α β γ _ (upd_lot σ hmix _ _)).trans ?_
    rw [Tv3_same σ (0 : Fin 2)]
    simp only [Tv1_ne, Tv2_ne, Tv3_ne, Tw1_ne, Tv1'_ne, Tw2_ne, Tv2'_ne, Tw3_ne, Tw_ne, Tu_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    simp [Tv1, Tv2, Tv3, Tw1, Tv1', Tw2, Tv2', Tw3, Tw, Tu] <;> ring
  have Pv3_1 : DGPNash.NashMap.purePayoff (addMulPayoff α β γ) σ .v3 (1 : Fin 2) = σ .w3 (0 : Fin 2) := by
    unfold DGPNash.NashMap.purePayoff
    refine (E_v3 α β γ _ (upd_lot σ hmix _ _)).trans ?_
    rw [Tv3_same σ (1 : Fin 2)]
    simp only [Tv1_ne, Tv2_ne, Tv3_ne, Tw1_ne, Tv1'_ne, Tw2_ne, Tv2'_ne, Tw3_ne, Tw_ne, Tu_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    simp [Tv1, Tv2, Tv3, Tw1, Tv1', Tw2, Tv2', Tw3, Tw, Tu] <;> ring
  have sv3 : σ .v3 (0 : Fin 2) + σ .v3 (1 : Fin 2) = 1 := by
    rw [← sum_two_of (σ .v3) (0 : Fin 2) (1 : Fin 2) (show (0 : Fin 2) ≠ 1 by decide) fin2]; exact (hmix .v3).2
  have sw3 : σ .w3 (0 : Fin 2) + σ .w3 (1 : Fin 2) = 1 := by
    rw [← sum_two_of (σ .w3) (0 : Fin 2) (1 : Fin 2) (show (0 : Fin 2) ≠ 1 by decide) fin2]; exact (hmix .w3).2
  have p30 := nn .v3 (0 : Fin 2); have p31 := nn .v3 (1 : Fin 2)
  have q0 := nn .w3 (0 : Fin 2); have q1 := nn .w3 (1 : Fin 2)
  have ts := nn .v2' Tri.star
  have hup : σ .v3 (1 : Fin 2) ≤ 8 * σ .v2' Tri.star + ε := by
    by_contra hc; push_neg at hc
    have e1 : σ .w3 (0 : Fin 2) = 0 :=
      hws .w3 (1 : Fin 2) (0 : Fin 2) (by rw [Pw3_0, Pw3_1]; linarith)
    have e2 : σ .v3 (1 : Fin 2) = 0 :=
      hws .v3 (0 : Fin 2) (1 : Fin 2) (by rw [Pv3_0, Pv3_1]; linarith)
    linarith
  have hlo : 8 * σ .v2' Tri.star - ε ≤ σ .v3 (1 : Fin 2) ∨ σ .v3 (1 : Fin 2) = 1 := by
    by_contra hc; push_neg at hc
    have e1 : σ .w3 (1 : Fin 2) = 0 :=
      hws .w3 (0 : Fin 2) (1 : Fin 2) (by rw [Pw3_0, Pw3_1]; linarith)
    have e2 : σ .v3 (0 : Fin 2) = 0 :=
      hws .v3 (1 : Fin 2) (0 : Fin 2) (by rw [Pv3_0, Pv3_1]; linarith)
    exact hc.2 (by linarith)
  rw [abs_le]
  rcases min_cases (1 : ℝ) (8 * σ .v2' Tri.star) with ⟨hm, hm'⟩ | ⟨hm, hm'⟩ <;> rw [hm] <;>
    rcases hlo with h | h <;> constructor <;> linarith

theorem part2 (hαβγ : α + β + γ ≤ 3) (ε : ℝ) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 100)
    (σ : ∀ r, AddMulStrat r → ℝ) (hσ : IsEpsNash (addMulPayoff α β γ) ε σ) :
    |σ .v3 (1 : Fin 2) - min 1 ((α : ℝ) * σ .v1 (1 : Fin 2) + (β : ℝ) * σ .v2 (1 : Fin 2)
      + (γ : ℝ) * σ .v1 (1 : Fin 2) * σ .v2 (1 : Fin 2))| ≤ 81 * ε := by
  have h3 := DGPNash.Gadget.claim3_v2prime_star α β γ hαβγ ε hε0 hε σ hσ
  have h4 := claim4 α β γ ε hε0 hε σ hσ
  set T := (α : ℝ) * σ .v1 (1 : Fin 2) + (β : ℝ) * σ .v2 (1 : Fin 2)
      + (γ : ℝ) * σ .v1 (1 : Fin 2) * σ .v2 (1 : Fin 2) with hT
  have h8 : |8 * σ .v2' Tri.star - T| ≤ 80 * ε := by
    have : 8 * σ .v2' Tri.star - T = 8 * (σ .v2' Tri.star - ((α : ℝ) / 8 * σ .v1 (1 : Fin 2)
        + (β : ℝ) / 8 * σ .v2 (1 : Fin 2) + (γ : ℝ) / 8 * σ .v1 (1 : Fin 2) * σ .v2 (1 : Fin 2))) := by
      rw [hT]; ring
    rw [this, abs_mul]; norm_num; linarith
  have hm : |min 1 (8 * σ .v2' Tri.star) - min 1 T| ≤ 80 * ε := by
    have := abs_min_sub_min_le_max (1 : ℝ) (8 * σ .v2' Tri.star) 1 T
    simp only [sub_self, abs_zero] at this
    exact this.trans (max_le (by linarith) h8)
  calc |σ .v3 (1 : Fin 2) - min 1 T|
      = |(σ .v3 (1 : Fin 2) - min 1 (8 * σ .v2' Tri.star)) + (min 1 (8 * σ .v2' Tri.star) - min 1 T)| := by
        ring_nf
    _ ≤ |σ .v3 (1 : Fin 2) - min 1 (8 * σ .v2' Tri.star)| + |min 1 (8 * σ .v2' Tri.star) - min 1 T| :=
        abs_add_le _ _
    _ ≤ ε + 80 * ε := add_le_add h4 hm
    _ = 81 * ε := by ring

def reads : AddMulRole → List AddMulRole
  | .v1 => []
  | .v2 => []
  | .v1' => [.v1', .w1]
  | .w1 => [.w1, .v1, .v1']
  | .v3 => [.v3, .w3]
  | .w3 => [.w3, .v2', .v3]
  | .w2 => [.w2, .v2, .v2']
  | .v2' => [.v2', .u, .w2]
  | .w => [.w, .v2', .v1']
  | .u => [.u, .w]

lemma pay_dep (r : AddMulRole) (s t : ∀ r, AddMulStrat r) (h : ∀ x ∈ reads r, s x = t x) :
    addMulPayoff α β γ r s = addMulPayoff α β γ r t := by
  cases r
  · rfl
  · rfl
  · simp only [addMulPayoff]; rw [h .v3 (by decide), h .w3 (by decide)]
  · simp only [addMulPayoff]; rw [h .w1 (by decide), h .v1 (by decide), h .v1' (by decide)]
  · simp only [addMulPayoff]; rw [h .v1' (by decide), h .w1 (by decide)]
  · simp only [addMulPayoff]; rw [h .w2 (by decide), h .v2 (by decide), h .v2' (by decide)]
  · simp only [addMulPayoff]; rw [h .v2' (by decide), h .u (by decide), h .w2 (by decide)]
  · simp only [addMulPayoff]; rw [h .w3 (by decide), h .v2' (by decide), h .v3 (by decide)]
  · simp only [addMulPayoff]; rw [h .w (by decide), h .v2' (by decide), h .v1' (by decide)]
  · simp only [addMulPayoff]; rw [h .u (by decide), h .w (by decide)]

lemma affects_reads (v w : AddMulRole) (h : Affects (addMulPayoff α β γ) v w) : v ∈ reads w := by
  by_contra hv
  obtain ⟨_, s, a, b, hne⟩ := h
  apply hne
  apply pay_dep
  intro x hx
  have hxv : x ≠ v := fun e => hv (e ▸ hx)
  rw [Function.update_of_ne hxv, Function.update_of_ne hxv]

def col : AddMulRole → Fin 3
  | .v2' => 0 | .w => 1 | .u => 2 | .w2 => 1 | .v2 => 2 | .v1' => 2
  | .w1 => 0 | .v1 => 1 | .w3 => 1 | .v3 => 2

lemma col_edge : ∀ v w : AddMulRole, v ∈ reads w → v ≠ w → col v ≠ col w := by decide

lemma col_sib : ∀ v v' w : AddMulRole, v ∈ reads w → v' ∈ reads w → v ≠ w → v' ≠ w →
    v ≠ v' → col v ≠ col v' := by decide

theorem part1 : IsLegallyColorable (addMulPayoff α β γ) 3 := by
  refine ⟨col, ?_, ?_⟩
  · intro v w h
    exact col_edge v w (affects_reads α β γ v w h) h.1
  · intro v v' w h h' hne
    exact col_sib v v' w (affects_reads α β γ v w h) (affects_reads α β γ v' w h') h.1 h'.1 hne

end

section
set_option autoImplicit false

open DGPNash.Gadget in
theorem solution (α β γ : ℕ) (hαβγ : α + β + γ ≤ 3) :
    IsLegallyColorable (addMulPayoff α β γ) 3 ∧
    ∀ (ε : ℝ), 0 ≤ ε → ε ≤ 1 / 100 → ∀ σ : ∀ r, AddMulStrat r → ℝ,
      IsEpsNash (addMulPayoff α β γ) ε σ →
      |σ .v3 (1 : Fin 2) - min 1 ((α : ℝ) * σ .v1 (1 : Fin 2) + (β : ℝ) * σ .v2 (1 : Fin 2)
        + (γ : ℝ) * σ .v1 (1 : Fin 2) * σ .v2 (1 : Fin 2))| ≤ 81 * ε := by
  exact ⟨part1 α β γ, fun ε h0 h1 σ hσ => part2 α β γ hαβγ ε h0 h1 σ hσ⟩

end
