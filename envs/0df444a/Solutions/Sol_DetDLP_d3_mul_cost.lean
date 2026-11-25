-- Prove2me | solution 1 for DetDLP.d3_mul_cost
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T05:20:42.9928+00:00
-- url     : https://prove2.me/submissions/d40714c4-ec38-463a-bd69-822329bfbe6e

import Definitions.Def_DetDLP_F9A2_BMul
import Theorems.Thm_Groundwork_Unary_of_length
import Theorems.Thm_Groundwork_PolyT_map

set_option autoImplicit false
set_option maxHeartbeats 3000000
open Groundwork Groundwork.PolyT
open DetDLP DetDLP.F9A2 DetDLP_W1_Queries
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open Polynomial
namespace F9Proof
attribute [local fun_prop] PolyT.length PolyT.comp PolyT.const PolyT.fst PolyT.snd PolyT.prodMk PolyT.map
  PolyT.flatMap PolyT.mul PolyT.mod PolyT.sum PolyT.id' w5_M6Sort.encode_poly first_poly more_poly
  P2M_Groundwork_PolyT_id__1c5d0f44cc8f P2M_Groundwork_PolyT_cons__3a60f43a3b86
  P2M_Groundwork_PolyT_ite__226169acf219

variable {α : Type} [Enc α]
private theorem len_map_cap (D : List ℕ) (g : ℕ → ℕ) (m : ℕ) (h : ∀ i, g i ≤ m) :
    len (D.map g) ≤ D.length * (len m + 2) + 2 := by
  induction D with
  | nil => simp [len_nil]
  | cons i D ih =>
    have hi : len (g i) ≤ len m := by simp only [len_nat]; have := Nat.size_le_size (h i); omega
    simp only [List.map_cons, List.length_cons, len_cons, Nat.succ_mul]; omega

@[local fun_prop] private theorem step_poly {m : α → ℕ} {D c v : α → List ℕ}
    (hm : PolyT m) (hD : PolyT D) (hc : PolyT c) (hv : PolyT v) :
    PolyT fun x => step (m x) (D x) (c x) (v x) := by unfold step; fun_prop

private abbrev PC := ℕ × List ℕ × List ℕ × List ℕ
private theorem power_core : PolyT (fun p : PC => power p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have h : PolyT (fun p : PC => p.2.2.2.foldl (fun v _ => step (max 1 p.1) p.2.1 p.2.2.1 v)
      (p.2.1.map fun k => if k = 0 then 1 else 0)) := by
    apply PolyT.foldl (l := fun p : PC => p.2.2.2) (a := fun p : PC => p.2.1.map fun k => if k = 0 then 1 else 0) (g := fun (p : PC) (v : List ℕ) (_ : ℕ) => step (max 1 p.1) p.2.1 p.2.2.1 v)
    · fun_prop
    · fun_prop
    · fun_prop
    · refine ⟨fun n => n*(n+7)+2, (PB.id'.mul (PB.id'.add (PB.const 7))).add (PB.const 2), ?_⟩
      rintro ⟨m,D,c,F⟩ k
      have hm : len (max 1 m) ≤ len (m,D,c,F) + 5 := by
        cases m with
        | zero => simp [len_pair, len_nat]
        | succ n => simp [len_pair]; omega
      have hD : D.length ≤ len (m,D,c,F) := by have := length_le_len D; simp only [len_pair]; omega
      have hb : D.length * (len (max 1 m)+2)+2 ≤ len (m,D,c,F)*(len (m,D,c,F)+7)+2 :=
        Nat.add_le_add_right (Nat.mul_le_mul hD (by omega)) 2
      apply le_trans _ hb
      generalize F.take k = l
      induction l using List.reverseRecOn with
      | nil => apply len_map_cap; intro i; split <;> omega
      | append_singleton l a ih =>
        simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, step]
        apply len_map_cap; intro i; exact (Nat.mod_lt _ (by omega)).le
  have HH : PolyT (fun p : PC => if p.1 = 0 then ([] : List ℕ) else
      p.2.2.2.foldl (fun v _ => step (max 1 p.1) p.2.1 p.2.2.1 v)
        (p.2.1.map fun k => if k = 0 then 1 else 0)) := by fun_prop
  exact HH.congr fun p => by
    by_cases h0 : p.1 = 0
    · simp [power,h0]
    · simp [power,h0,Nat.max_eq_right (show 1 ≤ p.1 by omega)]

@[local fun_prop] private theorem power_poly {m : α → ℕ} {D c F : α → List ℕ}
    (hm : PolyT m) (hD : PolyT D) (hc : PolyT c) (hF : PolyT F) :
    PolyT fun x => power (m x) (D x) (c x) (F x) :=
  PolyT.comp (g := fun x => (m x,D x,c x,F x)) power_core (by fun_prop)

@[local fun_prop] private theorem rowsum_poly {I : α → List ℕ} {g : α → ℕ → ℕ}
    (hg : PolyT fun p : α × ℕ => g p.1 p.2) (hI : PolyT I) :
    PolyT fun x => rowsum (I x) (g x) := PolyT.sum (PolyT.map hg hI)

@[local fun_prop] private theorem coeff_poly {m t k : α → ℕ} {E D c a b : α → List ℕ}
    (hm : PolyT m) (hE : PolyT E) (hD : PolyT D) (hc : PolyT c) (ha : PolyT a) (hb : PolyT b)
    (ht : PolyT t) (hk : PolyT k) : PolyT fun x => F9A2.coeff (m x) (E x) (D x) (c x) (a x) (b x) (t x) (k x) := by
  unfold F9A2.coeff; fun_prop

@[local fun_prop] private theorem range_length {w : α → List Bool} (hw : PolyT w) :
    PolyT fun x => List.range (w x).length := PolyT.range (Unary.of_length hw)

@[local fun_prop] private theorem dec_poly {w : α → List Bool} (hw : PolyT w) :
    PolyT fun x => w5_M6Sort.decode (w x) := w5_M6Sort.decode_poly.comp hw

private theorem uniform : PolyT bMulRaw := by unfold bMulRaw table; dsimp only; fun_prop
end F9Proof
theorem solution : PolyT bMulRaw := F9Proof.uniform
