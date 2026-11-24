-- Prove2me | solution 1 for Erdos1219.core
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:52:24.854796+00:00
-- url     : https://prove2.me/submissions/4264066c-c47a-4f78-8962-752ad75a417e

import Definitions.Def_Erdos1219_Defs
import Definitions.Def_Erdos1219_CardinalLemmas
import Definitions.Def_Erdos1219_Ramsey
import Definitions.Def_Erdos1219_UnbalancedErdosRado
import Definitions.Def_Erdos1219_Canonization
import Theorems.Thm_Erdos1219_Ctx_exists_homog
import Theorems.Thm_Erdos1219_sum_eq_of_interlaced


set_option autoImplicit false
open Cardinal Ordinal Function
open Erdos1219
universe u
namespace Erdos1219
theorem _root_.solution {V : Type u} (f : V → V → Bool) (hf : ∀ x y, f x y = f y x)
    (n : ℕ → ℕ) (hn : StrictMono n)
    (hpow : StrictMono fun k => (2 : Cardinal.{u}) ^ ℵ_ (n k))
    (h0 : ℵ_ ω < (2 : Cardinal.{u}) ^ ℵ_ (n 0))
    (hV : #V = Cardinal.sum fun k => (2 : Cardinal.{u}) ^ ℵ_ (n k)) :
    ∃ (c : Bool) (H : Set V), #H = ℵ_ ω ∧ Homog f c H := by
  by_contra hno
  have hsum : #V = #(Σ k : ℕ, (Order.succ ((2 : Cardinal.{u}) ^ ℵ_ (n k))).out) := by
    rw [hV]
    exact sum_eq_of_interlaced _ _ (fun k => Order.le_succ _)
      (fun k => Order.succ_le_of_lt (hpow (Nat.lt_succ_self k)))
  obtain ⟨e⟩ := Cardinal.eq.1 hsum
  let A : ℕ → Set V := fun k => e.symm '' Set.range (Sigma.mk k)
  have hA : ∀ k, #(A k) = Order.succ ((2 : Cardinal.{u}) ^ ℵ_ (n k)) := by
    intro k
    simp only [A]
    rw [mk_image_eq e.symm.injective, mk_range_eq _ sigma_mk_injective, mk_out]
  have hdisj : ∀ i j, i ≠ j → Disjoint (A i) (A j) := by
    intro i j hij
    simp only [A]
    rw [Set.disjoint_image_iff e.symm.injective]
    rw [Set.disjoint_left]
    rintro _ ⟨a, rfl⟩ ⟨b, hb⟩
    exact hij (Sigma.mk.inj_iff.1 hb).1.symm
  have hno' : ∀ (c : Bool) (H : Set V), Homog f c H → #H ≠ ℵ_ ω :=
    fun c H hH hc => hno ⟨c, H, hc, hH⟩
  let S : Ctx V := ⟨f, hf, n, hn, hpow, h0, A, hA, hdisj, hno'⟩
  obtain ⟨c, H, h1, h2⟩ := S.exists_homog
  exact hno ⟨c, H, h1, h2⟩
end Erdos1219
