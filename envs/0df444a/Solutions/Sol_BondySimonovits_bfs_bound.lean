-- Prove2me | solution 1 for BondySimonovits.bfs_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:16:14.450705+00:00
-- url     : https://prove2.me/submissions/a3b17cca-23cc-4916-95bc-be7c614647a9

module
public import Definitions.Def_BondySimonovitsLib_BSCycle
public import Definitions.Def_BondySimonovitsLib_BSGrowth
public import Theorems.Thm_BondySimonovits_ecount_comm
public import Theorems.Thm_BondySimonovits_ecount_le_mul
public import Theorems.Thm_BondySimonovits_ecount_eq_zero
public import Theorems.Thm_BondySimonovits_layer_growth
public import Theorems.Thm_BondySimonovits_mem_layer
public import Theorems.Thm_BondySimonovits_layer_zero_card_le
public import Theorems.Thm_BondySimonovits_mem_layer_zero
public import Theorems.Thm_BondySimonovits_no_adj_same_layer
public import Theorems.Thm_BondySimonovits_degree_sum_layer
public import Theorems.Thm_BondySimonovits_layer_claim

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BondySimonovits
variable {V : Type*} [Fintype V] [DecidableEq V] (K : SimpleGraph V) [DecidableRel K.Adj]
variable (f : V → Bool) (hf : ∀ u v, K.Adj u v → f u ≠ f v)
include hf
omit [DecidableEq V]
namespace BondySimonovits
theorem _root_.solution (x : V) (k : ℕ) (hk : 2 ≤ k)
    (hcyc : ∀ (v : V) (p : K.Walk v v), p.IsCycle → p.length ≠ 2 * k) (d : ℕ)
    (hdeg : ∀ v, K.Reachable x v → d ≤ (univ.filter (K.Adj v)).card) (hdk : 8 * k ≤ d) :
    ((d : ℝ) / (2 * k : ℕ) - 3) ^ k ≤ Fintype.card V := by
  classical
  have hsum : ∀ i, d * (layer K x i).card ≤ ecount K (layer K x i) (layer K x (i - 1)) +
      ecount K (layer K x i) (layer K x (i + 1)) := by
    intro i
    rw [← degree_sum_layer K f hf x i]
    calc d * (layer K x i).card = ∑ _u ∈ layer K x i, d := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun u hu => hdeg u ((mem_layer K).1 hu).1)
  have h0 : (layer K x 0).card ≤ 1 := layer_zero_card_le K x
  have ha0 : (layer K x 0).card = 1 :=
    le_antisymm h0 (Finset.card_pos.2 ⟨x, mem_layer_zero K x⟩)
  have h1 : d ≤ (layer K x 1).card := by
    have := hsum 0
    rw [show (0 : ℕ) - 1 = 0 by rfl, ecount_eq_zero K _ _ (no_adj_same_layer K f hf x 0)] at this
    have h2 := ecount_le_mul K (layer K x 0) (layer K x (0 + 1))
    rw [ha0] at this h2
    simp only [zero_add] at this h2
    omega
  have hrec : ∀ i, 1 ≤ i → i + 1 ≤ k →
      d * (layer K x i).card ≤ 2 * k * ((layer K x (i - 1)).card + (layer K x i).card) +
        2 * k * ((layer K x i).card + (layer K x (i + 1)).card) := by
    intro i hi hik
    have e1 := layer_claim K f hf x k hk hcyc (i - 1) (by omega)
    have e2 := layer_claim K f hf x k hk hcyc i hik
    rw [show i - 1 + 1 = i by omega] at e1
    have := hsum i
    rw [ecount_comm K (layer K x i) (layer K x (i - 1))] at this
    omega
  obtain ⟨hgrow, -⟩ := layer_growth (fun i => (layer K x i).card) k d (2 * k) (by omega)
    (by omega) h0 h1 hrec k (by omega) le_rfl
  calc ((d : ℝ) / (2 * k : ℕ) - 3) ^ k ≤ (layer K x k).card := hgrow
    _ ≤ Fintype.card V := by exact_mod_cast Finset.card_le_univ _
end BondySimonovits
