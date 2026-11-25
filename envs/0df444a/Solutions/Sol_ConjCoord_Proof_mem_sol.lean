-- Prove2me | solution 1 for ConjCoord.Proof.mem_sol
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:49:33.854804+00:00
-- url     : https://prove2.me/submissions/5ddd7b70-51ce-49bf-91e8-ab6d1e0e95b0

module
public import Definitions.Def_ConjCoord_Defs
public import Definitions.Def_ConjCoord_Reps
public import Theorems.Thm_ConjCoord_Proof_mem_Icc_of_sq_le

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof
namespace ConjCoord.Proof
theorem _root_.solution {a b c n : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (v : ℤ × ℤ × ℤ) :
    v ∈ sol a b c n ↔ (a : ℤ) * v.1 ^ 2 + b * v.2.1 ^ 2 + c * v.2.2 ^ 2 = n := by
  unfold sol box3
  rw [mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  have hc' : (1 : ℤ) ≤ c := by exact_mod_cast hc
  have e1 := mul_nonneg (by linarith : (0 : ℤ) ≤ a) (sq_nonneg v.1)
  have e2 := mul_nonneg (by linarith : (0 : ℤ) ≤ b) (sq_nonneg v.2.1)
  have e3 := mul_nonneg (by linarith : (0 : ℤ) ≤ c) (sq_nonneg v.2.2)
  have f1 : v.1 ^ 2 ≤ (a : ℤ) * v.1 ^ 2 := le_mul_of_one_le_left (sq_nonneg _) ha'
  have f2 : v.2.1 ^ 2 ≤ (b : ℤ) * v.2.1 ^ 2 := le_mul_of_one_le_left (sq_nonneg _) hb'
  have f3 : v.2.2 ^ 2 ≤ (c : ℤ) * v.2.2 ^ 2 := le_mul_of_one_le_left (sq_nonneg _) hc'
  refine mem_product.mpr ⟨mem_Icc_of_sq_le (by linarith), mem_product.mpr
    ⟨mem_Icc_of_sq_le (by linarith), mem_Icc_of_sq_le (by linarith)⟩⟩
end ConjCoord.Proof
