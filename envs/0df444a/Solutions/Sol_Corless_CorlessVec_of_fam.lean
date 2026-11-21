-- Prove2me | solution 1 for Corless.CorlessVec.of_fam
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:44:15.699821+00:00
-- url     : https://prove2.me/submissions/9ee53d98-ebc3-4225-8a7f-d84abf4ad5e6

module
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Set.Card
public import Definitions.Def_LeanPool_CorlessNilpotent_Matrix
public import Definitions.Def_LeanPool_CorlessNilpotent_Vectors
public import Theorems.Thm_Corless_length_foldVector
public import Theorems.Thm_Corless_Fam_congr
public import Theorems.Thm_Corless_getD_step_left
public import Theorems.Thm_Corless_getD_step_a
public import Theorems.Thm_Corless_getD_step_b
public import Theorems.Thm_Corless_getD_step_right
public import Theorems.Thm_Corless_getD_mem
public import Theorems.Thm_Corless_eq_of_sgn
public import Theorems.Thm_Corless_ext_getD
public import Theorems.Thm_Corless_Dv_one
public import Theorems.Thm_Corless_Dv_zero
public import Theorems.Thm_Corless_entrySign_I
public import Theorems.Thm_Corless_entrySign_one
public import Theorems.Thm_Corless_folded_edges
attribute [local simp] Corless.Dv_one
attribute [local simp] Corless.Dv_zero
attribute [local simp] Corless.entrySign_I
attribute [local simp] Corless.entrySign_one



set_option autoImplicit true
@[expose] public section
public section
open Polynomial
open Corless
namespace Corless
namespace CorlessVec
theorem _root_.solution : ∀ (k : ℕ) {u : List ℂ}, u.length = 2 ^ (k + 1) - 2 →
    (∀ x ∈ u, x = 1 ∨ x = Complex.I) → Fam k (sgns u) → CorlessVec k u
  | 0, u, hlen, _, _ => by
      obtain rfl : u = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
      exact .base
  | k + 1, u, hlen, hu, hfam => by
      obtain ⟨n, hn⟩ : ∃ n, n = 2 ^ (k + 1) - 2 := ⟨_, rfl⟩
      have hlen' : u.length = 2 * n + 2 := by
        rw [hlen, hn]
        exact folded_edges k
      simp only [Fam, IsFolded, ← hn] at hfam
      obtain ⟨⟨hmid, hmir⟩, hfam'⟩ := hfam
      obtain ⟨v, hv⟩ : ∃ v, v = u.take n := ⟨_, rfl⟩
      have hvlen : v.length = n := by rw [hv, List.length_take]; omega
      have hvget : ∀ i < n, v.getD i 1 = u.getD i 1 := by
        intro i hi
        rw [hv, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take]
        simp [hi]
      have hvmem : ∀ x ∈ v, x = 1 ∨ x = Complex.I := fun x hx =>
        hu x (List.mem_of_mem_take (hv ▸ hx))
      have hvfam : Fam k (sgns v) := by
        rw [Fam_congr k (t := sgns u) (fun i hi => by
          unfold sgns
          rw [hvget i (by omega)])]
        exact hfam'
      have ih := solution k (by omega) hvmem hvfam
      -- `u` is `v ++ [a, b] ++ rev v` with `a, b` its two middle entries
      have hu_eq : u = foldVector v (u.getD n 1) (u.getD (n + 1) 1) := by
        apply ext_getD (by rw [length_foldVector, hvlen, hlen'])
        intro i hi
        rcases Nat.lt_or_ge i n with h1 | h1
        · rw [getD_step_left _ _ _ (by omega), hvget i h1]
        rcases Nat.lt_or_ge i (n + 2) with h2 | h2
        · rcases Nat.lt_or_ge i (n + 1) with h3 | h3
          · rw [show i = v.length by omega, getD_step_a, hvlen]
          · rw [show i = v.length + 1 by omega, getD_step_b, hvlen]
        · -- the right half mirrors the left half
          have hj := hmir (2 * n + 1 - i) (by omega)
          rw [show 2 * n + 1 - (2 * n + 1 - i) = i by omega] at hj
          rw [show i = 2 * v.length + 1 - (2 * n + 1 - i) by omega,
            getD_step_right _ _ _ (by omega), hvget _ (by omega)]
          rw [show 2 * v.length + 1 - (2 * n + 1 - i) = i by omega]
          exact eq_of_sgn (getD_mem hu i hi) (getD_mem hu (2 * n + 1 - i) (by omega)) hj
      -- the two middle entries are `1, i` or `i, 1`
      rw [hu_eq]
      unfold sgns at hmid
      rcases getD_mem hu n (by omega) with ha | ha <;>
        rcases getD_mem hu (n + 1) (by omega) with hb | hb <;>
          rw [ha, hb] at hmid ⊢ <;> simp at hmid
      · exact .step₁ ih
      · exact .step₂ ih
end CorlessVec
end Corless
