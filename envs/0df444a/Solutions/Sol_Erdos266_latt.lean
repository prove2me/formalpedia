-- Prove2me | solution 1 for Erdos266.latt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:47:46.702674+00:00
-- url     : https://prove2.me/submissions/ce091408-5c29-4c7d-9072-03c0da799129

module
public import Definitions.Def_Erdos266_LatticeLemma
public import Definitions.Def_Erdos266_Growth
public import Definitions.Def_Erdos266_Algorithm
public import Theorems.Thm_Erdos266_lattice_lemma


set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
namespace Erdos266
theorem _root_.solution (d : ℕ) :
    ∀ (N M : ℕ), 1 ≤ N → 4 * d * M ≤ N →
      ∀ x : Fin d → ℝ,
        (∀ i : Fin d, |x i - ∑ j : Fin d, f (i.val + 1) (((j.val + 1) * N : ℕ) : ℝ)|
          ≤ εL d * M / (N : ℝ) ^ (i.val + 2)) →
        ∃ n : Fin d → ℤ, (∀ j, |n j| ≤ (M : ℤ)) ∧
          ∀ i : Fin d,
            |x i - ∑ j : Fin d, f (i.val + 1) ((((j.val + 1) * N : ℕ) : ℝ) + (n j : ℝ))|
              ≤ DL d * (1 / (N : ℝ) ^ (i.val + 2) + (M : ℝ) ^ 2 / (N : ℝ) ^ (i.val + 3)) :=
  (lattice_lemma d).choose_spec.choose_spec.2.2.2
end Erdos266
