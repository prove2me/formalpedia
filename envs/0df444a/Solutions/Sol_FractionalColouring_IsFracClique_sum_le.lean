-- Prove2me | solution 1 for FractionalColouring.IsFracClique.sum_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:38:39.04564+00:00
-- url     : https://prove2.me/submissions/03944f77-6b35-40e0-b788-e5b86e25cd2c

module
public import Mathlib
public import Definitions.Def_FractionalLib_FiniteLPDuality
public import Definitions.Def_FractionalLib_Basic
public import Theorems.Thm_FractionalColouring_sum_le_mul_of_indep
public import Theorems.Thm_FiniteLP_toE_apply
attribute [local simp] FiniteLP.toE_apply



set_option autoImplicit true
@[expose] public section
public section
open Finset
open FractionalColouring
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
variable {G}
namespace FractionalColouring
namespace IsFracClique
theorem _root_.solution {g : V → ℝ} (hg : IsFracClique G g) {x : Finset V → ℝ}
    (hx : IsFracColouring G x) : ∑ v, g v ≤ ∑ s, x s := by
  have := sum_le_mul_of_indep (T := univ) hg.1 (c := 1)
    (fun s hs => by rw [Finset.univ_inter]; exact hg.2 s hs) hx
  simpa using this
end IsFracClique
end FractionalColouring
