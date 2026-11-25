-- Prove2me | solution 1 for FractionalColouring.IsFracClique.sum_le_fracChromaticNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:39:28.838089+00:00
-- url     : https://prove2.me/submissions/76e83703-a070-4d74-9d24-5a58714ccf2e

module
public import Mathlib
public import Definitions.Def_FractionalLib_FiniteLPDuality
public import Definitions.Def_FractionalLib_Basic
public import Theorems.Thm_FractionalColouring_weights_nonempty
public import Theorems.Thm_FractionalColouring_IsFracClique_sum_le

set_option autoImplicit true
@[expose] public section
public section
open Finset
open FractionalColouring
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
variable {G}
namespace FractionalColouring
namespace IsFracClique
theorem _root_.solution {g : V → ℝ} (hg : IsFracClique G g) :
    ∑ v, g v ≤ fracChromaticNumber G :=
  le_csInf weights_nonempty (by rintro _ ⟨x, hx, rfl⟩; exact hg.sum_le hx)
end IsFracClique
end FractionalColouring
