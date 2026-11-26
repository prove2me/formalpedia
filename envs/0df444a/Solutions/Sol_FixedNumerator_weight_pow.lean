-- Prove2me | solution 1 for FixedNumerator.weight_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:41:33.81315+00:00
-- url     : https://prove2.me/submissions/39bb64c5-1e4a-4988-9a0e-4cfeaa052b62

module
public import Definitions.Def_FixedNumerator_Local
public import Definitions.Def_FixedNumerator_Split

set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator
namespace FixedNumerator
theorem _root_.solution {W : GaussianInt → ℂ} (hW1 : W 1 = 1) (hW : ∀ a b, W (a * b) = W a * W b)
    (a : GaussianInt) (k : ℕ) : W (a ^ k) = W a ^ k := by
  induction k with
  | zero => simpa using hW1
  | succ k ih => rw [pow_succ, hW, ih, pow_succ]
end FixedNumerator
