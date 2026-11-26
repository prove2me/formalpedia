-- Prove2me | solution 1 for FixedNumerator.QuarticData.chi_pow_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:42:16.715231+00:00
-- url     : https://prove2.me/submissions/12a06e51-df37-4379-9e26-87b4766ce3cc

module
public import Definitions.Def_FixedNumerator_Primary
public import Definitions.Def_FixedNumerator_Local
public import Theorems.Thm_FixedNumerator_QuarticData_chi_one_right
public import Theorems.Thm_FixedNumerator_IsPrimary_pow


set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator
open FixedNumerator.QuarticData
variable (D : QuarticData)
namespace FixedNumerator.QuarticData
theorem _root_.solution (a : GaussianInt) {π : GaussianInt} (hπ : IsPrimary π) (n : ℕ) :
    D.χ a (π ^ n) = D.χ a π ^ n := by
  induction n with
  | zero => simpa using D.chi_one_right a
  | succ n ih => rw [pow_succ, D.chi_mul_right a _ _ (hπ.pow n) hπ, ih, pow_succ]
end FixedNumerator.QuarticData
