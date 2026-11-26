-- Prove2me | solution 1 for Erdos266.elemZ_cross
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:11:00.790472+00:00
-- url     : https://prove2.me/submissions/2b930782-f48e-4343-8fe3-3c22a8796bfb

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
public import Theorems.Thm_Erdos266_two_le_of_dOf_pos
public import Theorems.Thm_Erdos266_elemZ_lb
public import Theorems.Thm_Erdos266_elemZ_ub
public import Theorems.Thm_Erdos266_twice_succ_le_bigN
public import Theorems.Thm_Erdos266_bigN_pos
public import Theorems.Thm_Erdos266_bigN_strictMono
public import Theorems.Thm_Erdos266_two_mul_bigM_lt


set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology
namespace Erdos266
theorem _root_.solution {l l' j j' : ℕ} (hll : l < l') (hj : j < dOf l) (hj' : j' < dOf l') :
    elemZ l j < elemZ l' j' := by
  have h2 : 2 ≤ l := two_le_of_dOf_pos (by omega)
  have h2' : 2 ≤ l' := by omega
  have hub := elemZ_ub hj
  have hlb := elemZ_lb hj'
  -- `l·N l + M l < N l' - M l'` via the doubling bound and `2M < N`
  have key : (l * bigN l : ℤ) + bigM l < (bigN l' : ℤ) - bigM l' := by
    have hA : 2 * ((l : ℤ) * bigN l + bigM l) ≤ (bigN (l + 1) : ℤ) := by
      have h5 : (bigM l : ℤ) < bigN l := by
        have := two_mul_bigM_lt h2
        have h6 : (0:ℤ) ≤ (bigM l : ℤ) := by positivity
        exact_mod_cast by omega
      have h7 : 2 * (l + 1) * bigN l ≤ bigN (l + 1) := twice_succ_le_bigN l
      have h7' : (2 * (l + 1) * bigN l : ℤ) ≤ (bigN (l + 1) : ℤ) := by exact_mod_cast h7
      nlinarith [show (0:ℤ) ≤ (l : ℤ) from by positivity,
        show (0:ℤ) < (bigN l : ℤ) from by exact_mod_cast bigN_pos l]
    have hB : (bigN (l + 1) : ℤ) ≤ (bigN l' : ℤ) := by
      exact_mod_cast bigN_strictMono.monotone (by omega : l + 1 ≤ l')
    have hC : 2 * (bigM l' : ℤ) < (bigN l' : ℤ) := by
      exact_mod_cast two_mul_bigM_lt h2'
    omega
  omega
end Erdos266
