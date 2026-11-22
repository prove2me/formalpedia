-- Prove2me | solution 1 for Egrs75.RoundUp.ru_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:29:53.879183+00:00
-- url     : https://prove2.me/submissions/75fbc751-6e0f-4da4-9e7a-b8530f566009

module
public import Definitions.Def_LeanPool_Egrs75_Defs
public import Mathlib.Algebra.Order.SuccPred
public import Mathlib.Data.Finset.Attr
public import Definitions.Def_LeanPool_Egrs75_RoundUp

set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.RoundUp
open Nat
open Egrs75
variable (p : ℕ)
namespace Egrs75.RoundUp
theorem _root_.solution {p : ℕ} (hp : 3 ≤ p) (hodd : Odd p) :
    ∀ x, 1 ≤ x → x ≤ ru p x ∧ ru p x < 2 * x := by
  -- `Odd p` ⟹ `2 * ((p-1)/2) + 1 = p`, i.e. the half is exact: `(p-1)/2 = (p-1)/2`
  -- and any digit `> (p-1)/2` is `≥ (p+1)/2`, so `2*digit ≥ p+1 > p`.
  have hhalf : 2 * ((p - 1) / 2) + 1 = p := by
    obtain ⟨k, hk⟩ := hodd
    simp_all
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro hx1
    rw [ru]
    split_ifs with hx0 hsmall hlow hlow2
    · omega  -- x = 0 contradicts 1 ≤ x
    · -- single low digit: ru = x.  x ≤ x ✓; x < 2x since x ≥ 1
      omega
    · -- carry to p (here ¬(x ≤ (p-1)/2), and hsmall : x < p ∨ p < 3, with p ≥ 3 so x < p)
      -- ru = p.  Need x ≤ p (since x < p) and p < 2x.
      -- ¬hlow : (p-1)/2 < x, and 2*((p-1)/2)+1 = p ⟹ p ≤ 2x - 1 < 2x. x ≤ p since x < p.
      refine ⟨by omega, ?_⟩
      -- p < 2x : from (p-1)/2 < x ⟹ p = 2*((p-1)/2)+1 ≤ 2*(x-1)+1 = 2x-1 < 2x
      omega
    · -- keep low digit: ru = p * ru(x/p) + x%p,  hlow2 : x%p ≤ (p-1)/2
      -- Need x/p ≥ 1 to apply IH. Since ¬hsmall ⟹ p ≤ x ⟹ x/p ≥ 1.
      have hpx : p ≤ x := by omega
      have hr1 : 1 ≤ x / p := Nat.one_le_div_iff (by omega) |>.mpr hpx
      have hrlt : x / p < x := Nat.div_lt_self (by omega) (by omega)
      obtain ⟨hlo, hhi⟩ := ih (x / p) hrlt hr1
      have hsplit : x = p * (x / p) + x % p := (Nat.div_add_mod x p).symm
      constructor
      · -- x = p*(x/p) + x%p ≤ p*ru(x/p) + x%p
        calc x = p * (x / p) + x % p := hsplit
          _ ≤ p * ru p (x / p) + x % p := by
              exact Nat.add_le_add_right (Nat.mul_le_mul_left p hlo) _
      · -- p*ru(x/p) + x%p < 2x = 2*(p*(x/p) + x%p)
        -- ru(x/p) < 2*(x/p) ⟹ p*ru(x/p) < 2*(p*(x/p))
        -- so p*ru(x/p) + x%p < 2*(p*(x/p)) + x%p ≤ 2*(p*(x/p)) + 2*(x%p) = 2x
        have hstrict : p * ru p (x / p) < 2 * (p * (x / p)) := by
          have := Nat.mul_lt_mul_of_pos_left hhi (show 0 < p by omega)
          -- this : p * ru(x/p) < p * (2 * (x/p));  p*(2*(x/p)) = 2*(p*(x/p))
          calc p * ru p (x / p) < p * (2 * (x / p)) := this
            _ = 2 * (p * (x / p)) := by ring
        -- linear in atoms {p*ru(x/p), p*(x/p), x, x%p}:
        --   hsplit : x = p*(x/p) + x%p;  hstrict : p*ru(x/p) < 2*(p*(x/p))
        --   goal   : p*ru(x/p) + x%p < 2*x.
        have hge0 : 0 ≤ x % p := Nat.zero_le _
        linarith [hsplit, hstrict, hge0]
    · -- carry branch: ru = p * ru(x/p + 1),  ¬hlow2 : (p-1)/2 < x%p
      have hpx : p ≤ x := by omega
      have hdec : x / p + 1 < x := by
        have hdiv : x / p ≤ x / 3 := Nat.div_le_div_left hp (by omega)
        omega
      have hr1 : 1 ≤ x / p + 1 := Nat.le_add_left 1 (x / p)
      obtain ⟨hlo, hhi⟩ := ih (x / p + 1) hdec hr1
      have hsplit : x = p * (x / p) + x % p := (Nat.div_add_mod x p).symm
      have hxmod : x % p < p := Nat.mod_lt x (by omega)
      -- ¬hlow2 : (p-1)/2 < x%p ⟹ x%p ≥ (p-1)/2 + 1, and 2*((p-1)/2)+1 = p ⟹ 2*(x%p) ≥ p+1 > p
      have hmodbig : p < 2 * (x % p) := by
        -- hlow2 : ¬(x%p ≤ (p-1)/2); hhalf : 2*((p-1)/2)+1 = p
        omega
      refine ⟨le_of_lt ?_, ?_⟩
      · -- x = p*(x/p)+x%p < p*(x/p) + p = p*(x/p+1) ≤ p*ru(x/p+1)
        calc x = p * (x / p) + x % p := hsplit
          _ < p * (x / p) + p := by omega
          _ = p * (x / p + 1) := by ring
          _ ≤ p * ru p (x / p + 1) := Nat.mul_le_mul_left p hlo
      · -- p*ru(x/p+1) < 2x.  ru(x/p+1) < 2*(x/p+1) ⟹ ru(x/p+1) ≤ 2*(x/p)+1
        -- p*ru ≤ p*(2*(x/p)+1) = 2*(p*(x/p)) + p < 2*(p*(x/p)) + 2*(x%p) = 2x.
        have hru_le : ru p (x / p + 1) ≤ 2 * (x / p) + 1 := by omega
        have hmul : p * ru p (x / p + 1) ≤ 2 * (p * (x / p)) + p := by
          calc p * ru p (x / p + 1) ≤ p * (2 * (x / p) + 1) := Nat.mul_le_mul_left p hru_le
            _ = 2 * (p * (x / p)) + p := by ring
        -- linear in atoms {p*ru(x/p+1), p*(x/p), x, x%p, p}:
        --   hsplit : x = p*(x/p) + x%p; hmul : p*ru(x/p+1) ≤ 2*(p*(x/p)) + p;
        --   hmodbig : p < 2*(x%p).  goal : p*ru(x/p+1) < 2*x.
        linarith [hsplit, hmul, hmodbig]
end Egrs75.RoundUp
