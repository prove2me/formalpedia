-- Prove2me | solution 1 for Erdos1063.erdos_1063.variants.exception_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:15:34.576628+00:00
-- url     : https://prove2.me/submissions/5d316b69-f79c-4875-a99b-6226c6dae351

module
public import Definitions.Def_Erdos1063_Lower
public import Definitions.Def_Erdos1063_Solution
public import Theorems.Thm_Erdos1063_exception_dvd


set_option autoImplicit false
@[expose] public section
public section
open Erdos1063
namespace Erdos1063
namespace erdos_1063.variants
theorem _root_.solution {n k e : ℕ} (hk : 2 ≤ k) (h : 2 * k ≤ n) (he : e < k)
    (hgood : ∀ i < k, i ≠ e → (n - i) ∣ n.choose k) :
    e = n % k ∧
      ∏ p ∈ k.primeFactors,
        p ^ (padicValNat p k + padicValNat p ((k - 1).choose e) + Nat.log p (max e (k - 1 - e)))
        ∣ n - e :=
  Erdos1063.exception_dvd hk h he hgood
end erdos_1063.variants
end Erdos1063
