-- Prove2me | solution 1 for Erdos1063.erdos_1063.variants.lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:36:06.834636+00:00
-- url     : https://prove2.me/submissions/b8654340-7958-4434-87f8-3a536eea8b37

module
public import Definitions.Def_Erdos1063_Lower
public import Definitions.Def_Erdos1063_Solution
public import Theorems.Thm_Erdos1063_lower_bound


set_option autoImplicit false
@[expose] public section
public section
open Erdos1063
namespace Erdos1063
namespace erdos_1063.variants
theorem _root_.solution {k : ℕ} (hk : 2 ≤ k) :
    ∏ p ∈ k.primeFactors, p ^ (padicValNat p k + Nat.log p (k - 1)) ≤ n k :=
  Erdos1063.lower_bound hk
end erdos_1063.variants
end Erdos1063
