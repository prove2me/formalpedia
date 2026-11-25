-- Prove2me | solution 1 for Erdos1063.k_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:53:36.558167+00:00
-- url     : https://prove2.me/submissions/8775b76c-c110-4d58-9623-a4f9284b5f55

module
public import Mathlib
public import Definitions.Def_Erdos1063_Lower
public import Theorems.Thm_Erdos1063_W_dvd
public import Theorems.Thm_Erdos1063_dvd_W

set_option autoImplicit false
@[expose] public section
public section
open Finset
open scoped Nat
open Erdos1063
namespace Erdos1063
theorem _root_.solution {n k i0 : ℕ} (hkn : 2 * k ≤ n) (hk : 2 ≤ k) (hi0 : i0 < k)
    (hgood : ∀ i < k, i ≠ i0 → (n - i) ∣ n.choose k) : k ∣ n - i0 :=
  (dvd_W (by omega)).trans (W_dvd hkn hk hi0 hgood)
end Erdos1063
