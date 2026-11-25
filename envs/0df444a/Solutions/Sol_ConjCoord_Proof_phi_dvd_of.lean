-- Prove2me | solution 1 for ConjCoord.Proof.phi_dvd_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:54:32.471823+00:00
-- url     : https://prove2.me/submissions/f3b5e26d-1562-4001-a805-9a3395f3b7e5

module
public import Definitions.Def_ConjCoord_Compute
public import Definitions.Def_ConjCoord_TwoSquares
public import Definitions.Def_ConjCoord_Main
public import Theorems.Thm_ConjCoord_Proof_phi_eq

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof
namespace ConjCoord.Proof
theorem _root_.solution {n : ℕ} (h : ∀ m ≤ n, (64 : ℤ) ∣ tCoeff m) : (256 : ℤ) ∣ phi n := by
  rw [phi_eq]
  have h1 : (128 : ℤ) ∣ ∑ k ∈ range n, 2 * (if (k + 1) ^ 2 ≤ n then tCoeff (n - (k + 1) ^ 2) else 0) := by
    refine dvd_sum fun k _ => ?_
    split_ifs
    · obtain ⟨c, hc⟩ := h (n - (k + 1) ^ 2) (Nat.sub_le _ _)
      exact ⟨c, by rw [hc]; ring⟩
    · simp
  obtain ⟨c, hc⟩ := h1
  obtain ⟨d, hd⟩ := h n le_rfl
  exact ⟨d + 2 * c, by rw [hc, hd]; ring⟩
end ConjCoord.Proof
