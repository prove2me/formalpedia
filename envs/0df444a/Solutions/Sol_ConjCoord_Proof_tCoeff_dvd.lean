-- Prove2me | solution 1 for ConjCoord.Proof.tCoeff_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:59:05.656386+00:00
-- url     : https://prove2.me/submissions/ae6551f7-3b85-4d6e-8c66-d9673214643c

module
public import Definitions.Def_ConjCoord_Compute
public import Definitions.Def_ConjCoord_TwoSquares
public import Definitions.Def_ConjCoord_Main
public import Theorems.Thm_ConjCoord_Proof_phi_eq
public import Theorems.Thm_ConjCoord_Proof_phi_dvd

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof
namespace ConjCoord.Proof
theorem _root_.solution (S : SturmInput phi 512) (m : ℕ) : (64 : ℤ) ∣ tCoeff m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    have hphi := phi_dvd S m
    rw [phi_eq] at hphi
    have h1 : (128 : ℤ) ∣ ∑ k ∈ range m,
        2 * (if (k + 1) ^ 2 ≤ m then tCoeff (m - (k + 1) ^ 2) else 0) := by
      refine dvd_sum fun k _ => ?_
      split_ifs with hk
      · obtain ⟨c, hc⟩ := ih (m - (k + 1) ^ 2) (by
          have : 0 < (k + 1) ^ 2 := by positivity
          omega)
        exact ⟨c, by rw [hc]; ring⟩
      · simp
    obtain ⟨c, hc⟩ := h1
    obtain ⟨d, hd⟩ := hphi
    rw [hc] at hd
    exact ⟨d - 2 * c, by linarith⟩
end ConjCoord.Proof
