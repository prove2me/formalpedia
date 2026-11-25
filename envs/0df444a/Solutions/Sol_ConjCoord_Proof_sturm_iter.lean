-- Prove2me | solution 1 for ConjCoord.Proof.sturm_iter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:53:02.166085+00:00
-- url     : https://prove2.me/submissions/d5abe730-f9e4-4ee5-930d-596625056911

module
public import Definitions.Def_ConjCoord_Compute
public import Definitions.Def_ConjCoord_TwoSquares
public import Definitions.Def_ConjCoord_Main

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof
namespace ConjCoord.Proof
theorem _root_.solution {f : ℕ → ℤ} {B : ℕ} (S : SturmInput f B) (k : ℕ) :
    ∀ g ∈ S.M, (∀ n ≤ B, (2 : ℤ) ^ k ∣ g n) → ∀ n, (2 : ℤ) ^ k ∣ g n := by
  induction k with
  | zero => intro g _ _ n; simp
  | succ k ih =>
    intro g hg hB n
    have h2 : ∀ n, (2 : ℤ) ∣ g n := S.sturm g hg fun n hn =>
      (dvd_pow_self 2 (Nat.succ_ne_zero k)).trans (hB n hn)
    have hg' := S.half_mem g hg h2
    have hB' : ∀ n ≤ B, (2 : ℤ) ^ k ∣ (fun n => g n / 2) n := by
      intro n hn
      obtain ⟨c, hc⟩ := hB n hn
      refine ⟨c, ?_⟩
      simp only [hc, pow_succ]
      rw [mul_comm ((2 : ℤ) ^ k) 2, mul_assoc, Int.mul_ediv_cancel_left _ two_ne_zero]
    obtain ⟨c, hc⟩ := ih _ hg' hB' n
    obtain ⟨d, hd⟩ := h2 n
    refine ⟨c, ?_⟩
    rw [hd, Int.mul_ediv_cancel_left _ two_ne_zero] at hc
    rw [hd, hc, pow_succ]; ring
end ConjCoord.Proof
