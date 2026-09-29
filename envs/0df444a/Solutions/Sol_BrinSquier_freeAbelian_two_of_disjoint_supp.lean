-- Prove2me | solution 1 for BrinSquier.freeAbelian_two_of_disjoint_supp
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-12T22:27:05.392834+00:00
-- url     : https://prove2.me/submissions/570bd1f3-82ea-484a-be06-da1d16653f05

import Definitions.Def_BrinSquier
import Mathlib

namespace BS_aux

/-- If `w` fixes `x`, so does every integer power of `w`. -/
lemma zpow_fix {w : ℝ ≃o ℝ} {x : ℝ} (h : w x = x) : ∀ k : ℤ, (w ^ k) x = x := by
  have hinv : w⁻¹ x = x := w.injective (by rw [RelIso.apply_inv_self, h])
  intro k
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih =>
      rw [zpow_add w (n : ℤ) 1, zpow_one]
      show (w ^ (n : ℤ)) (w x) = x
      rw [h, ih]
  | pred n ih =>
      rw [show (-(n : ℤ) - 1) = (-(n : ℤ)) + (-1) by ring, zpow_add w (-(n : ℤ)) (-1),
        zpow_neg_one]
      show (w ^ (-(n : ℤ))) (w⁻¹ x) = x
      rw [hinv, ih]

/-- The support of a power is contained in the support. -/
lemma supp_zpow_subset (w : ℝ ≃o ℝ) (k : ℤ) : BrinSquier.supp (w ^ k) ⊆ BrinSquier.supp w := by
  intro x hx
  by_contra hnot
  exact hx (zpow_fix (not_not.1 hnot) k)

end BS_aux

open BS_aux in
theorem solution {u v : ℝ ≃o ℝ}
    (hu : ∀ k : ℤ, k ≠ 0 → u ^ k ≠ 1) (hv : ∀ k : ℤ, k ≠ 0 → v ^ k ≠ 1)
    (hdisj : Disjoint (BrinSquier.supp u) (BrinSquier.supp v)) :
    Function.Injective (fun p : ℤ × ℤ => u ^ p.1 * v ^ p.2) := by
  rintro ⟨m, n⟩ ⟨m', n'⟩ h
  dsimp only at h
  have key : u ^ (m - m') = v ^ (n' - n) := by
    have h2 : (u ^ m')⁻¹ * (u ^ m * v ^ n) * (v ^ n)⁻¹
            = (u ^ m')⁻¹ * (u ^ m' * v ^ n') * (v ^ n)⁻¹ := by rw [h]
    calc u ^ (m - m')
        = (u ^ m')⁻¹ * (u ^ m * v ^ n) * (v ^ n)⁻¹ := by group
      _ = (u ^ m')⁻¹ * (u ^ m' * v ^ n') * (v ^ n)⁻¹ := h2
      _ = v ^ (n' - n) := by group
  -- the common element is supported in both, hence nowhere
  have hone : u ^ (m - m') = 1 := by
    have hsu := supp_zpow_subset u (m - m')
    have hsv : BrinSquier.supp (u ^ (m - m')) ⊆ BrinSquier.supp v := by
      rw [key]; exact supp_zpow_subset v (n' - n)
    apply RelIso.ext
    intro x
    show (u ^ (m - m')) x = x
    by_contra hne
    exact Set.disjoint_left.mp hdisj (hsu hne) (hsv hne)
  have hm : m = m' := by
    by_contra hne
    exact hu (m - m') (sub_ne_zero.2 hne) hone
  have hn : n = n' := by
    by_contra hne
    exact hv (n' - n) (sub_ne_zero.2 (Ne.symm hne)) (key ▸ hone)
  simp [hm, hn]
