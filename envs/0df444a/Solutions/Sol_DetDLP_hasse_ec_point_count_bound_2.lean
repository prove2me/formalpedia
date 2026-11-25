-- Prove2me | solution 2 for DetDLP.hasse_ec_point_count_bound
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T16:39:11.963504+00:00
-- url     : https://prove2.me/submissions/e8df3da9-df81-4846-9fd6-abda8628b236

import Theorems.Thm_WeilConjectures_hasse_elliptic_curve
import Definitions.Def_DetDLP_FactorBase

set_option autoImplicit false
open DetDLP

private theorem m89_point_card {k L : Type} [Field k] [Field L] [Algebra k L]
    (E : WeierstrassCurve k) (e : k ≃ₐ[k] L) :
    Nat.card (E.baseChange L).toAffine.Point = Nat.card E.toAffine.Point := by
  let f := algebraMap k L
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    exact ⟨x, by simpa [f] using (e.commutes x).symm⟩
  let push : E.toAffine.Point → (E.baseChange L).toAffine.Point
    | .zero => .zero
    | .some x y h => .some (f x) (f y) ((E.toAffine.map_nonsingular f.injective x y).2 h)
  have hinj : Function.Injective push := by
    rintro (_ | ⟨x, y, h⟩) (_ | ⟨x', y', h'⟩) heq
    · rfl
    · cases heq
    · cases heq
    · obtain ⟨hx, hy⟩ := WeierstrassCurve.Affine.Point.some.inj heq
      cases f.injective hx
      cases f.injective hy
      rfl
  have hsurj : Function.Surjective push := by
    rintro (_ | ⟨x, y, h⟩)
    · exact ⟨.zero, rfl⟩
    · obtain ⟨x, rfl⟩ := hf x
      obtain ⟨y, rfl⟩ := hf y
      exact ⟨.some x y ((E.toAffine.map_nonsingular f.injective x y).1 h), rfl⟩
  exact (Nat.card_congr (Equiv.ofBijective push ⟨hinj, hsurj⟩)).symm

private theorem m89_card_one (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Finite k] [CharP k p]
    (E : WeierstrassCurve k) :
    Nat.card (E.baseChange (FiniteField.Extension k p 1)).toAffine.Point = Nat.card E.toAffine.Point :=
  m89_point_card E (FiniteField.algEquivExtension k p 1 k (by simp))

theorem solution :
    ∀ (p : ℕ) [Fact p.Prime], 3 < p →
      ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic],
        letI := ecPointFintype E
        |(Fintype.card E.toAffine.Point : ℝ) - ((p : ℝ) + 1)| ≤ 2 * Real.sqrt (p : ℝ) := by
  intro p hp _ E hE
  letI := ecPointFintype E
  obtain ⟨a, b, _, ha, hb, h⟩ := WeilConjectures.hasse_elliptic_curve p (ZMod p) E
  have h1 := h 1
  have hc := m89_card_one p (ZMod p) E
  have hk : Nat.card (ZMod p) = p := by rw [Nat.card_eq_fintype_card, ZMod.card]
  rw [hc, hk, Nat.card_eq_fintype_card] at h1
  simp only [pow_one] at h1
  rw [hk] at ha hb
  have hdiff : (((Fintype.card E.toAffine.Point : ℝ) - ((p : ℝ) + 1) : ℝ) : ℂ) = -(a + b) := by
    push_cast
    linear_combination h1
  calc
    _ = ‖(((Fintype.card E.toAffine.Point : ℝ) - ((p : ℝ) + 1) : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    _ = ‖a + b‖ := by rw [hdiff, norm_neg]
    _ ≤ ‖a‖ + ‖b‖ := norm_add_le _ _
    _ = _ := by rw [ha, hb, two_mul]

#print axioms solution
