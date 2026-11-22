-- Prove2me | solution 1 for Bernstein.addSubgroups
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-22T17:49:57.854659+00:00
-- url     : https://prove2.me/submissions/b0d4cb24-ece7-4488-afa4-b8df84bfc140

import Mathlib
import Definitions.Def_Curve25519Bernstein

namespace Bernstein.GroupLawDev

open WeierstrassCurve WeierstrassCurve.Affine

variable {p : ℕ} [Fact p.Prime] {A : ℤ}

lemma Ea₁ : (Ecurve p A).a₁ = 0 := by
  simp [Ecurve, curve]

lemma Ea₂ : (Ecurve p A).a₂ = emb p (A : ZMod p) := by
  simp [Ecurve, curve]

lemma Ea₄ : (Ecurve p A).a₄ = 1 := by
  simp [Ecurve, curve]

lemma negY_eq (x y : Fp2 p) : (Ecurve p A).negY x y = -y := by
  simp [Affine.negY, Ecurve, curve]

lemma some_eq {x y x' y' : Fp2 p} {h : (Ecurve p A).Nonsingular x y} (hx : x = x') (hy : y = y') :
    ∃ h' : (Ecurve p A).Nonsingular x' y', (Affine.Point.some x y h : Pt p A) = .some x' y' h' := by
  subst hx; subst hy; exact ⟨h, rfl⟩

lemma addX_eq (x₁ x₂ l : Fp2 p) :
    (Ecurve p A).addX x₁ x₂ l = l ^ 2 - emb p (A : ZMod p) - x₁ - x₂ := by
  simp only [Affine.addX, Ea₁, Ea₂]; ring

lemma addY_eq (x₁ x₂ y₁ l : Fp2 p) :
    (Ecurve p A).addY x₁ x₂ y₁ l = l * (x₁ - (Ecurve p A).addX x₁ x₂ l) - y₁ := by
  simp only [Affine.addY, Affine.negAddY, negY_eq]; ring

/-- The sets `{∞} ∪ {(x, t c) : x, c ∈ F_p}` for `t² ∈ F_p` are subgroups. -/
lemma S_subgroup (t : Fp2 p) (d : ZMod p) (ht : t ^ 2 = emb p d) :
    ∃ H : AddSubgroup (Pt p A), (H : Set (Pt p A)) =
      {Q | Q = 0 ∨ ∃ (x c : ZMod p) (h : _), Q = .some (emb p x) (t * emb p c) h} := by
  refine ⟨{ carrier := {Q | Q = 0 ∨ ∃ (x c : ZMod p) (h : _), Q = .some (emb p x) (t * emb p c) h}
            zero_mem' := Or.inl rfl
            add_mem' := ?_
            neg_mem' := ?_ }, rfl⟩
  · rintro P Q (rfl | ⟨x₁, c₁, h₁, rfl⟩) (rfl | ⟨x₂, c₂, h₂, rfl⟩)
    · exact Or.inl (zero_add 0)
    · exact Or.inr ⟨x₂, c₂, h₂, zero_add _⟩
    · exact Or.inr ⟨x₁, c₁, h₁, add_zero _⟩
    · by_cases hxy : emb p x₁ = emb p x₂ ∧ t * emb p c₁ = (Ecurve p A).negY (emb p x₂) (t * emb p c₂)
      · exact Or.inl (Affine.Point.add_of_Y_eq hxy.1 hxy.2)
      · rw [Affine.Point.add_some hxy]
        obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ZMod p,
            (Ecurve p A).slope (emb p x₁) (emb p x₂) (t * emb p c₁) (t * emb p c₂) = t * emb p ℓ := by
          by_cases hx : emb p x₁ = emb p x₂
          · have hy : t * emb p c₁ ≠ (Ecurve p A).negY (emb p x₂) (t * emb p c₂) :=
              fun e => hxy ⟨hx, e⟩
            rw [Affine.slope_of_Y_ne hx hy, Ea₁, Ea₂, Ea₄, negY_eq]
            refine ⟨(3 * x₁ ^ 2 + 2 * (A : ZMod p) * x₁ + 1) / (2 * d * c₁), ?_⟩
            by_cases ht0 : t = 0
            · simp [ht0]
            by_cases hc : c₁ = 0
            · simp [hc]
            have hd : d ≠ 0 := by
              rintro rfl; apply ht0; simpa using ht
            have hc' : emb p c₁ ≠ 0 := by simpa using hc
            simp only [map_div₀, map_mul, map_add, map_pow, map_ofNat, map_one, ← ht]
            field_simp
            ring
          · rw [Affine.slope_of_X_ne hx]
            refine ⟨(c₁ - c₂) / (x₁ - x₂), ?_⟩
            simp only [map_div₀, map_sub]
            ring
        refine Or.inr ⟨d * ℓ ^ 2 - A - x₁ - x₂, -(ℓ * (d * ℓ ^ 2 - A - x₁ - x₂ - x₁) + c₁), ?_⟩
        refine some_eq ?_ ?_
        · rw [addX_eq, hℓ]
          simp only [map_sub, map_mul, map_pow, ← ht]; ring
        · rw [addY_eq, addX_eq, hℓ]
          simp only [map_sub, map_mul, map_pow, map_neg, map_add, ← ht]; ring
  · rintro Q (rfl | ⟨x, c, h, rfl⟩)
    · exact Or.inl neg_zero
    · rw [Affine.Point.neg_some]
      obtain ⟨h', e⟩ := some_eq (h := (Affine.nonsingular_neg ..).mpr h) rfl
        (show (Ecurve p A).negY (emb p x) (t * emb p c) = t * emb p (-c) by
          rw [negY_eq, map_neg]; ring)
      exact Or.inr ⟨x, -c, h', e⟩

theorem addSubgroups_dev (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (A : ℤ)
    (hA : ¬ IsSquare ((A : ZMod p) ^ 2 - 4)) :
    (∃ H : AddSubgroup (Pt p A),
      (H : Set (Pt p A)) =
        {Q | Q = 0 ∨ ∃ h : (Ecurve p A).Nonsingular 0 0, Q = .some 0 0 h}) ∧
    (∃ H : AddSubgroup (Pt p A), (H : Set (Pt p A)) = fpPoints p A) ∧
    (∀ s : Fp2 p, s ^ 2 = emb p (delta p : ZMod p) →
      ∃ H : AddSubgroup (Pt p A), (H : Set (Pt p A)) = twistPoints p A s) := by
  refine ⟨?_, ?_, fun s hs => S_subgroup s _ hs⟩
  · refine ⟨{ carrier := {Q | Q = 0 ∨ ∃ h : (Ecurve p A).Nonsingular 0 0, Q = .some 0 0 h}
              zero_mem' := Or.inl rfl
              add_mem' := ?_
              neg_mem' := ?_ }, rfl⟩
    · rintro P Q (rfl | ⟨h₁, rfl⟩) (rfl | ⟨h₂, rfl⟩)
      · exact Or.inl (zero_add 0)
      · exact Or.inr ⟨h₂, zero_add _⟩
      · exact Or.inr ⟨h₁, add_zero _⟩
      · exact Or.inl (Affine.Point.add_of_Y_eq rfl (by rw [negY_eq, neg_zero]))
    · rintro Q (rfl | ⟨h, rfl⟩)
      · exact Or.inl neg_zero
      · rw [Affine.Point.neg_some]
        obtain ⟨h', e⟩ := some_eq (h := (Affine.nonsingular_neg ..).mpr h) rfl
          (show (Ecurve p A).negY 0 0 = 0 by rw [negY_eq, neg_zero])
        exact Or.inr ⟨h', e⟩
  · obtain ⟨H, hH⟩ := S_subgroup (p := p) (A := A) 1 1 (by simp)
    refine ⟨H, ?_⟩
    rw [hH]
    ext Q
    simp only [one_mul, fpPoints, Set.mem_ofPred_eq]

end Bernstein.GroupLawDev

theorem solution : type_of% @Bernstein.GroupLawDev.addSubgroups_dev := @Bernstein.GroupLawDev.addSubgroups_dev
