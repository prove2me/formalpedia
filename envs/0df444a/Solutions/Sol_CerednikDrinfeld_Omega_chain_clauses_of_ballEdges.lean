-- Prove2me | solution 1 for CerednikDrinfeld.Omega.chain_clauses_of_ballEdges
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/0437ef2d-b39b-5d5a-a9da-705d79639622

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_chain_clauses_of_ballEdges

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega

namespace P2mWs2L4

section levels

variable {K₀ : Type} [Field K₀] {C : Type} [Field C] [Algebra K₀ C]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
variable (ϖ : PseudoUniformizer K₀ C)

theorem v_zpow (ℓ : ℤ) :
    Valued.v (algebraMap K₀ C (ϖ.ϖ ^ ℓ)) = Valued.v (algebraMap K₀ C ϖ.ϖ) ^ ℓ := by
  rw [map_zpow₀, map_zpow₀]

theorem v_zpow_pos (ℓ : ℤ) : 0 < Valued.v (algebraMap K₀ C (ϖ.ϖ ^ ℓ)) := by
  rw [v_zpow]; exact zpow_pos ϖ.pos ℓ

theorem v_zpow_ne_zero (ℓ : ℤ) : algebraMap K₀ C (ϖ.ϖ ^ ℓ) ≠ 0 := by
  intro h
  have := v_zpow_pos ϖ ℓ
  rw [h, map_zero] at this
  exact lt_irrefl _ this

theorem v_zpow_le_iff (ℓ ℓ' : ℤ) :
    Valued.v (algebraMap K₀ C (ϖ.ϖ ^ ℓ')) ≤ Valued.v (algebraMap K₀ C (ϖ.ϖ ^ ℓ)) ↔ ℓ ≤ ℓ' := by
  rw [v_zpow, v_zpow]; exact zpow_le_zpow_iff_right_of_lt_one₀ ϖ.pos ϖ.lt_one

theorem v_zpow_lt_iff (ℓ ℓ' : ℤ) :
    Valued.v (algebraMap K₀ C (ϖ.ϖ ^ ℓ')) < Valued.v (algebraMap K₀ C (ϖ.ϖ ^ ℓ)) ↔ ℓ < ℓ' := by
  rw [v_zpow, v_zpow]; exact zpow_lt_zpow_iff_right_of_lt_one₀ ϖ.pos ϖ.lt_one

theorem v_zpow_anti {ℓ ℓ' : ℤ} (h : ℓ ≤ ℓ') :
    Valued.v (algebraMap K₀ C (ϖ.ϖ ^ ℓ')) ≤ Valued.v (algebraMap K₀ C (ϖ.ϖ ^ ℓ)) := (v_zpow_le_iff ϖ ℓ ℓ').2 h

theorem v_zpow_strictAnti {ℓ ℓ' : ℤ} (h : ℓ < ℓ') :
    Valued.v (algebraMap K₀ C (ϖ.ϖ ^ ℓ')) < Valued.v (algebraMap K₀ C (ϖ.ϖ ^ ℓ)) := (v_zpow_lt_iff ϖ ℓ ℓ').2 h

end levels

section discrete

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K₀ : Type} [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
variable {C : Type} [Field C] [Algebra K₀ C]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
variable (ϖ : PseudoUniformizer K₀ C) (ϖ₀ : R) (hϖ₀ : Irreducible ϖ₀) (hϖ : ϖ.ϖ = algebraMap R K₀ ϖ₀)
variable (hint : ∀ a : R, Valued.v (algebraMap K₀ C (algebraMap R K₀ a)) ≤ 1)

include hint in

theorem v_unit (u : Rˣ) : Valued.v (algebraMap K₀ C (algebraMap R K₀ (u : R))) = 1 := by
  apply le_antisymm (hint u)
  have h1 : Valued.v (algebraMap K₀ C (algebraMap R K₀ (u : R))) *
      Valued.v (algebraMap K₀ C (algebraMap R K₀ ((u⁻¹ : Rˣ) : R))) = 1 := by
    rw [← map_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, map_one]
  calc (1 : Γ₀) = _ * _ := h1.symm
    _ ≤ Valued.v (algebraMap K₀ C (algebraMap R K₀ (u : R))) * 1 := by
        gcongr
        exact hint _
    _ = _ := mul_one _

include hϖ₀ hϖ hint in

theorem exists_v_eq_pow (r : R) (hr : r ≠ 0) :
    ∃ a : ℕ, Valued.v (algebraMap K₀ C (algebraMap R K₀ r)) = Valued.v (algebraMap K₀ C ϖ.ϖ) ^ a := by
  obtain ⟨a, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hr hϖ₀
  refine ⟨a, ?_⟩
  have h : Valued.v (algebraMap K₀ C (algebraMap R K₀ (r * (u : R)))) = Valued.v (algebraMap K₀ C ϖ.ϖ) ^ a := by
    rw [hu, map_pow, map_pow, map_pow, hϖ]
  rw [map_mul, map_mul, map_mul, v_unit hint u, mul_one] at h
  exact h

include hϖ₀ hϖ hint in

theorem exists_v_eq_zpow (x : K₀) (hx : x ≠ 0) :
    ∃ ℓ : ℤ, Valued.v (algebraMap K₀ C x) = Valued.v (algebraMap K₀ C (ϖ.ϖ ^ ℓ)) := by
  obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hx (by rw [map_zero, zero_div])
  obtain ⟨a, ha⟩ := exists_v_eq_pow ϖ ϖ₀ hϖ₀ hϖ hint r hr0
  obtain ⟨b, hb⟩ := exists_v_eq_pow ϖ ϖ₀ hϖ₀ hϖ hint s hs0
  refine ⟨(a : ℤ) - (b : ℤ), ?_⟩
  rw [map_div₀, map_div₀, ha, hb, v_zpow, zpow_sub₀ ϖ.pos.ne', zpow_natCast, zpow_natCast]

include hϖ₀ hϖ hint in

theorem v_zpow_pred_le_of_lt (x : K₀) (m : ℤ)
    (h : Valued.v (algebraMap K₀ C (ϖ.ϖ ^ m)) < Valued.v (algebraMap K₀ C x)) :
    Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (m - 1))) ≤ Valued.v (algebraMap K₀ C x) := by
  have hx : x ≠ 0 := by
    rintro rfl
    rw [map_zero, map_zero] at h
    exact not_lt_of_ge zero_le' h
  obtain ⟨ℓ, hℓ⟩ := exists_v_eq_zpow ϖ ϖ₀ hϖ₀ hϖ hint x hx
  rw [hℓ] at h ⊢
  rw [v_zpow_lt_iff] at h
  exact v_zpow_anti ϖ (by omega)

end discrete

end P2mWs2L4

open P2mWs2L4 in
theorem solution
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K₀ : Type) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (C : Type) [Field C] [Algebra K₀ C] [DecidableEq C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
    (ϖ : PseudoUniformizer K₀ C) (ϖ₀ : R) (hϖ₀ : Irreducible ϖ₀) (hϖ : ϖ.ϖ = algebraMap R K₀ ϖ₀)
    [Finite (R ⧸ Ideal.span {ϖ₀})]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ C (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ C a) ≤ 1 → IsLocalization.IsInteger R a)
    (n : ℕ) (k : ℕ) (cen : Fin (k + 1) → K₀) (lev : Fin (k + 1) → ℤ)
    (hlev0 : lev 0 = 1 - (n : ℤ))
    (hroot : ∀ j, Valued.v (algebraMap K₀ C (cen j)) ≤ Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (-(n : ℤ)))))
    (hlow : ∀ j, 1 - (n : ℤ) ≤ lev j)
    (hmono : ∀ i j, i ≤ j → lev i ≤ lev j)
    (hdist : ∀ i j, i ≠ j → lev i = lev j →
      Valued.v (algebraMap K₀ C (ϖ.ϖ ^ lev j)) < Valued.v (algebraMap K₀ C (cen i) - algebraMap K₀ C (cen j)))
    (hpar : ∀ j, lev j = 1 - (n : ℤ) ∨ ∃ i, i < j ∧ lev i = lev j - 1 ∧
      Valued.v (algebraMap K₀ C (cen j) - algebraMap K₀ C (cen i)) ≤ Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (lev j - 1))))
    (P : Fin (k + 1) → Set C)
    (hP : ∀ j, P j = ({z : C | Valued.v (z - algebraMap K₀ C (cen j)) ≤ Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (lev j - 1))) ∧
          ∀ a : K₀, Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (lev j - 1))) ≤ Valued.v (z - algebraMap K₀ C a)} ∪
        {z : C | Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (lev j))) < Valued.v (z - algebraMap K₀ C (cen j)) ∧
          Valued.v (z - algebraMap K₀ C (cen j)) < Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (lev j - 1)))} ∪
        {z : C | Valued.v (z - algebraMap K₀ C (cen j)) ≤ Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (lev j))) ∧
          ∀ a : K₀, Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (lev j))) ≤ Valued.v (z - algebraMap K₀ C a)})) :
    (∀ j, j ≠ 0 → algebraMap K₀ C (ϖ.ϖ ^ (lev j - 1)) ≠ 0) ∧
    (∀ j, j ≠ 0 → ∀ i, i < j → ∀ z ∈ P i,
      Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (lev j - 1))) ≤ Valued.v (z - algebraMap K₀ C (cen j))) ∧
    (∀ j, j ≠ 0 → ∀ z ∈ P j, (∃ i, i < j ∧ z ∈ P i) ∨
      Valued.v (z - algebraMap K₀ C (cen j)) < Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (lev j - 1)))) ∧
    ∃ Z : Fin (k + 1) → Finset C,
      ∀ j, j ≠ 0 → ∀ z : C, Valued.v (z - algebraMap K₀ C (cen j)) = Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (lev j - 1))) →
        (∀ ζ ∈ Z j, Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (lev j - 1))) ≤ Valued.v (z - ζ)) → z ∈ P j ∧ ∃ i, i < j ∧ z ∈ P i := by
  classical

  have tri : ∀ z a b : C, Valued.v (z - a) ≤ max (Valued.v (z - b)) (Valued.v (b - a)) := fun z a b => by
    rw [show z - a = (z - b) + (b - a) by ring]; exact Valued.v.map_add _ _
  have tri_eq_right : ∀ z a b : C, Valued.v (z - b) < Valued.v (b - a) → Valued.v (z - a) = Valued.v (b - a) :=
    fun z a b h => by rw [show z - a = (z - b) + (b - a) by ring]; exact Valued.v.map_add_eq_of_lt_right h
  have tri_eq_left : ∀ z a b : C, Valued.v (b - a) < Valued.v (z - b) → Valued.v (z - a) = Valued.v (z - b) :=
    fun z a b h => by rw [show z - a = (z - b) + (b - a) by ring]; exact Valued.v.map_add_eq_of_lt_left h
  have anti : ∀ {ℓ ℓ' : ℤ}, ℓ ≤ ℓ' →
      Valued.v (algebraMap K₀ C (ϖ.ϖ ^ ℓ')) ≤ Valued.v (algebraMap K₀ C (ϖ.ϖ ^ ℓ)) := fun h => v_zpow_anti ϖ h
  have santi : ∀ {ℓ ℓ' : ℤ}, ℓ < ℓ' →
      Valued.v (algebraMap K₀ C (ϖ.ϖ ^ ℓ')) < Valued.v (algebraMap K₀ C (ϖ.ϖ ^ ℓ)) := fun h => v_zpow_strictAnti ϖ h
  have step : ∀ (x : K₀) (m : ℤ), Valued.v (algebraMap K₀ C (ϖ.ϖ ^ m)) < Valued.v (algebraMap K₀ C x) →
      Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (m - 1))) ≤ Valued.v (algebraMap K₀ C x) :=
    fun x m h => v_zpow_pred_le_of_lt ϖ ϖ₀ hϖ₀ hϖ hint x m h

  have hsib : ∀ i j, i ≠ j → lev i = lev j →
      Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (lev j - 1))) ≤ Valued.v (algebraMap K₀ C (cen i) - algebraMap K₀ C (cen j)) := by
    intro i j hij hl
    have h := hdist i j hij hl
    rw [← map_sub] at h ⊢
    exact step _ _ h

  have hparent : ∀ j : Fin (k + 1), j ≠ 0 → ∃ i, i < j ∧ ∀ z : C,
      Valued.v (z - algebraMap K₀ C (cen j)) ≤ Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (lev j - 1))) →
      (∀ a : K₀, Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (lev j - 1))) ≤ Valued.v (z - algebraMap K₀ C a)) → z ∈ P i := by
    intro j hj
    rcases hpar j with hl | ⟨i, hij, hli, hci⟩
    · refine ⟨0, Fin.pos_of_ne_zero hj, fun z hz1 hz2 => ?_⟩
      have e : lev (0 : Fin (k + 1)) - 1 = lev j - 1 := by rw [hlev0, hl]
      have hlj : lev j - 1 = -(n : ℤ) := by rw [hl]; ring
      rw [hP 0]
      simp only [Set.mem_union, Set.mem_setOf_eq]
      refine Or.inl (Or.inl ⟨?_, ?_⟩)
      · rw [e]
        refine (tri z _ (algebraMap K₀ C (cen j))).trans (max_le hz1 ?_)
        rw [hlj, ← map_sub]
        have := Valued.v.map_sub_le (hroot j) (hroot 0)
        rwa [← map_sub] at this
      · intro a; rw [e]; exact hz2 a
    · refine ⟨i, hij, fun z hz1 hz2 => ?_⟩
      rw [hP i]
      simp only [Set.mem_union, Set.mem_setOf_eq]
      refine Or.inr ⟨?_, ?_⟩
      · rw [hli]
        exact (tri z _ (algebraMap K₀ C (cen j))).trans (max_le hz1 hci)
      · intro a; rw [hli]; exact hz2 a
  refine ⟨fun j _ => v_zpow_ne_zero ϖ _, ?_, ?_, ?_⟩
  ·
    intro j hj i hij z hz
    have hle : lev i ≤ lev j := hmono i j (le_of_lt hij)
    have hne : i ≠ j := ne_of_lt hij
    rw [hP i] at hz
    simp only [Set.mem_union, Set.mem_setOf_eq] at hz
    rcases hz with (⟨hz1, hz2⟩ | ⟨hz1, hz2⟩) | ⟨hz1, hz2⟩
    ·
      exact (anti (by omega)).trans (hz2 (cen j))
    ·
      rcases lt_or_eq_of_le hle with hlt | heq
      · by_contra hcon
        rw [not_le] at hcon

        have h1 : Valued.v (z - algebraMap K₀ C (cen j)) < Valued.v (z - algebraMap K₀ C (cen i)) :=
          hcon.trans_le ((anti (by omega)).trans hz1.le)
        have h2 : Valued.v (algebraMap K₀ C (cen i) - algebraMap K₀ C (cen j)) = Valued.v (z - algebraMap K₀ C (cen i)) := by
          rw [show algebraMap K₀ C (cen i) - algebraMap K₀ C (cen j) =
            (z - algebraMap K₀ C (cen j)) - (z - algebraMap K₀ C (cen i)) by ring, Valued.v.map_sub_swap]
          rw [sub_eq_add_neg, Valued.v.map_add_eq_of_lt_left (by rw [Valued.v.map_neg]; exact h1)]
        have h3 := step (cen i - cen j) (lev i) (by rw [map_sub, h2]; exact hz1)
        rw [map_sub, h2] at h3
        exact absurd hz2 (not_lt.2 h3)
      · rw [tri_eq_right z _ (algebraMap K₀ C (cen i)) (hz2.trans_le (heq ▸ hsib i j hne heq))]
        exact hsib i j hne heq
    ·
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact (anti (by omega)).trans (hz2 (cen j))
      · have h := hsib i j hne heq
        rw [tri_eq_right z _ (algebraMap K₀ C (cen i)) (hz1.trans_lt ((santi (by omega)).trans_le (heq ▸ h)))]
        exact h
  ·
    intro j hj z hz
    obtain ⟨i, hij, hPi⟩ := hparent j hj
    rw [hP j] at hz
    simp only [Set.mem_union, Set.mem_setOf_eq] at hz
    rcases hz with (⟨hz1, hz2⟩ | ⟨hz1, hz2⟩) | ⟨hz1, hz2⟩
    · exact Or.inl ⟨i, hij, hPi z hz1 hz2⟩
    · exact Or.inr hz2
    · exact Or.inr (hz1.trans_lt (santi (by omega)))
  ·
    haveI : Fintype (R ⧸ Ideal.span {ϖ₀}) := Fintype.ofFinite _
    obtain ⟨s, hs⟩ : ∃ s : R ⧸ Ideal.span {ϖ₀} → R, ∀ q, Ideal.Quotient.mk (Ideal.span {ϖ₀}) (s q) = q :=
      ⟨fun q => (Ideal.Quotient.mk_surjective q).choose, fun q => (Ideal.Quotient.mk_surjective q).choose_spec⟩
    refine ⟨fun j => Finset.univ.image
      (fun q => algebraMap K₀ C (cen j + ϖ.ϖ ^ (lev j - 1) * algebraMap R K₀ (s q))), ?_⟩
    intro j hj z hzr hZ
    have hz2 : ∀ a : K₀, Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (lev j - 1))) ≤ Valued.v (z - algebraMap K₀ C a) := by
      intro a
      rcases lt_trichotomy (Valued.v (algebraMap K₀ C a - algebraMap K₀ C (cen j)))
        (Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (lev j - 1)))) with hlt | heq | hgt
      ·
        rw [tri_eq_left z _ (algebraMap K₀ C (cen j)) (by rw [Valued.v.map_sub_swap, hzr]; exact hlt), hzr]
      ·
        have hρ0 : Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (lev j - 1))) ≠ 0 := (v_zpow_pos ϖ _).ne'
        have hϖne : ϖ.ϖ ^ (lev j - 1) ≠ 0 := by
          intro h; apply hρ0; rw [h, map_zero, map_zero]
        obtain ⟨r, hr⟩ := hv ((a - cen j) / ϖ.ϖ ^ (lev j - 1))
          (by rw [map_div₀, map_div₀, map_sub, heq, div_self hρ0])
        obtain ⟨t, ht⟩ : ∃ t : R, s (Ideal.Quotient.mk (Ideal.span {ϖ₀}) r) - r = ϖ₀ * t := by
          have h := hs (Ideal.Quotient.mk (Ideal.span {ϖ₀}) r)
          rw [Ideal.Quotient.eq, Ideal.mem_span_singleton'] at h
          obtain ⟨t, ht⟩ := h
          exact ⟨t, by rw [← ht, mul_comm]⟩
        set ζ : C := algebraMap K₀ C (cen j + ϖ.ϖ ^ (lev j - 1) * algebraMap R K₀ (s (Ideal.Quotient.mk (Ideal.span {ϖ₀}) r)))
          with hζdef
        have hζ : ζ ∈ Finset.univ.image
            (fun q => algebraMap K₀ C (cen j + ϖ.ϖ ^ (lev j - 1) * algebraMap R K₀ (s q))) :=
          Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩

        have hclose : Valued.v (algebraMap K₀ C a - ζ) < Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (lev j - 1))) := by
          have hs' : algebraMap R K₀ (s (Ideal.Quotient.mk (Ideal.span {ϖ₀}) r)) =
              (a - cen j) / ϖ.ϖ ^ (lev j - 1) + ϖ.ϖ * algebraMap R K₀ t := by
            rw [← hr, hϖ, ← map_mul, ← map_add]; congr 1; linear_combination ht
          have hid : a - (cen j + ϖ.ϖ ^ (lev j - 1) * algebraMap R K₀ (s (Ideal.Quotient.mk (Ideal.span {ϖ₀}) r))) =
              -(ϖ.ϖ ^ (lev j - 1) * ϖ.ϖ * algebraMap R K₀ t) := by
            rw [hs']; field_simp; ring
          rw [hζdef, ← map_sub, hid]
          simp only [map_neg, map_mul, Valuation.map_neg]
          calc Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (lev j - 1))) * Valued.v (algebraMap K₀ C ϖ.ϖ) *
                Valued.v (algebraMap K₀ C (algebraMap R K₀ t))
              ≤ Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (lev j - 1))) * Valued.v (algebraMap K₀ C ϖ.ϖ) * 1 := by
                gcongr; exact hint t
            _ = Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (lev j - 1 + 1))) := by
                rw [mul_one, v_zpow, v_zpow, zpow_add_one₀ ϖ.pos.ne']
            _ < Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (lev j - 1))) := santi (by omega)
        by_contra hcon
        rw [not_le] at hcon
        have : Valued.v (z - ζ) < Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (lev j - 1))) := by
          rw [show z - ζ = (z - algebraMap K₀ C a) + (algebraMap K₀ C a - ζ) by ring]
          exact Valued.v.map_add_lt hcon hclose
        exact absurd (hZ ζ hζ) (not_le.2 this)
      ·
        rw [tri_eq_right z _ (algebraMap K₀ C (cen j)) (by rw [hzr, Valued.v.map_sub_swap]; exact hgt),
          Valued.v.map_sub_swap]
        exact hgt.le
    have hz1 : Valued.v (z - algebraMap K₀ C (cen j)) ≤ Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (lev j - 1))) := hzr.le
    obtain ⟨i, hij, hPi⟩ := hparent j hj
    refine ⟨?_, i, hij, hPi z hz1 hz2⟩
    rw [hP j]
    simp only [Set.mem_union, Set.mem_setOf_eq]
    exact Or.inl (Or.inl ⟨hz1, hz2⟩)

end S_CerednikDrinfeld_Omega_chain_clauses_of_ballEdges
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_chain_clauses_of_ballEdges (solution)
