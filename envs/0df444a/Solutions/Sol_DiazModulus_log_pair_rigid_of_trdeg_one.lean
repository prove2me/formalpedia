-- Prove2me | solution 1 for DiazModulus.log_pair_rigid_of_trdeg_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-23T16:03:55.407075+00:00
-- url     : https://prove2.me/submissions/29db2aa6-51a0-474e-830c-3363968aeb51

import Mathlib
import Theorems.Thm_DiazModulus_four_exponentials_trdeg_one

open ComplexConjugate

/-- Complex conjugation as a `ℚ`-algebra map, used to transport algebraicity. -/
noncomputable def lpr_cjQ : ℂ →ₐ[ℚ] ℂ :=
  (Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ).toAlgHom.restrictScalars ℚ

theorem lpr_alg_conj {z : ℂ} (h : IsAlgebraic ℚ z) : IsAlgebraic ℚ (conj z) := by
  obtain ⟨p, hp0, hp⟩ := h
  refine ⟨p, hp0, ?_⟩
  have : Polynomial.aeval (lpr_cjQ z) p = lpr_cjQ (Polynomial.aeval z p) :=
    Polynomial.aeval_algHom_apply lpr_cjQ z p
  rw [show (conj z : ℂ) = lpr_cjQ z from rfl, this, hp, map_zero]

/-- `ℒ` is stable under conjugation. -/
theorem lpr_exp_conj {w : ℂ} (hw : IsAlgebraic ℚ (Complex.exp w)) :
    IsAlgebraic ℚ (Complex.exp (conj w)) := by
  rw [Complex.exp_conj]; exact lpr_alg_conj hw

/-- `ℒ` is a `ℚ`-vector space: rational multiples of logarithms are logarithms. -/
theorem lpr_exp_rat_mul (q : ℚ) {w : ℂ} (hw : IsAlgebraic ℚ (Complex.exp w)) :
    IsAlgebraic ℚ (Complex.exp ((q : ℂ) * w)) := by
  refine IsAlgebraic.of_pow (n := q.den) q.pos ?_
  have hden : ((q.den : ℕ) : ℂ) * (q : ℂ) = ((q.num : ℤ) : ℂ) := by
    rw [Rat.cast_def]; field_simp
  rw [← Complex.exp_nat_mul, ← mul_assoc, hden, Complex.exp_int_mul]
  obtain ⟨m, hm | hm⟩ := Int.eq_nat_or_neg q.num
  · rw [hm, zpow_natCast]; exact hw.pow m
  · rw [hm, zpow_neg, zpow_natCast]; exact (hw.pow m).inv

theorem solution (u v : ℂ) (hu : u ≠ 0) (hv : v ≠ 0)
    (heu : IsAlgebraic ℚ (Complex.exp u)) (hev : IsAlgebraic ℚ (Complex.exp v))
    (c : ℚ) (hc : u * conj u = (c : ℂ) * (v * conj v))
    (htr : Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({u, v, conj u, conj v} : Set ℂ)) ≤ 1) :
    ∃ q : ℚ, v = (q : ℂ) * u ∨ v = (q : ℂ) * conj u := by
  have hcu : conj u ≠ 0 := (map_ne_zero _).2 hu
  have hcv : conj v ≠ 0 := (map_ne_zero _).2 hv
  have hc0 : (c : ℂ) ≠ 0 := by
    rintro h0
    rw [h0, zero_mul] at hc
    exact mul_ne_zero hu hcu hc
  -- the matrix [[u, v], [c·v̄, ū]]
  have hsub : Algebra.adjoin ℚ ({u, v, (c : ℂ) * conj v, conj u} : Set ℂ) ≤
      Algebra.adjoin ℚ ({u, v, conj u, conj v} : Set ℂ) := by
    rw [Algebra.adjoin_le_iff]
    have m : ∀ z ∈ ({u, v, conj u, conj v} : Set ℂ),
        z ∈ Algebra.adjoin ℚ ({u, v, conj u, conj v} : Set ℂ) :=
      fun z hz => Algebra.subset_adjoin hz
    rintro z (rfl | rfl | rfl | rfl)
    · exact m _ (by simp)
    · exact m _ (by simp)
    · exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ c) (m _ (by simp))
    · exact m _ (by simp)
  have htr' : Algebra.trdeg ℚ
      ↥(Algebra.adjoin ℚ ({u, v, (c : ℂ) * conj v, conj u} : Set ℂ)) ≤ 1 :=
    (trdeg_le_of_injective (Subalgebra.inclusion hsub)
      (Subalgebra.inclusion_injective hsub)).trans htr
  rcases DiazModulus.four_exponentials_trdeg_one u v ((c : ℂ) * conj v) (conj u)
      heu hev (lpr_exp_rat_mul c (lpr_exp_conj hev)) (lpr_exp_conj heu)
      hu hv (mul_ne_zero hc0 hcv) hcu (by rw [hc]; ring) htr' with
    ⟨a, b, hab, -, h2⟩ | ⟨a, b, hab, h1, -⟩
  · -- rows dependent: a·v + b·ū = 0
    have ha : (a : ℂ) ≠ 0 := by
      intro ha0
      rw [ha0, zero_mul, zero_add] at h2
      have hb : (b : ℂ) = 0 := (mul_eq_zero.1 h2).resolve_right hcu
      exact hab ⟨by exact_mod_cast ha0, by exact_mod_cast hb⟩
    refine ⟨-b / a, Or.inr ?_⟩
    push_cast
    field_simp
    linear_combination h2
  · -- columns dependent: a·u + b·v = 0
    have hb : (b : ℂ) ≠ 0 := by
      intro hb0
      rw [hb0, zero_mul, add_zero] at h1
      have ha : (a : ℂ) = 0 := (mul_eq_zero.1 h1).resolve_right hu
      exact hab ⟨by exact_mod_cast ha, by exact_mod_cast hb0⟩
    refine ⟨-a / b, Or.inl ?_⟩
    push_cast
    field_simp
    linear_combination h1

#print axioms solution
