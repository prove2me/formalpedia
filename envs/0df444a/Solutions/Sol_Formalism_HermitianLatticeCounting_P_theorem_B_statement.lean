-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.theorem_B_statement
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:39.1678+00:00
-- url     : https://prove2.me/submissions/d9f47cc4-e2f5-4fa3-b98e-d8b6f1396e3c

import Definitions.Def_Formalism_FlagUnipotentLattices_DetIndexProductHyperbolicInequality
import Definitions.Def_Formalism_HyperbolicPlaceProducts_ArithmeticCountRevised
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ComplexMultiplicationRoot
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_integer_group_preservation
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_complex_multiplication_root
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_IntegralityLocalGlobal_isInt_mul
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_IntegralityLocalGlobal_isInt_add
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_IntegralityLocalGlobal_divGlob
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s_integrality
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_IntegralityLocalGlobal_formEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Formalism.HermitianLatticeCounting.LocalIntegralStructure
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open IntegralityLocalGlobal
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.LocalIntegralStructure.ThmB := by
  intro E _ _ σ hσ hcx T T' g a b c d x hT hT' hg hiso hZZ hloc hx hxw
  have hTpos : 0 < T := by omega
  have hT'pos : 0 < T' := by omega
  have hTr : (0 : ℝ) < T := by exact_mod_cast hTpos
  have hT'r : (0 : ℝ) < T' := by exact_mod_cast hT'pos
  have hgr : (0 : ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  have hm : ∀ w : InfinitePlace E, w.mult = 2 := fun w =>
    NumberField.InfinitePlace.mult_isComplex ⟨w, hcx w⟩
  have hn : Module.finrank ℚ E = 2 * Fintype.card (InfinitePlace E) := by
    rw [← NumberField.InfinitePlace.sum_mult_eq]
    simp only [hm, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    ring
  have hne : Nonempty (InfinitePlace E) := by
    first
    | infer_instance
    | (apply Fintype.card_pos_iff.mp
       have := Module.finrank_pos (R := ℚ) (M := E)
       omega)
  obtain ⟨w0⟩ := hne
  have hcard : 1 ≤ Fintype.card (InfinitePlace E) := Fintype.card_pos_iff.mpr ⟨w0⟩
  have hnw : ∀ (w : InfinitePlace E) (y : E), w y = ‖w.embedding y‖ := fun w y =>
    (NumberField.InfinitePlace.norm_embedding_eq w y).symm
  have hI : ∀ y : 𝓞 E, IsInt (y : E) := fun y => by unfold IsInt; exact ⟨y, rfl⟩
  have hm1 : IsInt (-1 : E) := by simpa using hI (-1)
  have h1 : IsInt (1 : E) := by simpa using hI 1
  have normge : ∀ β : 𝓞 E, β ≠ 0 → 1 ≤ ∏ w : InfinitePlace E, (w (β : E)) ^ 2 := by
    intro β hβ
    have hp := NumberField.InfinitePlace.prod_eq_abs_norm (β : E)
    simp only [hm] at hp
    rw [hp, ← Algebra.coe_norm_int]
    have hn0 : Algebra.norm ℤ β ≠ 0 := Algebra.norm_ne_zero_iff.mpr hβ
    have h2 : (1 : ℤ) ≤ |Algebra.norm ℤ β| := Int.one_le_abs hn0
    exact_mod_cast h2
  have hwn : ∀ w : InfinitePlace E,
      (T : ℝ) ^ 2 * ‖w.embedding b‖ ^ 2 = (T' : ℝ) ^ 2 * ‖w.embedding c‖ ^ 2 := fun w =>
    formEq _ _ _ _ _ _ (hiso w.embedding)
  have zz := integer_group_preservation E g a b c d hZZ
  have unit1 : ∀ (y : E) (N : ℕ), 3 ≤ N → IsInt (y - 1) →
      (∀ P : Ideal (𝓞 E), P.IsPrime → (N : 𝓞 E) ∈ P → LocIn P (y - 1) N) →
      (∀ w : InfinitePlace E, ‖w.embedding y‖ = 1) → y = 1 := by
    intro y N hN hi hl hy
    obtain ⟨β, hβ⟩ := divGlob (y - 1) N (by omega) hi hl
    by_contra hne
    have hβ0 : β ≠ 0 := by
      rintro rfl
      apply hne
      have h0 : y - 1 = 0 := by rw [hβ]; simp
      exact sub_eq_zero.mp h0
    have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
    have hb : ∀ w : InfinitePlace E, (w (β : E)) ^ 2 ≤ 4 / 9 := by
      intro w
      have h5 : w.embedding y - 1 = (N : ℂ) * w.embedding (β : E) := by
        rw [← map_one w.embedding, ← map_sub, hβ, map_mul, map_natCast]
      have e1 : (N : ℝ) * ‖w.embedding (β : E)‖ = ‖w.embedding y - 1‖ := by
        rw [h5, norm_mul]
        simp
      have e2 : ‖w.embedding y - 1‖ ≤ 2 := by
        calc ‖w.embedding y - 1‖ ≤ ‖w.embedding y‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ = 2 := by rw [hy w, norm_one]; norm_num
      have e3 : 0 ≤ ‖w.embedding (β : E)‖ := norm_nonneg _
      have e4 : ‖w.embedding (β : E)‖ ≤ 2 / 3 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hNr) e3]
      rw [hnw]
      nlinarith [mul_nonneg e3 (sub_nonneg.mpr e4)]
    have hprod : ∏ w : InfinitePlace E, (w (β : E)) ^ 2 ≤ ∏ _w : InfinitePlace E, (4 / 9 : ℝ) :=
      Finset.prod_le_prod (fun w _ => sq_nonneg _) (fun w _ => hb w)
    rw [Finset.prod_const, Finset.card_univ] at hprod
    have h49 : (4 / 9 : ℝ) ^ Fintype.card (InfinitePlace E) ≤ 4 / 9 :=
      pow_le_of_le_one (by norm_num) (by norm_num) (by omega)
    linarith [normge β hβ0]
  by_cases hc0 : c = 0
  · left
    have hb0 : b = 0 := by
      have h := hwn w0
      rw [hc0, map_zero, norm_zero] at h
      have h2 : ‖w0.embedding b‖ ^ 2 = 0 :=
        mul_left_cancel₀ (pow_ne_zero 2 hTr.ne') (by rw [h]; ring)
      have h3 : w0.embedding b = 0 := norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h2)
      exact (map_eq_zero_iff _ w0.embedding.injective).mp h3
    have ha1 : ∀ w : InfinitePlace E, ‖w.embedding a‖ = 1 := by
      intro w
      have h := hiso w.embedding 1 0
      rw [hb0, hc0] at h
      simp only [map_zero, mul_one, mul_zero, zero_mul, add_zero, zero_add, norm_zero, norm_one] at h
      have h2 : (T : ℝ) * (‖w.embedding a‖ ^ 2 - 1) = 0 := by linear_combination h
      have h3 := (mul_eq_zero.mp h2).resolve_left hTr.ne'
      nlinarith [norm_nonneg (w.embedding a)]
    have hd1 : ∀ w : InfinitePlace E, ‖w.embedding d‖ = 1 := by
      intro w
      have h := hiso w.embedding 0 1
      rw [hb0, hc0] at h
      simp only [map_zero, mul_one, mul_zero, zero_mul, add_zero, zero_add, norm_zero, norm_one] at h
      have h2 : (T' : ℝ) * (‖w.embedding d‖ ^ 2 - 1) = 0 := by linear_combination -h
      have h3 := (mul_eq_zero.mp h2).resolve_left hT'r.ne'
      nlinarith [norm_nonneg (w.embedding d)]
    have ha : a = 1 := unit1 a T hT
      (by convert isInt_add zz.2.2.2.2.1 hm1 using 1; rw [hb0]; ring)
      (fun P hP h => (hloc P hP (Or.inl h)).1) ha1
    have hd : d = 1 := unit1 d T' hT'
      (by convert isInt_mul hm1 (isInt_add zz.2.2.2.2.2 h1) using 1; rw [hc0]; ring)
      (fun P hP h => (hloc P hP (Or.inr h)).2.2.2) hd1
    exact ⟨ha, hb0, hc0, hd⟩
  · right
    obtain ⟨s, hs1⟩ : ∃ s : E, s = (T' : E) * c * σ c / (T : E) := ⟨_, rfl⟩
    have hs2 : s = (T : E) * b * σ b / (T' : E) := by
      rw [hs1]
      apply w0.embedding.injective
      have hconj : ∀ z : E,
          w0.embedding z * w0.embedding (σ z) = ((‖w0.embedding z‖ ^ 2 : ℝ) : ℂ) := by
        intro z
        rw [hσ, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      simp only [map_div₀, map_mul, map_natCast]
      rw [mul_assoc, mul_assoc, hconj, hconj]
      have hTc : (T : ℂ) ≠ 0 := by exact_mod_cast hTpos.ne'
      have hT'c : (T' : ℂ) ≠ 0 := by exact_mod_cast hT'pos.ne'
      rw [div_eq_div_iff hTc hT'c]
      have h' := congrArg (fun r : ℝ => (r : ℂ)) (hwn w0)
      push_cast at h' ⊢
      linear_combination -h'
    obtain ⟨β, hβ⟩ := s_integrality E σ T T' g s b c hTpos hT'pos hs1 hs2 zz.2.1 zz.2.2.1
      (fun P hP h => (hloc P hP (Or.inl h)).2.1) (fun P hP h => (hloc P hP (Or.inr h)).2.2.1)
    have hs0 : s ≠ 0 := by
      rw [hs1]
      have hσc : σ c ≠ 0 := fun h => hc0 (σ.injective (by rw [h, map_zero]))
      have hT0 : (T : E) ≠ 0 := Nat.cast_ne_zero.mpr hTpos.ne'
      have hT'0 : (T' : E) ≠ 0 := Nat.cast_ne_zero.mpr hT'pos.ne'
      exact div_ne_zero (mul_ne_zero (mul_ne_zero hT'0 hc0) hσc) hT0
    have hβ0 : β ≠ 0 := by
      rintro rfl
      have hg0 : (g : E) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have h0 : (g : E) ^ 2 * s = 0 := by rw [hβ]; simp
      exact hs0 ((mul_eq_zero.mp h0).resolve_left (pow_ne_zero 2 hg0))
    set q : ℝ := (T : ℝ) * T' / (g : ℝ) ^ 2 with hq_def
    have hq : 0 < q := div_pos (mul_pos hTr hT'r) (pow_pos hgr 2)
    have key : ∀ w : InfinitePlace E, q ^ 2 * (w (β : E)) ^ 2 ≤ (x w ^ 2) ^ 2 := by
      intro w
      have A : (g : ℝ) ^ 2 * ‖w.embedding s‖ = (T : ℝ) * T' * ‖w.embedding (β : E)‖ := by
        have h := congrArg (fun y => ‖w.embedding y‖) hβ
        simpa [map_mul, map_pow, map_natCast, norm_mul, norm_pow] using h
      have B : ‖w.embedding s‖ = (T' : ℝ) * ‖w.embedding c‖ ^ 2 / T := by
        rw [hs1]
        simp [hσ, norm_div] <;> ring
      have C := hxw w
      rw [hnw w c] at C
      have hs_le : ‖w.embedding s‖ ≤ x w ^ 2 := by rw [B]; exact C
      have hs_eq : ‖w.embedding s‖ = q * ‖w.embedding (β : E)‖ := by
        rw [hq_def, div_mul_eq_mul_div, eq_div_iff (pow_ne_zero 2 hgr.ne')]
        linear_combination A
      rw [hnw w, ← mul_pow, ← hs_eq]
      first
      | exact pow_le_pow_left (norm_nonneg _) hs_le 2
      | exact pow_le_pow_left₀ (norm_nonneg _) hs_le 2
      | nlinarith [norm_nonneg (w.embedding s)]
    apply complex_multiplication_root E q x hcx hq hx
    simp only [hm]
    rw [hn, pow_mul]
    have hprod : ∏ w : InfinitePlace E, q ^ 2 * (w (β : E)) ^ 2 ≤
        ∏ w : InfinitePlace E, (x w ^ 2) ^ 2 :=
      Finset.prod_le_prod (fun w _ => by positivity) (fun w _ => key w)
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ] at hprod
    have hqn : 0 ≤ (q ^ 2) ^ Fintype.card (InfinitePlace E) := by positivity
    have h3 := mul_le_mul_of_nonneg_left (normge β hβ0) hqn
    rw [mul_one] at h3
    linarith
end Formalism.HermitianLatticeCounting.P
