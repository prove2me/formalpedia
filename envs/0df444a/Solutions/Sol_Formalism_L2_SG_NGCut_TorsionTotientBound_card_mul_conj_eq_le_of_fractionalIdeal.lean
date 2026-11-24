-- Prove2me | solution 1 for Formalism.L2.SG.NGCut.TorsionTotientBound.card_mul_conj_eq_le_of_fractionalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:06:46.488316+00:00
-- url     : https://prove2.me/submissions/5444d095-5441-462d-9b6b-0622aff5db47

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_MemTorsionOfMulConj
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_CardMulConjEqLeOfFractionalIdeal
import Theorems.Thm_Formalism_L2_SG_NGCut_TorsionTotientBound_cO_coe
import Theorems.Thm_Formalism_L2_SG_NGCut_TorsionTotientBound_count_int


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.NGCut Formalism.L2.SG.NGCut.TorsionTotientBound
namespace Formalism.L2.SG.NGCut.TorsionTotientBound
theorem _root_.solution (E : Type) [Field E] [NumberField E] [IsCMField E]
    (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (m : E) (hJ : J ≠ 0) (hm : m ≠ 0)
    (S : Finset E) (hS : ∀ x ∈ S, x ∈ J ∧ x * IsCMField.complexConj E x = m) :
    (S.card : ℝ) * ((FractionalIdeal.absNorm J : ℚ) : ℝ) ^ 2 ≤
      2 * (Module.finrank ℚ E : ℝ) ^ 2 * |((Algebra.norm ℚ m : ℚ) : ℝ)| := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | ⟨x0, hx0⟩
  · simp only [Finset.card_empty, Nat.cast_zero, zero_mul]
    positivity
  obtain ⟨a, ha⟩ : ∃ a : 𝓞 E, a = (J.den : 𝓞 E) := ⟨_, rfl⟩
  have hcoe : ∀ y : 𝓞 E, algebraMap (𝓞 E) E y = (y : E) := fun _ => rfl
  have ha0 : algebraMap (𝓞 E) E a ≠ 0 := by
    rw [ha]
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors J.den.2
  have hmem : ∀ x ∈ S, ∃ y ∈ J.num, algebraMap (𝓞 E) E y = algebraMap (𝓞 E) E a * x := by
    intro x hx
    have h1 : J.den • x ∈ Submodule.map (Algebra.linearMap (𝓞 E) E) J.num := by
      rw [← J.den_mul_self_eq_num]
      exact Submodule.smul_mem_pointwise_smul x _ _ (hS x hx).1
    obtain ⟨y, hy, hy'⟩ := Submodule.mem_map.1 h1
    refine ⟨y, hy, ?_⟩
    rw [ha]
    simpa [Algebra.smul_def, Submonoid.smul_def] using hy'
  choose! g hgI hg using hmem
  have hginj : Set.InjOn g S := by
    intro x hx y hy hxy
    have h := (hg x hx).symm.trans ((congrArg (algebraMap (𝓞 E) E) hxy).trans (hg y hy))
    exact mul_left_cancel₀ ha0 h
  have hTcard : (S.image g).card = S.card := Finset.card_image_of_injOn hginj
  have hgm : ∀ x ∈ S, algebraMap (𝓞 E) E (g x * cO E (g x)) =
      algebraMap (𝓞 E) E a * IsCMField.complexConj E (algebraMap (𝓞 E) E a) * m := by
    intro x hx
    rw [map_mul, hcoe (cO E (g x)), cO_coe, ← hcoe, hg x hx, map_mul, ← (hS x hx).2]
    ring
  have hT : ∀ y ∈ S.image g, y ∈ J.num ∧ y * cO E y = g x0 * cO E (g x0) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    refine ⟨hgI x hx, ?_⟩
    apply IsFractionRing.injective (𝓞 E) E
    rw [hgm x hx, hgm x0 hx0]
  have hnum : J.num ≠ ⊥ := by
    intro h
    apply hJ
    rw [← FractionalIdeal.num_eq_zero_iff]
    exact h
  have hc0 : IsCMField.complexConj E (algebraMap (𝓞 E) E a) ≠ 0 :=
    (map_ne_zero_iff _ (IsCMField.complexConj E).injective).2 ha0
  have hm'0 : g x0 * cO E (g x0) ≠ 0 := by
    intro h
    have h2 := hgm x0 hx0
    rw [h, map_zero] at h2
    exact (mul_ne_zero (mul_ne_zero ha0 hc0) hm) h2.symm
  have key := count_int J.num hnum (g x0 * cO E (g x0)) hm'0 (S.image g) hT
  have key' : ((((S.image g).card * Ideal.absNorm J.num ^ 2 : ℕ)) : ℝ) ≤
      ((2 * Module.finrank ℚ E ^ 2 * (Algebra.norm ℤ (g x0 * cO E (g x0))).natAbs : ℕ) : ℝ) := by
    exact_mod_cast key
  push_cast [Nat.cast_natAbs, Int.cast_abs] at key'
  rw [hTcard] at key'
  have hconj : ∀ y : E, Algebra.norm ℚ (IsCMField.complexConj E y) = Algebra.norm ℚ y := by
    intro y
    exact Algebra.norm_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) y
  have hNaQ : ((Algebra.norm ℤ a : ℤ) : ℚ) = Algebra.norm ℚ (algebraMap (𝓞 E) E a) :=
    Algebra.coe_norm_int a
  have hNa0 : ((Algebra.norm ℤ a : ℤ) : ℝ) ≠ 0 := by
    have h : Algebra.norm ℚ (algebraMap (𝓞 E) E a) ≠ 0 := Algebra.norm_ne_zero_iff.2 ha0
    rw [← hNaQ] at h
    exact_mod_cast h
  have hNm' : ((Algebra.norm ℤ (g x0 * cO E (g x0)) : ℤ) : ℝ) =
      ((Algebra.norm ℤ a : ℤ) : ℝ) ^ 2 * ((Algebra.norm ℚ m : ℚ) : ℝ) := by
    have h : ((Algebra.norm ℤ (g x0 * cO E (g x0)) : ℤ) : ℚ) =
        Algebra.norm ℚ (algebraMap (𝓞 E) E a) ^ 2 * Algebra.norm ℚ m := by
      rw [Algebra.coe_norm_int, ← hcoe, hgm x0 hx0, map_mul (Algebra.norm ℚ), map_mul (Algebra.norm ℚ),
        hconj]
      ring
    have h3 : ((Algebra.norm ℤ (g x0 * cO E (g x0)) : ℤ) : ℝ) =
        (((Algebra.norm ℤ (g x0 * cO E (g x0)) : ℤ) : ℚ) : ℝ) := by norm_cast
    rw [h3, h, ← hNaQ]
    push_cast
    ring
  have hJn : ((FractionalIdeal.absNorm J : ℚ) : ℝ) =
      ((Ideal.absNorm J.num : ℕ) : ℝ) / |((Algebra.norm ℤ a : ℤ) : ℝ)| := by
    rw [FractionalIdeal.absNorm_eq, ha]
    push_cast
    rfl
  have hpos : (0 : ℝ) < ((Algebra.norm ℤ a : ℤ) : ℝ) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hNa0))
  rw [hJn, div_pow, sq_abs, mul_div_assoc', div_le_iff₀ hpos]
  calc (S.card : ℝ) * ((Ideal.absNorm J.num : ℕ) : ℝ) ^ 2
      ≤ 2 * (Module.finrank ℚ E : ℝ) ^ 2 * |((Algebra.norm ℤ (g x0 * cO E (g x0)) : ℤ) : ℝ)| := key'
    _ = 2 * (Module.finrank ℚ E : ℝ) ^ 2 * |((Algebra.norm ℚ m : ℚ) : ℝ)| *
        ((Algebra.norm ℤ a : ℤ) : ℝ) ^ 2 := by
      rw [hNm', abs_mul, abs_of_nonneg (sq_nonneg _)]
      ring
end Formalism.L2.SG.NGCut.TorsionTotientBound
