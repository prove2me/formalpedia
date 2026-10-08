-- Prove2me | solution 1 for BookProof.ChapterA.AntiUnitary.comp_inner
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T16:42:42.477322+00:00
-- url     : https://prove2.me/submissions/c6698b56-9247-40c8-ad53-dd7762a2dd25

-- Generated from ChapterA1.lean — theorem BookProof.ChapterA.AntiUnitary.comp_inner
import Mathlib
import Definitions.Def_ChapterA1
import Definitions.Def_ChapterStoneMeasurable
import Definitions.Def_ChapterA
open BookProof.ChapterA
open BookProof.ChapterA

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]


open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace

private theorem anti_inner (θ : AntiUnitary V) (x y : V) :
    inner ℂ (θ x) (θ y) = conj (inner ℂ x y) := by
  have hi : θ (Complex.I • y) = -Complex.I • θ y := by
    rw [θ.map_smulₛₗ]
    change conj Complex.I • θ y = -Complex.I • θ y
    rw [Complex.conj_I]
  have ha : ‖θ x + θ y‖ = ‖x + y‖ := by
    rw [← θ.map_add, θ.norm_map]
  have hb : ‖θ x - θ y‖ = ‖x - y‖ := by
    rw [← θ.map_sub, θ.norm_map]
  have hc : ‖θ x - Complex.I • θ y‖ = ‖x + Complex.I • y‖ := by
    rw [← θ.norm_map (x + Complex.I • y), θ.map_add, hi]
    simp [sub_eq_add_neg]
  have hd : ‖θ x + Complex.I • θ y‖ = ‖x - Complex.I • y‖ := by
    rw [← θ.norm_map (x - Complex.I • y), θ.map_sub, hi]
    simp
  rw [inner_eq_sum_norm_sq_div_four, inner_eq_sum_norm_sq_div_four, ha, hb]
  change ((_ : ℂ) - _ + ((‖θ x - Complex.I • θ y‖ : ℂ) ^ 2 -
    (‖θ x + Complex.I • θ y‖ : ℂ) ^ 2) * Complex.I) / 4 = _
  rw [hc, hd]
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  have hr : ∀ r : ℝ, star (r : ℂ) = (r : ℂ) := Complex.conj_ofReal
  simp only [map_div₀, map_add, map_sub, map_mul, map_pow,
    starRingEnd_apply, star_ofNat, hI, hr]
  change ((_ : ℂ) - _ + ((_ : ℂ) - _) * Complex.I) / 4 =
    (((star (‖x + y‖ : ℂ)) ^ 2 - (star (‖x - y‖ : ℂ)) ^ 2 +
      ((star (‖x - Complex.I • y‖ : ℂ)) ^ 2 -
        (star (‖x + Complex.I • y‖ : ℂ)) ^ 2) * star Complex.I) / 4)
  rw [hI, hr, hr, hr, hr]
  change ((‖x + y‖ : ℂ) ^ 2 - (‖x - y‖ : ℂ) ^ 2 +
    ((‖x + Complex.I • y‖ : ℂ) ^ 2 - (‖x - Complex.I • y‖ : ℂ) ^ 2) *
      Complex.I) / 4 =
    ((‖x + y‖ : ℂ) ^ 2 - (‖x - y‖ : ℂ) ^ 2 +
      ((‖x - Complex.I • y‖ : ℂ) ^ 2 - (‖x + Complex.I • y‖ : ℂ) ^ 2) *
        (-Complex.I)) / 4
  ring

theorem solution (θ θ' : AntiUnitary V) (x y : V) :
    inner ℂ (θ' (θ x)) (θ' (θ y)) = inner ℂ x y := by
  rw [anti_inner, anti_inner]
  simp

#print axioms solution
