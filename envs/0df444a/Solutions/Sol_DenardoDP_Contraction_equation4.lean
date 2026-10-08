-- Prove2me | solution 1 for DenardoDP.Contraction.equation4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T14:55:58.830896+00:00
-- url     : https://prove2.me/submissions/f8b9462a-4e92-449b-86cb-f95279455163

import Mathlib
import Definitions.Def_DenardoDP_Contraction_Model

open DenardoDP.Contraction in
theorem cc4b119f_modulus {Ω : Type*} {D : Ω → Type*}
    (h : (x : Ω) → D x → BFun Ω → ℝ) (A : BFun Ω → BFun Ω)
    (c : ℝ) (hA : IsMaxOperator h A) (hc : ContractionAssumption h c) :
    ModulusLE A c := by
  obtain ⟨hc0, -, hh⟩ := hc
  intro u v
  have key : ∀ (a b : BFun Ω) (x : Ω), A a x ≤ A b x + c * dist a b := by
    intro a b x
    apply (hA a x).2
    rintro _ ⟨d, rfl⟩
    have h1 := (abs_le.mp (hh a b x d)).2
    have h2 : h x d b ≤ A b x := (hA b x).1 ⟨d, rfl⟩
    linarith
  rw [dist_eq_norm]
  apply lp.norm_le_of_forall_le (mul_nonneg hc0 dist_nonneg)
  intro x
  rw [lp.coeFn_sub, Pi.sub_apply, Real.norm_eq_abs, abs_le]
  have k1 := key u v x
  have k2 := key v u x
  rw [dist_comm] at k2
  constructor <;> linarith

open DenardoDP.Contraction in
theorem solution {Ω : Type*} {D : Ω → Type*}
    (h : (x : Ω) → D x → BFun Ω → ℝ) (A : BFun Ω → BFun Ω)
    (c : ℝ) (hA : IsMaxOperator h A) (hc : ContractionAssumption h c) :
    ∃! w : BFun Ω, A w = w := by
  have hmod := cc4b119f_modulus h A c hA hc
  obtain ⟨hc0, hc1, -⟩ := hc
  have hK : ContractingWith ⟨c, hc0⟩ A := by
    refine ⟨?_, ?_⟩
    · show c < 1
      exact hc1
    · exact LipschitzWith.of_dist_le_mul (fun u v => hmod u v)
  refine ⟨ContractingWith.fixedPoint A hK, ContractingWith.fixedPoint_isFixedPt hK, ?_⟩
  intro y hy
  exact ContractingWith.fixedPoint_unique hK hy
