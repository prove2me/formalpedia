-- Prove2me | solution 1 for BraidsLinksMCG.complex_exp_winding_one_deck_translation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T15:09:27.422379+00:00
-- url     : https://prove2.me/submissions/90b2abec-8113-4591-9e90-cd7bd34806a6

import Mathlib
import Definitions.Def_exp_covering_helpers

set_option autoImplicit false

open scoped Topology

open BraidsLinksMCG in
/-- The straight segment from `0` to `2πi`. -/
noncomputable def d59_seg : Path (0 : ℂ) (2 * Real.pi * Complex.I) where
  toFun t := 2 * Real.pi * (t : ℝ) * Complex.I
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

open BraidsLinksMCG in
/-- The fibre point `2πi` over `expBase`. -/
noncomputable def d59_top :
    (fun z : ℂ ↦ (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {z : ℂ // z ≠ 0})) ⁻¹'
      {expBase} :=
  ⟨2 * Real.pi * Complex.I, by
    simp only [Set.mem_preimage, Set.mem_singleton_iff, expBase]
    exact Subtype.ext (by simp [Complex.exp_two_pi_mul_I])⟩

open BraidsLinksMCG in
theorem d59_monodromy :
    Complex.isCoveringMap_exp.monodromy
      (Path.Homotopic.Quotient.mk expWindingLoop) expFibreBase = d59_top := by
  apply Complex.isCoveringMap_exp.monodromy_eq_of_map_eq
    (Path.Homotopic.Quotient.mk d59_seg)
  have h : d59_seg.map Complex.isCoveringMap_exp.continuous =
      expWindingLoop.cast (by simp [expBase]) (by
        apply Subtype.ext; simp [expBase, Complex.exp_two_pi_mul_I]) := by
    ext t
    simp [d59_seg, expWindingLoop]
    rfl
  exact congrArg Path.Homotopic.Quotient.mk h

open BraidsLinksMCG in
theorem solution :
    Complex.isAddQuotientCoveringMap_exp.fundamentalGroupToMulOpposite expFibreBase
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk expWindingLoop)) =
      MulOpposite.op ((1 : ℤ) • (⟨2 * Real.pi * Complex.I, AddSubgroup.mem_zmultiples (2 * Real.pi * Complex.I)⟩ : AddSubgroup.zmultiples (2 * Real.pi * Complex.I))) := by
  refine (Complex.isAddQuotientCoveringMap_exp.fundamentalGroupToMulOpposite_apply_eq_Iff
    (e := expFibreBase)).mpr ?_
  have h := congrArg Subtype.val d59_monodromy
  refine Eq.trans ?_ h.symm
  simp [d59_top, expFibreBase]
  exact add_zero _
