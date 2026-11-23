-- Prove2me | solution 1 for DiscreteGroups.sglob.LConvKM.convex_capSet
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:48:15.993473+00:00
-- url     : https://prove2.me/submissions/a313a141-fda0-4c5f-ba3f-fdb55c804b76

import Mathlib
import Definitions.Def_Development_DiscreteGroups_GlobalIrreducibility_LConvKMCore
import Theorems.Thm_DiscreteGroups_sglob_LConvKM_comb_apply
import Theorems.Thm_DiscreteGroups_sglob_LConvKM_mkForm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] DiscreteGroups.sglob.LConvKM.mkForm_apply

set_option autoImplicit false
open Set ComplexConjugate
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open DiscreteGroups DiscreteGroups.sglob DiscreteGroups.sglob.LConvKM
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
variable {G : Type*} [Group G] (ρ : Representation ℂ G M) (c : ℕ → ℝ) (xs : ℕ → M)
namespace DiscreteGroups.sglob.LConvKM
theorem _root_.solution : Convex ℝ (capSet ρ c xs) := by
  intro F hF G hG a b ha hb hab
  obtain ⟨⟨⟨⟨⟨⟨⟨f1, f2⟩, f3⟩, f4⟩, fh⟩, fp⟩, fi⟩, fk⟩ := hF
  obtain ⟨⟨⟨⟨⟨⟨⟨g1, g2⟩, g3⟩, g4⟩, gh⟩, gp⟩, gi⟩, gk⟩ := hG
  refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro x y z; simp only [comb_apply, f1 x y z, g1 x y z]; ring
  · intro α x z; simp only [comb_apply, f2 α x z, g2 α x z]; ring
  · intro x y z; simp only [comb_apply, f3 x y z, g3 x y z]; ring
  · intro α x y; simp only [comb_apply, f4 α x y, g4 α x y]; ring
  · intro x y; simp only [comb_apply, map_add, map_mul, Complex.conj_ofReal, fh x y, gh x y]
  · intro x
    simp only [comb_apply, Complex.add_re, Complex.re_ofReal_mul]
    exact add_nonneg (mul_nonneg ha (fp x)) (mul_nonneg hb (gp x))
  · intro g x y; simp only [comb_apply, fi g x y, gi g x y]
  · intro n
    have e : ∑ i ∈ Finset.range n, c i * ((a • F + b • G) (xs i) (xs i)).re
        = a * ∑ i ∈ Finset.range n, c i * (F (xs i) (xs i)).re
          + b * ∑ i ∈ Finset.range n, c i * (G (xs i) (xs i)).re := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [comb_apply, Complex.add_re, Complex.re_ofReal_mul]
      ring
    rw [e]
    linarith [mul_le_mul_of_nonneg_left (fk n) ha, mul_le_mul_of_nonneg_left (gk n) hb]
end DiscreteGroups.sglob.LConvKM
