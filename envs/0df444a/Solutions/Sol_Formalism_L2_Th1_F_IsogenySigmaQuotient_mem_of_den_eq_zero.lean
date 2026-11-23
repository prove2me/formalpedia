-- Prove2me | solution 1 for Formalism.L2.Th1.F.IsogenySigmaQuotient.mem_of_den_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:27:57.503215+00:00
-- url     : https://prove2.me/submissions/6ed728e5-cba4-4d7e-8b27-1dd6f1ff81c7

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IsogenySigma

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.IsogenySigmaQuotient
variable (L : PeriodPair)
variable (α : ℂ) (S : Finset ℂ)
namespace Formalism.L2.Th1.F.IsogenySigmaQuotient
theorem _root_.solution (hb : SgStarBasic) (hα : α ≠ 0) (hst : MulStable L α)
    (hS : IsKerReps L α S) (z : ℂ) (h : den L α S z = 0) : α * z ∈ L.lattice := by
  have hz := (hb L).2.2.1
  unfold den at h
  rcases mul_eq_zero.1 h with h | h
  · rcases mul_eq_zero.1 h with h | h
    · exact absurd ((pow_eq_zero_iff two_ne_zero).1 h) hα
    · exact hst z ((hz z).1 ((pow_eq_zero_iff two_ne_zero).1 h))
  · obtain ⟨P, hP, h⟩ := Finset.prod_eq_zero_iff.1 h
    have hPL := hS.1 P hP
    have hs : sgStar L P ≠ 0 := fun h0 => hPL.2 ((hz P).1 h0)
    unfold fac at h
    rcases mul_eq_zero.1 h with h | h
    · exfalso; simp [hs] at h
    · rcases mul_eq_zero.1 h with h | h
      · have h3 := hst _ ((hz _).1 h)
        have e : α * z = α * (z + P) - α * P := by ring
        rw [e]; exact L.lattice.sub_mem h3 hPL.1
      · have h3 := hst _ ((hz _).1 h)
        have e : α * z = α * (z - P) + α * P := by ring
        rw [e]; exact L.lattice.add_mem h3 hPL.1
end Formalism.L2.Th1.F.IsogenySigmaQuotient
