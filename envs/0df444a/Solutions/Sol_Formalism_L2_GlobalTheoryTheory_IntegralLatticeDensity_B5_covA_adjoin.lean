-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.covA_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:40:06.461666+00:00
-- url     : https://prove2.me/submissions/c00a790d-7753-49cd-86dd-1bd533bf1875

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_DedekindFactorK
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_QuadDiscr
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_LatITopBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
open NumberField Polynomial Matrix Classical
open scoped Pointwise
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
theorem _root_.solution (K : Type) [Field K] [NumberField K] (d : ℕ) [Fact d.Prime]
    (x : K) (hx : x ^ 2 = -(d : K)) (hK : Module.finrank ℚ K = 2) :
    IntermediateField.adjoin ℚ {x} = ⊤ := by
  have hint : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  have hnot : x ∉ (algebraMap ℚ K).range := by
    rintro ⟨q, rfl⟩
    have h2 : q ^ 2 = -(d : ℚ) := (algebraMap ℚ K).injective (by simpa using hx)
    have hd : (0 : ℚ) < d := by exact_mod_cast (Fact.out : d.Prime).pos
    nlinarith [sq_nonneg q]
  have hle : (minpoly ℚ x).natDegree ≤ 2 := hK ▸ minpoly.natDegree_le x
  have hne : (minpoly ℚ x).natDegree ≠ 1 := fun h => hnot (minpoly.natDegree_eq_one_iff.mp h)
  have hpos : 0 < (minpoly ℚ x).natDegree := minpoly.natDegree_pos hint
  have hfin : Module.finrank ℚ (IntermediateField.adjoin ℚ {x}) = 2 := by
    rw [IntermediateField.adjoin.finrank hint]
    omega
  exact IntermediateField.eq_of_le_of_finrank_le le_top
    (by rw [IntermediateField.finrank_top', hK, hfin])
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
