-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.half_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:16:44.766831+00:00
-- url     : https://prove2.me/submissions/57cd3ef5-94d1-4ffb-8600-05a13045ee0d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_Th0CharMulOpUTh0HalfPeriodEq
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlockFirstBlockEmb
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PStdChar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC
open Formalism.L2.Th1.H
open Formalism.L2.Th1.F (cmTheta thetaZeroCharacter semiChar herm)
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC
theorem _root_.solution (L : PeriodPair) (a b : ℤ) (ha : 2 ∣ a) (hb : 2 ∣ b) :
    ((a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂) / 2 ∈ L.lattice := by
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  have h1 : L.ω₁ ∈ L.lattice := Submodule.subset_span (Set.mem_insert _ _)
  have h2 : L.ω₂ ∈ L.lattice := Submodule.subset_span (Set.mem_insert_of_mem _ rfl)
  have e : (((2 * a' : ℤ) : ℂ) * L.ω₁ + ((2 * b' : ℤ) : ℂ) * L.ω₂) / 2 = a' • L.ω₁ + b' • L.ω₂ := by
    simp only [zsmul_eq_mul]
    push_cast
    ring
  rw [e]
  exact L.lattice.add_mem (L.lattice.smul_mem a' h1) (L.lattice.smul_mem b' h2)
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC
