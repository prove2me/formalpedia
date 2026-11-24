-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:27:31.86166+00:00
-- url     : https://prove2.me/submissions/91146b4f-093f-492c-a6bd-799611772af0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_Th0CharMulOpUTh0HalfPeriodEq
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlockFirstBlockEmb
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PStdChar
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_SC_gen_mod_two
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_SC_half_notMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators ComplexConjugate
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC
open Formalism.L2.Th1.H
open Formalism.L2.Th1.F (cmTheta thetaZeroCharacter semiChar herm)
section Main
variable (L : PeriodPair) (d : ℕ)
local notation "EE" => Formalism.L2.Th1.F.altE L
variable {L d}
variable (hst : ∀ x ∈ L.lattice, cmTheta 1 d * x ∈ L.lattice)
include hst
variable {ω₀ : ℂ} (h0 : ω₀ ∈ L.lattice) (hθ : cmTheta 1 d * (ω₀ / 2) ∉ L.lattice)
  (hθ' : (1 - cmTheta 1 d) * (ω₀ / 2) ∉ L.lattice)
include h0 hθ hθ'
private theorem half_periods_not_mem_cm_lattice : ω₀ / 2 ∉ L.lattice ∧ cmTheta 1 d * ω₀ / 2 ∉ L.lattice ∧
    (ω₀ + cmTheta 1 d * ω₀) / 2 ∉ L.lattice := by
  refine ⟨half_notMem hst h0 hθ hθ', ?_, ?_⟩
  · rw [mul_div_assoc]
    exact hθ
  · intro h
    apply hθ'
    have e : (1 - cmTheta 1 d) * (ω₀ / 2) = ω₀ - (ω₀ + cmTheta 1 d * ω₀) / 2 := by ring
    rw [e]
    exact L.lattice.sub_mem h0 h
end Main
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC
open Formalism.L2.Th1.H
open Formalism.L2.Th1.F (cmTheta thetaZeroCharacter semiChar herm)
variable (L : PeriodPair) (d : ℕ)
local notation "EE" => Formalism.L2.Th1.F.altE L
variable {L d}
variable (hst : ∀ x ∈ L.lattice, cmTheta 1 d * x ∈ L.lattice)
include hst
variable {ω₀ : ℂ} (h0 : ω₀ ∈ L.lattice) (hθ : cmTheta 1 d * (ω₀ / 2) ∉ L.lattice)
  (hθ' : (1 - cmTheta 1 d) * (ω₀ / 2) ∉ L.lattice)
include h0 hθ hθ'
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC
theorem _root_.solution (w : ℂ) (hw : w ∈ L.lattice) :
    ∃ v ∈ L.lattice, w = 2 * v ∨ w = ω₀ + 2 * v ∨ w = cmTheta 1 d * ω₀ + 2 * v ∨
      w = ω₀ + cmTheta 1 d * ω₀ + 2 * v := by
  obtain ⟨n1, n2, n3⟩ := half_periods_not_mem_cm_lattice hst h0 hθ hθ'
  exact gen_mod_two L ω₀ (cmTheta 1 d * ω₀) w h0 (hst _ h0) hw n1 n2 n3
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC
