-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.stdChar_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:16:02.676352+00:00
-- url     : https://prove2.me/submissions/6c97c19b-2cc3-47bd-857c-d723a3ccd962

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_Th0CharMulOpUTh0HalfPeriodEq
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlockFirstBlockEmb
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PStdChar
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_SC_char_eq
import Theorems.Thm_Formalism_L2_Th1_H_mem_stdLat
import Theorems.Thm_Formalism_L2_Th1_H_stdH_apply


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
variable (L : PeriodPair) (d : ℕ)
local notation "EE" => Formalism.L2.Th1.F.altE L
variable {L d}
variable (hst : ∀ x ∈ L.lattice, cmTheta 1 d * x ∈ L.lattice)
include hst
variable {ω₀ : ℂ} (h0 : ω₀ ∈ L.lattice) (hθ : cmTheta 1 d * (ω₀ / 2) ∉ L.lattice)
  (hθ' : (1 - cmTheta 1 d) * (ω₀ / 2) ∉ L.lattice)
include h0 hθ hθ'
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC
theorem _root_.solution (hd : d % 8 = 7) (n : Type) [Fintype n] [DecidableEq n] (x : n → ℂ) (hx : x ∈ stdLat L n) :
    alphaQ (Real.sqrt d / 2) (stdH L n) x = stdChar L ω₀ x := by
  rw [mem_stdLat] at hx
  rw [alphaQ, qOf, stdH_apply, Complex.re_sum, Finset.mul_sum, Complex.ofReal_sum, Finset.mul_sum,
    Complex.exp_sum, stdChar]
  exact Finset.prod_congr rfl fun i _ => char_eq hst h0 hθ hθ' hd (x i) (hx i)
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC
