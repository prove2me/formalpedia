-- Prove2me | solution 1 for Formalism.L2.Th1.F.semi_character_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:14:46.583946+00:00
-- url     : https://prove2.me/submissions/4c82faaf-3ebc-49b8-a0b9-63f8f738089a

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaZeroLogDerivative
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_QuasiPeriodConstUniqueOf
import Theorems.Thm_Formalism_L2_Th1_F_PeriodAreaSignLemmas_sgn_odd
import Theorems.Thm_Formalism_L2_Th1_F_PeriodAreaSignLemmas_altE_coord
import Theorems.Thm_Formalism_L2_Th1_F_PeriodAreaSignLemmas_semiChar_coord
import Theorems.Thm_Formalism_L2_Th1_F_PeriodAreaSignLemmas_exp_pi_int

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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open PeriodAreaSignLemmas
namespace Formalism.L2.Th1.F
theorem _root_.solution : SemiCharMul := by
  intro L x y hx hy
  obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.mp hx
  obtain ⟨m', n', rfl⟩ := PeriodPair.mem_lattice.mp hy
  have hadd : (m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂ + ((m' : ℂ) * L.ω₁ + (n' : ℂ) * L.ω₂)
      = ((m + m' : ℤ) : ℂ) * L.ω₁ + ((n + n' : ℤ) : ℂ) * L.ω₂ := by
    push_cast; ring
  rw [hadd, semiChar_coord, semiChar_coord, semiChar_coord, altE_coord, exp_pi_int]
  have hsg := sgn_odd L
  by_cases h1 : Even m <;> by_cases h2 : Even n <;> by_cases h3 : Even m' <;>
    by_cases h4 : Even n' <;>
    simp [Int.even_add, Int.even_sub, Int.even_mul, h1, h2, h3, h4, hsg]
end Formalism.L2.Th1.F
