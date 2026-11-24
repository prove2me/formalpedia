-- Prove2me | solution 1 for Formalism.L2.Th1.F.PeriodAreaSignLemmas.semiChar_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:24:54.374811+00:00
-- url     : https://prove2.me/submissions/d6c7fb65-00b9-476f-948d-3738d2416ce6

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaZeroLogDerivative
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_QuasiPeriodConstUniqueOf

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
open Formalism.L2.Th1.F.PeriodAreaSignLemmas
namespace Formalism.L2.Th1.F.PeriodAreaSignLemmas
theorem _root_.solution (L : PeriodPair) (m n : ℤ) :
    semiChar L ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) = if Even m ∧ Even n then 1 else -1 := by
  have key : ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) / 2 ∈ L.lattice ↔ Even m ∧ Even n := by
    constructor
    · intro hx
      obtain ⟨a, b, e⟩ := PeriodPair.mem_lattice.mp hx
      have := LinearIndependent.pair_iff.mp L.indep ((m : ℝ) - 2 * a) ((n : ℝ) - 2 * b) (by
        simp only [Complex.real_smul]
        push_cast
        linear_combination (-2 : ℂ) * e)
      refine ⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩
      · have h1 : (m : ℝ) = 2 * a := by linarith [this.1]
        have : m = 2 * a := by exact_mod_cast h1
        omega
      · have h1 : (n : ℝ) = 2 * b := by linarith [this.2]
        have : n = 2 * b := by exact_mod_cast h1
        omega
    · rintro ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
      refine PeriodPair.mem_lattice.mpr ⟨a, b, ?_⟩
      push_cast
      ring
  rw [semiChar]
  simp only [key]
end Formalism.L2.Th1.F.PeriodAreaSignLemmas
