-- Prove2me | solution 1 for Formalism.L2.Th1.F.PeriodLatticeBasisLemmas.coords_half
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:24:59.052422+00:00
-- url     : https://prove2.me/submissions/6ff9b369-4794-40d7-9ffa-6bea96a7ac6d

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaQuasi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.L2.Th1.F
namespace PeriodLatticeBasisLemmas
private theorem linearIndependent_real_periods (L : PeriodPair) : LinearIndependent ℝ ![L.ω₁, L.ω₂] := by
  exact L.indep
end PeriodLatticeBasisLemmas
end Formalism.L2.Th1.F
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.PeriodLatticeBasisLemmas
namespace Formalism.L2.Th1.F.PeriodLatticeBasisLemmas
theorem _root_.solution (L : PeriodPair) {a b a' b' : ℤ}
    (h : (a' : ℂ) * L.ω₁ + b' * L.ω₂ = (a * L.ω₁ + b * L.ω₂) / 2) : a = 2 * a' ∧ b = 2 * b' := by
  have h2 : ((2 * a' - a : ℤ) : ℝ) • L.ω₁ + ((2 * b' - b : ℤ) : ℝ) • L.ω₂ = 0 := by
    simp only [Complex.real_smul]
    push_cast
    linear_combination 2 * h
  obtain ⟨h3, h4⟩ := LinearIndependent.pair_iff.mp (linearIndependent_real_periods L) _ _ h2
  have h5 : 2 * a' - a = 0 := by exact_mod_cast h3
  have h6 : 2 * b' - b = 0 := by exact_mod_cast h4
  constructor <;> omega
end Formalism.L2.Th1.F.PeriodLatticeBasisLemmas
