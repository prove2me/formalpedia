-- Prove2me | solution 1 for Formalism.L2.Th1.F.S2IsogenyPsi.isPreconnected_dom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:36:43.793545+00:00
-- url     : https://prove2.me/submissions/8a49c2fc-9543-48ba-994b-982717053abb

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_QuasiPeriodConstIsogeny

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
open Formalism.L2.Th1.F.S2IsogenyPsi
namespace Formalism.L2.Th1.F.S2IsogenyPsi
theorem _root_.solution (L : PeriodPair) (α : ℂ) (hα : α ≠ 0) : IsPreconnected (dom L α) := by
  have hc : (L.lattice : Set ℂ).Countable := by
    have hsub : (L.lattice : Set ℂ) ⊆
        Set.range (fun p : ℤ × ℤ => (p.1 : ℂ) * L.ω₁ + (p.2 : ℂ) * L.ω₂) := by
      intro x hx
      obtain ⟨m, n, h⟩ := PeriodPair.mem_lattice.mp hx
      exact ⟨(m, n), h⟩
    exact (Set.countable_range _).mono hsub
  have hc' : ((fun z => α * z) ⁻¹' (L.lattice : Set ℂ)).Countable :=
    hc.preimage (mul_right_injective₀ hα)
  have hrank : 1 < Module.rank ℝ ℂ := by
    first
      | (rw [Complex.rank_real_complex]; exact one_lt_two)
      | (rw [Complex.rank_real_complex]; norm_num)
      | simp [Complex.rank_real_complex]
  have hconn : IsConnected ((fun z => α * z) ⁻¹' (L.lattice : Set ℂ))ᶜ := by
    first
      | exact Set.Countable.isConnected_compl_of_one_lt_rank hrank hc'
      | exact (Set.Countable.isPathConnected_compl_of_one_lt_rank hrank hc').isConnected
  exact hconn.isPreconnected
end Formalism.L2.Th1.F.S2IsogenyPsi
