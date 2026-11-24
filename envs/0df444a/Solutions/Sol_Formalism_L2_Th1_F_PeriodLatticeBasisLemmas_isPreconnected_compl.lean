-- Prove2me | solution 1 for Formalism.L2.Th1.F.PeriodLatticeBasisLemmas.isPreconnected_compl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:24:59.740877+00:00
-- url     : https://prove2.me/submissions/0fd6dfa5-ce91-4f79-b29b-776ce61d6f99

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
private theorem mem_lattice_iff_exists_int_comb' (L : PeriodPair) {x : ℂ} :
    x ∈ L.lattice ↔ ∃ m n : ℤ, (m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂ = x := by
  exact L.mem_lattice
end PeriodLatticeBasisLemmas
end Formalism.L2.Th1.F
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.PeriodLatticeBasisLemmas
namespace Formalism.L2.Th1.F.PeriodLatticeBasisLemmas
theorem _root_.solution (L : PeriodPair) : IsPreconnected ((L.lattice : Set ℂ)ᶜ) := by
  have hc : (L.lattice : Set ℂ).Countable := by
    refine (Set.countable_range (fun p : ℤ × ℤ => (p.1 : ℂ) * L.ω₁ + (p.2 : ℂ) * L.ω₂)).mono ?_
    intro x hx
    obtain ⟨m, n, rfl⟩ := (mem_lattice_iff_exists_int_comb' L).mp hx
    exact ⟨(m, n), rfl⟩
  have hr : 1 < Module.rank ℝ ℂ := by
    rw [← Module.finrank_eq_rank, Complex.finrank_real_complex]
    norm_num
  exact (hc.isPathConnected_compl_of_one_lt_rank hr).isConnected.isPreconnected
end Formalism.L2.Th1.F.PeriodLatticeBasisLemmas
