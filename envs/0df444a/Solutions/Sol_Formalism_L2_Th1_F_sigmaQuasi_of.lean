-- Prove2me | solution 1 for Formalism.L2.Th1.F.sigmaQuasi_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:09:44.571227+00:00
-- url     : https://prove2.me/submissions/645ffd6a-3c8e-4065-837e-791992005f60

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaQuasi
import Theorems.Thm_Formalism_L2_Th1_F_PeriodLatticeBasisLemmas_qp_coords
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
open PeriodLatticeBasisLemmas
namespace Formalism.L2.Th1.F
theorem _root_.solution (hq : ZetaQuasi) (hl : SigmaLogDeriv) (_he : SigmaEntire) (ho : SigmaOdd)
    (hz : SigmaZero) : SigmaQuasi := by
  intro L ω z hω
  obtain ⟨a, b, rfl⟩ := (_root_.Formalism.L2.Th1.F.PeriodLatticeBasisLemmas.mem_lattice_iff_exists_int_comb' L).mp hω
  exact Formalism.L2.Th1.F.PeriodLatticeBasisLemmas.qp_coords hq hl ho hz L _ a b le_rfl z
end Formalism.L2.Th1.F
