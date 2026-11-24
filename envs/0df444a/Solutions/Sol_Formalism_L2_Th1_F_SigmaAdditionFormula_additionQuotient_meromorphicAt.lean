-- Prove2me | solution 1 for Formalism.L2.Th1.F.SigmaAdditionFormula.additionQuotient_meromorphicAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:24:57.490933+00:00
-- url     : https://prove2.me/submissions/ab9cc932-f518-4c08-9f37-34f0069ba4ed

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Filter Topology
namespace Formalism.L2.Th1.F
namespace SigmaAdditionFormula
variable (L : PeriodPair) (w : ℂ)
private lemma meromorphicAt_weierstrassP (z : ℂ) : MeromorphicAt L.weierstrassP z := by
  classical
  obtain ⟨l, hl⟩ : ∃ l : L.lattice, z ∉ (L.lattice : Set ℂ) \ {(l : ℂ)} := by
    by_cases h : z ∈ L.lattice
    · exact ⟨⟨z, h⟩, fun h' => h'.2 rfl⟩
    · exact ⟨0, fun h' => h h'.1⟩
  have e : L.weierstrassP = fun x => L.weierstrassPExcept l x + (1 / (x - l) ^ 2 - 1 / (l : ℂ) ^ 2) :=
    funext fun x => (L.weierstrassPExcept_add l x).symm
  rw [e]
  exact (L.analyticOnNhd_weierstrassPExcept l z hl).meromorphicAt.add
    ((analyticAt_const.meromorphicAt.div ((analyticAt_id.sub analyticAt_const).pow 2).meromorphicAt).sub
      analyticAt_const.meromorphicAt)
end SigmaAdditionFormula
end Formalism.L2.Th1.F
end
end

set_option autoImplicit false
noncomputable section
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.SigmaAdditionFormula
variable (L : PeriodPair) (w : ℂ)
namespace Formalism.L2.Th1.F.SigmaAdditionFormula
theorem _root_.solution (he : SigmaEntire) (z : ℂ) : MeromorphicAt (additionQuotient L w) z := by
  have hσd : Differentiable ℂ (wSigma L) := he L
  have a1 : AnalyticAt ℂ (fun x => wSigma L (x + w)) z :=
    (hσd.comp (differentiable_id.add_const w)).analyticAt z
  have a2 : AnalyticAt ℂ (fun x => wSigma L (x - w)) z :=
    (hσd.comp (differentiable_id.sub_const w)).analyticAt z
  have a3 : AnalyticAt ℂ (wSigma L) z := hσd.analyticAt z
  exact ((a1.mul a2).meromorphicAt.div (a3.pow 2).meromorphicAt).add
    (analyticAt_const.meromorphicAt.mul (meromorphicAt_weierstrassP L z))
end Formalism.L2.Th1.F.SigmaAdditionFormula
