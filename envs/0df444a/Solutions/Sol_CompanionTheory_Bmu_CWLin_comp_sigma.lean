-- Prove2me | solution 1 for CompanionTheory.Bmu.CWLin.comp_sigma
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:32:24.888885+00:00
-- url     : https://prove2.me/submissions/657fcb2f-e146-4128-b970-bf91376c09da

import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_ContinuousOnOrbit
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_add
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_apply
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_smul
import Theorems.Thm_CompanionTheory_D_Upq_Sm_SmOn_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm
open scoped ContDiff InnerProductSpace ComplexConjugate
noncomputable section
open CompanionTheory CompanionTheory.Bmu
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {Hm : Mat n} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Mat n → (H →L[ℂ] H)} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
namespace CompanionTheory.Bmu
namespace CWLin
theorem _root_.solution (hAd : DsAd) (hU : URep Hm σ) {B : H → V} (hB : CWLin Hm σ B) {y : Mat n}
    (hy : y ∈ UH Hm) : CWLin Hm σ (fun v => B (σ y v)) := by
  refine ⟨fun x hx x' hx' => ?_, fun a x hx => ?_, ?_⟩
  · rw [map_add, hB.add _ (hx.apply hU.rep hy) _ (hx'.apply hU.rep hy)]
  · rw [map_smul, hB.smul _ _ (hx.apply hU.rep hy)]
  · obtain ⟨C, Ws, hWs, hb⟩ := hB.bd
    refine ⟨C, Ws.map fun W => W.map fun X => y⁻¹ * X * y, fun W hW => ?_, fun v hv => ?_⟩
    · obtain ⟨W', hW', rfl⟩ := List.mem_map.1 hW
      exact (hAd n Hm H σ hU y hy W' (hWs W' hW')).1
    · refine (hb _ (hv.apply hU.rep hy)).trans_eq ?_
      rw [List.map_map]
      congr 2
      refine List.map_congr_left fun W hW => ?_
      rw [(hAd n Hm H σ hU y hy W (hWs W hW)).2 v hv, hU.iso y hy]
      rfl
end CWLin
end CompanionTheory.Bmu
