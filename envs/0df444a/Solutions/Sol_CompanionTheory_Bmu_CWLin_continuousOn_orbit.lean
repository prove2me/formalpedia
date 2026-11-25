-- Prove2me | solution 1 for CompanionTheory.Bmu.CWLin.continuousOn_orbit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:31:41.183214+00:00
-- url     : https://prove2.me/submissions/6bb0a3cd-d5c7-460b-8ce9-f014a2621dbe

import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_ContinuousOnOrbit
import Theorems.Thm_CompanionTheory_Bmu_LieWd_lieW
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_apply
import Theorems.Thm_CompanionTheory_D_Upq_Sm_continuousOn_dsW_orbit


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
theorem _root_.solution [FiniteDimensional ℂ V] (hF : Factor) (hU : URep Hm σ) {B : H → V}
    (hB : CWLin Hm σ B) {w : H} (hw : IsSm (UH Hm) σ w) : ContinuousOn (fun g => B (σ g w)) (UH Hm) := by
  obtain ⟨N, W, β, hW, hβ⟩ := hF n Hm H σ hU V B hB
  refine (continuousOn_finset_sum Finset.univ fun i _ =>
    (β i).continuous.comp_continuousOn (continuousOn_dsW_orbit hU.rep hw (hW i).lieW)).congr fun g hg => ?_
  exact hβ _ (hw.apply hU.rep hg)
end CWLin
end CompanionTheory.Bmu
