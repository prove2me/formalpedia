-- Prove2me | solution 1 for CompanionTheory.Bmu.CWLin.sum_orbit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:44:27.1988+00:00
-- url     : https://prove2.me/submissions/9c7ca432-f9c3-4a20-9e70-a5d35b51cdfd

import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_ContinuousOnOrbit
import Theorems.Thm_CompanionTheory_Bmu_CWLin_zero
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_add
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_apply
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_smul
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_zero
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
omit [CompleteSpace H]
namespace CompanionTheory.Bmu
namespace CWLin
theorem _root_.solution (hU : URep Hm σ) {B : H → V} (hB : CWLin Hm σ B) {w : H} (hw : IsSm (UH Hm) σ w)
    (h0 : ∀ g ∈ UH Hm, B (σ g w) = 0) {ι : Type} (s : Finset ι) (c : ι → ℂ) (g : ι → Mat n)
    (hg : ∀ i, g i ∈ UH Hm) : IsSm (UH Hm) σ (∑ i ∈ s, c i • σ (g i) w) ∧ B (∑ i ∈ s, c i • σ (g i) w) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ⟨IsSm.zero, hB.zero⟩
  | insert a s ha ih =>
    have h1 := hw.apply hU.rep (hg a)
    rw [Finset.sum_insert ha]
    exact ⟨(h1.smul _).add ih.1, by rw [hB.add _ (h1.smul _) _ ih.1, hB.smul _ _ h1, h0 _ (hg a), ih.2]; simp⟩
end CWLin
end CompanionTheory.Bmu
