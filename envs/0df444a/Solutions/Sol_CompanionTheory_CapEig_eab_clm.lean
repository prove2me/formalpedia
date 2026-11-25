-- Prove2me | solution 1 for CompanionTheory.CapEig.eab_clm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:07:24.472943+00:00
-- url     : https://prove2.me/submissions/f5a49e1d-b99d-4c3b-8bb1-ff54327e3d74

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_Smooth
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_CapelliEigenvalues_Transport
import Theorems.Thm_Formalism_REAL_cpartMem
import Theorems.Thm_Formalism_REAL_rdVPair


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open CompanionTheory CompanionTheory.CapEig
variable {n : ℕ} {ε : Fin n → Bool} {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup E'] [NormedSpace ℂ E']
namespace CompanionTheory.CapEig
theorem _root_.solution (φ : E →L[ℂ] E') {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : SmoothOnGV ε f) (a b : Fin n)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) : φ (EabV ε a b f g) = EabV ε a b (fun x => φ (f x)) g := by
  obtain ⟨h1, h2, -, -⟩ := cpartMem n ε (Matrix.single a b 1)
  unfold EabV EcV
  rw [map_add, map_smul, (rdVPair n ε E E' φ f _ g hf h1 hg).2, (rdVPair n ε E E' φ f _ g hf h2 hg).2]
end CompanionTheory.CapEig
