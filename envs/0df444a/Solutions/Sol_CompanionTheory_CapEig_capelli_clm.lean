-- Prove2me | solution 1 for CompanionTheory.CapEig.capelli_clm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:46:42.805443+00:00
-- url     : https://prove2.me/submissions/88edc49a-707a-4556-b770-97c7c2918e3a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_Smooth
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_CapelliEigenvalues_Transport
import Theorems.Thm_CompanionTheory_CapEig_qminorOp_rel
import Theorems.Thm_CompanionTheory_CapEig_top_smooth
import Theorems.Thm_CompanionTheory_CapEig_eab_clm

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
theorem _root_.solution (φ : E →L[ℂ] E') {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : SmoothOnGV ε f) (u : ℂ)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) : φ (capelli ε u f g) = capelli ε u (fun x => φ (f x)) g := by
  unfold capelli qdetOp
  refine qminorOp_rel (fun f f' => SmoothOnGV ε f ∧ ∀ x, inUJ ε x → φ (f x) = f' x) ?_ φ g
    (fun _ _ h => h.2 g hg) ⟨hf, fun _ _ => rfl⟩ id id u
  rintro u a b f f' ⟨hs, he⟩
  refine ⟨top_smooth hs u a b, fun x hx => ?_⟩
  unfold Formalism.QuantumDeterminants.Top
  rw [map_add, eab_clm φ hs a b hx, io_eab_congr he a b hx]
  congr 1
  split_ifs
  · rw [map_smul, he x hx]
  · exact map_zero φ
end CompanionTheory.CapEig
