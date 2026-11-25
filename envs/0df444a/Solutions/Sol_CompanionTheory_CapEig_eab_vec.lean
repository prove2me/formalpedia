-- Prove2me | solution 1 for CompanionTheory.CapEig.eab_vec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:50:37.608815+00:00
-- url     : https://prove2.me/submissions/b22f4fc3-0ae0-44ae-8e1b-37bcb148fb87

import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_CapelliEigenvalues_Transport
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_CapelliEigenvalues_FunAct
import Theorems.Thm_CompanionTheory_CapEig_rd_vec
import Theorems.Thm_Formalism_REAL_cpartMem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants PI.DSInfCharCap
noncomputable section
open CompanionTheory CompanionTheory.CapEig
variable {n : ℕ} {ε : Fin n → Bool} {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
  {σ : Matrix (Fin n) (Fin n) ℂ → (Hs →L[ℂ] Hs)}
namespace CompanionTheory.CapEig
theorem _root_.solution (hm : ∀ a b, inUJ ε a → inUJ ε b → σ (a * b) = (σ a).comp (σ b)) {v : Hs}
    (hv : SmoothOnGV ε fun x => σ x v) (a b : Fin n) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    EabV ε a b (fun x => σ x v) g = σ g (dsigC ε σ (unitM (a, b)) v) := by
  obtain ⟨h1, h2, -, -⟩ := cpartMem n ε (Matrix.single a b 1)
  unfold EabV EcV dsigC
  rw [rd_vec hm hv h1 hg, rd_vec hm hv h2 hg, map_add, map_smul]
  simp only [cpart1, cpart2, thetaJ, unitM, sub_neg_eq_add, ← sub_eq_add_neg]
end CompanionTheory.CapEig
