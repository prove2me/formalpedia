-- Prove2me | solution 1 for CompanionTheory.CapEig.rd_vec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:46:44.803292+00:00
-- url     : https://prove2.me/submissions/28ba5c67-bfcb-49a9-9e45-9aa8f79b8639

import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_CapelliEigenvalues_Transport
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_CapelliEigenvalues_FunAct
import Theorems.Thm_CompanionTheory_CapEig_inUJ_one
import Theorems.Thm_Formalism_REAL_rdLeftV
import Theorems.Thm_Formalism_REAL_rdVPair


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
    (hv : SmoothOnGV ε fun x => σ x v) {X g : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (hg : inUJ ε g) :
    RdV X (fun x => σ x v) g = σ g (PI.PhMeasCore.dsig σ X v) := by
  have e0 : PI.PhMeasCore.dsig σ X v = RdV X (fun x => σ x v) 1 := by
    unfold PI.PhMeasCore.dsig RdV
    simp only [Matrix.one_mul]
  rw [e0, (rdVPair n ε Hs Hs (σ g) _ X 1 hv hX inUJ_one).2,
    io_rd_congr (f' := fun x => σ (g * x) v) (fun x hx => by rw [hm g x hg hx]; rfl) hX inUJ_one,
    rdLeftV n Hs (fun x => σ x v) X g 1, Matrix.mul_one]
end CompanionTheory.CapEig
