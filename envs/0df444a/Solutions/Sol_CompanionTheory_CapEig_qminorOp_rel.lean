-- Prove2me | solution 1 for CompanionTheory.CapEig.qminorOp_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:12:03.727193+00:00
-- url     : https://prove2.me/submissions/fd02bdbd-bafd-4421-92d8-c532040f69fb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_Smooth
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_CapelliEigenvalues_Transport
import Theorems.Thm_CompanionTheory_CapEig_foldr_rel

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
variable {n : ℕ} {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
namespace CompanionTheory.CapEig
theorem _root_.solution
    {Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E)}
    {Eop' : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E') → (Matrix (Fin n) (Fin n) ℂ → E')}
    (Rel : (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E') → Prop)
    (hT : ∀ u a b f f', Rel f f' → Rel (Top Eop u a b f) (Top Eop' u a b f'))
    (φ : E →L[ℂ] E') (g : Matrix (Fin n) (Fin n) ℂ) (hg : ∀ f f', Rel f f' → φ (f g) = f' g)
    {f : Matrix (Fin n) (Fin n) ℂ → E} {f' : Matrix (Fin n) (Fin n) ℂ → E'} (h : Rel f f')
    {t : ℕ} (a b : Fin t → Fin n) (u : ℂ) :
    φ (qminorOp Eop a b u f g) = qminorOp Eop' a b u f' g := by
  unfold qminorOp
  simp only [Finset.sum_apply, Pi.smul_apply, map_sum, map_smul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  exact hg _ _ (foldr_rel Rel hT h t (fun k => u - ((k : ℕ) : ℂ)) (fun k => a (σ k)) b)
end CompanionTheory.CapEig
