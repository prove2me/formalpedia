-- Prove2me | solution 1 for CompanionTheory.CapEig.foldr_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:54:12.311389+00:00
-- url     : https://prove2.me/submissions/5ceda39e-5daf-48bd-a925-b388827765fd

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_Smooth
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_CapelliEigenvalues_Transport

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
    {f : Matrix (Fin n) (Fin n) ℂ → E} {f' : Matrix (Fin n) (Fin n) ℂ → E'} (h : Rel f f') :
    ∀ (t : ℕ) (u : Fin t → ℂ) (a b : Fin t → Fin n),
      Rel ((List.ofFn fun k => Top Eop (u k) (a k) (b k)).foldr (fun T h => T h) f)
        ((List.ofFn fun k => Top Eop' (u k) (a k) (b k)).foldr (fun T h => T h) f')
  | 0, _, _, _ => by simpa using h
  | t + 1, u, a, b => by
    rw [List.ofFn_succ, List.ofFn_succ, List.foldr_cons, List.foldr_cons]
    exact hT _ _ _ _ _ (solution Rel hT h t (fun k => u k.succ) (fun k => a k.succ) (fun k => b k.succ))
end CompanionTheory.CapEig
