-- Prove2me | solution 1 for Formalism.CyclotomicNorms.CentralScalarSequence.contr_agree
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:24.63187+00:00
-- url     : https://prove2.me/submissions/084fce15-05af-415a-8c16-9bd9e5a5b21a

import Definitions.Def_Formalism_CyclotomicNorms_StatementA
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_Central

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.CyclotomicNorms
open Formalism.CyclotomicNorms.CentralScalarSequence
variable {G : Type} [Group G]
namespace Formalism.CyclotomicNorms.CentralScalarSequence
theorem _root_.solution {m : ℕ} (j : Fin (m + 1)) (x : Fin (m + 1) → G) (y : ℕ → G)
    (hx : ∀ k : Fin (m + 1), x k = y k) :
    ∀ k : Fin m, Fin.contractNth j (· * ·) x k = contrN j y k := by
  intro k
  simp only [Fin.contractNth, contrN, hx, Fin.val_castSucc, Fin.val_succ]
end Formalism.CyclotomicNorms.CentralScalarSequence
