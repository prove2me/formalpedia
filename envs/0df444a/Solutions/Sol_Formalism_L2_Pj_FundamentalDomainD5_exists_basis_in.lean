-- Prove2me | solution 1 for Formalism.L2.Pj.FundamentalDomainD5.exists_basis_in
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:15:24.660284+00:00
-- url     : https://prove2.me/submissions/7efc1c86-fe51-4bf3-ab8b-a1575eae6e84

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_ExistsBasisIn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.FundamentalDomainD5
namespace Formalism.L2.Pj.FundamentalDomainD5
theorem _root_.solution {K : Type} [Field K] {r : ℕ} (S : Set (Fin r → K))
    (hS : Submodule.span K S = ⊤) :
    ∃ v : Fin r → Fin r → K, (∀ j, v j ∈ S) ∧ LinearIndependent K v := by
  obtain ⟨b, hbS, hspan, hli⟩ := exists_linearIndependent K S
  have htop : ⊤ ≤ Submodule.span K (Set.range ((↑) : b → Fin r → K)) := by
    rw [Subtype.range_coe, hspan, hS]
  let B := Module.Basis.mk hli htop
  let e := B.indexEquiv (Pi.basisFun K (Fin r))
  refine ⟨fun j => (e.symm j : Fin r → K), fun j => hbS (e.symm j).2, ?_⟩
  exact hli.comp e.symm e.symm.injective
end Formalism.L2.Pj.FundamentalDomainD5
