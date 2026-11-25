-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.rtj_supp_of_supported
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:27:26.1403+00:00
-- url     : https://prove2.me/submissions/ed44edca-495e-4bbe-b626-2f2e04d42259

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MemVarsProdAll
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieJet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
variable {K : Type} [Field K] {σ : Type}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution {A : Set σ} {P : MvPolynomial σ K} (hP : P ∈ MvPolynomial.supported K A)
    (m : σ →₀ ℕ) (hm : MvPolynomial.coeff m P ≠ 0) : (↑m.support : Set σ) ⊆ A := by
  intro i hi
  rw [MvPolynomial.mem_supported] at hP
  exact hP ((MvPolynomial.mem_vars i).mpr ⟨m, MvPolynomial.mem_support_iff.mpr hm, hi⟩)
end Formalism.L2.FormalSeriesBounds
