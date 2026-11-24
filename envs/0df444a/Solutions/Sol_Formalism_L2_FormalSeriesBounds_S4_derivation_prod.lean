-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.S4.derivation_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:56:53.786309+00:00
-- url     : https://prove2.me/submissions/f1e782f7-5733-487c-bbb3-bfad47d4c13e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ExistsStrictMonoMinor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.S4
variable {R : Type*} [CommRing R]
namespace Formalism.L2.FormalSeriesBounds.S4
theorem _root_.solution {F : Type*} [CommRing F] [Algebra R F] {n : ℕ} (D : Derivation R F F)
    (χ : Fin n → F) (b : Fin n → R) (hD : ∀ σ, D (χ σ) = b σ • χ σ) (s : Finset (Fin n)) :
    D (∏ σ ∈ s, χ σ) = (∑ σ ∈ s, b σ) • ∏ σ ∈ s, χ σ := by
  refine Finset.induction_on s (by simp) ?_
  intro i s hi ih
  rw [Finset.prod_insert hi, Finset.sum_insert hi, Derivation.leibniz, ih, hD]
  simp only [Algebra.smul_def, smul_eq_mul, map_add, Algebra.algebraMap_self, RingHom.id_apply]
  ring
end Formalism.L2.FormalSeriesBounds.S4
