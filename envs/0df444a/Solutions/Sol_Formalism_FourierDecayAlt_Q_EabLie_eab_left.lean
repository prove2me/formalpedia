-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.EabLie.eab_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:02:48.94826+00:00
-- url     : https://prove2.me/submissions/293f7ab2-f991-493a-800b-3e7414a1340e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DerivativePreservation_HasDerivAtExt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DerivativePreservation_EabPresMain
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabLie_hpart_mem
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabLie_rdV_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.EabLie
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.Q.EabLie
theorem _root_.solution (i : Fin (r + 1)) (z : Fin (2 * r + k + 1) → ℂ) (D : Set (Mx k r))
    (hD : IsOpen D) (p q : Fin (mdim k r i)) (f : Mx k r → E) (hf : SmoothLev k r i D f)
    (hL : LeftEq k r z i D f) :
    LeftEq k r z i D (EH k r (posL k r i p) (posL k r i q) f) := by
  have hX1 := (hpart_mem i p q).1
  have hX2 := (hpart_mem i p q).2
  intro g hg n hn
  simp only [EH, EabH]
  rw [rdV_left i z D hD _ hX1 f hf hL g hg n hn, rdV_left i z D hD _ hX2 f hf hL g hg n hn, smul_add,
    smul_comm Complex.I]
end Formalism.FourierDecayAlt.Q.EabLie
