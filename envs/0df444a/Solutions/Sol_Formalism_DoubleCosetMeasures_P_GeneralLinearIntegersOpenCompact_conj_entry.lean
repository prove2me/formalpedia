-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact.conj_entry
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:19.501554+00:00
-- url     : https://prove2.me/submissions/5cc75704-f39c-4705-8af3-914222cc637b

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_GLRealOpen
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_GlR
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsClosedLowUni

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Measure Topology Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact
variable {K : Type} [CommRing K]
namespace Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact
theorem _root_.solution {n : ℕ} (δ : Fin n → Kˣ) (g : GL (Fin n) K) (a b : Fin n) :
    (((Dg δ)⁻¹ * g * Dg δ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b =
      (((δ a)⁻¹ : Kˣ) : K) * (g : Matrix (Fin n) (Fin n) K) a b * (δ b : K) := by
  simp only [Units.val_mul]
  show (diagonal (fun a => (((δ a)⁻¹ : Kˣ) : K)) * (g : Matrix (Fin n) (Fin n) K) *
    diagonal (fun a => (δ a : K))) a b = _
  rw [mul_diagonal, diagonal_mul]
end Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact
