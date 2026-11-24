-- Prove2me | solution 1 for Formalism.L2.Col.span_prW_ow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:13:32.63539+00:00
-- url     : https://prove2.me/submissions/609b96f9-2726-45b5-a75c-b7fb14439423

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_LocalToGlobal_Columns_AlgebraMapMemMaximalIdealPowIff
import Theorems.Thm_Formalism_L2_Col_prW_eq_unit_mul_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Col
variable {K : Type} [Field K] [NumberField K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.L2.Col
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) :
    Ideal.span {((prW w : ℕ) : Ow w)} = IsLocalRing.maximalIdeal (Ow w) ^ eW w := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (Ow w)
  obtain ⟨u, hu⟩ := prW_eq_unit_mul_pow w hπ
  rw [hu, hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
  exact Ideal.span_singleton_eq_span_singleton.2 ⟨u⁻¹, by
    rw [mul_comm (u : Ow w), mul_assoc, Units.mul_inv, mul_one]⟩
end Formalism.L2.Col
