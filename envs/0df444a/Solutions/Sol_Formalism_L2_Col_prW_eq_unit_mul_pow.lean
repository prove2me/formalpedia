-- Prove2me | solution 1 for Formalism.L2.Col.prW_eq_unit_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:10:29.70764+00:00
-- url     : https://prove2.me/submissions/67dcc76b-19aa-4323-8462-30f2febfe1c8

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_LocalToGlobal_Columns_AlgebraMapMemMaximalIdealPowIff
import Theorems.Thm_Formalism_L2_Col_prW_prime
import Theorems.Thm_Formalism_L2_Col_natCast_ow_ne_zero

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
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) {ϖ : Ow w} (hϖ : Irreducible ϖ) :
    ∃ u : (Ow w)ˣ, ((prW w : ℕ) : Ow w) = u * ϖ ^ eW w := by
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (natCast_ow_ne_zero w (prW_prime w).ne_zero) hϖ
  have hspan : (w.asIdeal.under ℤ).map (algebraMap ℤ (Ow w)) = IsLocalRing.maximalIdeal (Ow w) ^ n := by
    rw [← Int.ideal_span_absNorm_eq_self (w.asIdeal.under ℤ), Ideal.map_span, Set.image_singleton,
      hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
    have : algebraMap ℤ (Ow w) ((Ideal.absNorm (w.asIdeal.under ℤ) : ℕ) : ℤ) = ((prW w : ℕ) : Ow w) := by
      simp [prW]
    rw [this, hu]
    exact Ideal.span_singleton_eq_span_singleton.2 ⟨u⁻¹, by
      rw [mul_comm (u : Ow w), mul_assoc, Units.mul_inv, mul_one]⟩
  have he : eW w = n := by
    unfold eW
    rw [Ideal.ramificationIdx_def, hspan, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal,
      ENat.toNat_natCast]
  exact ⟨u, by rw [he, hu]⟩
end Formalism.L2.Col
