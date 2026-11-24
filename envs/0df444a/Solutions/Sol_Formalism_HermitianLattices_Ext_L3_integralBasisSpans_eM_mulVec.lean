-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.integralBasisSpans.eM_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:16.448415+00:00
-- url     : https://prove2.me/submissions/876cee85-6fb6-477a-b6e5-521d59ce0058

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardQuotExtPPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.integralBasisSpans
open LocalSpans idealPowerSpanBounds localizedQuotients
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
variable [Fact (IsFixF K F)]
namespace Formalism.HermitianLattices.Ext.L3.integralBasisSpans
theorem _root_.solution (b : Basis κ K V) (J : Ideal (𝓞 K))
    (X : Module.End (𝓞 K) (spanO b ⧸ (J • ⊤ : Submodule (𝓞 K) (spanO b)))) (q) :
    eM b J X *ᵥ qE b J q = qE b J (X q) := by
  have : eM b J X = LinearMap.toMatrix' (LinearMap.extendScalarsOfSurjectiveEquiv (R := 𝓞 K)
      (S := 𝓞 K ⧸ J) Ideal.Quotient.mk_surjective ((qE b J).conj X)) := rfl
  rw [this, LinearMap.toMatrix'_mulVec]
  show (qE b J).conj X (qE b J q) = _
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
end Formalism.HermitianLattices.Ext.L3.integralBasisSpans
