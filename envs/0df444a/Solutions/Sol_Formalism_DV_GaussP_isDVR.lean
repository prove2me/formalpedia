-- Prove2me | solution 1 for Formalism.DV.GaussP.isDVR
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:54:21.723799+00:00
-- url     : https://prove2.me/submissions/e06c985a-4085-4445-9da3-55a17af59338

import Definitions.Def_Formalism_GaussIdealIdentity_StatementLA
import Definitions.Def_Formalism_GaussIdealIdentity_GaussIdealPrimality_GaussLocalizationLengthHolds
import Theorems.Thm_Formalism_DV_GaussP_maximalIdeal_eq
import Theorems.Thm_Formalism_DV_GaussP_algebraMap_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial IsLocalRing
noncomputable section
open Formalism Formalism.DV Formalism.DV.GaussP
variable (σ O : Type) [Fintype σ] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable [(gaussIdeal σ O).IsPrime]
local notation "A" => Localization.AtPrime (gaussIdeal σ O)
namespace Formalism.DV.GaussP
theorem _root_.solution : IsDiscreteValuationRing A := by
  obtain ⟨ϖ, hϖ⟩ := Submodule.IsPrincipal.principal (IsLocalRing.maximalIdeal O)
  have hϖ' : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} := hϖ
  have hmA : IsLocalRing.maximalIdeal A = Ideal.span {algebraMap O A ϖ} := by
    rw [maximalIdeal_eq σ O, hϖ', Ideal.map_span, Set.image_singleton]
  have hne : algebraMap O A ϖ ≠ 0 := by
    intro h0
    apply IsDiscreteValuationRing.not_a_field O
    rw [hϖ', Ideal.span_singleton_eq_bot]
    exact algebraMap_injective σ O (h0.trans (map_zero _).symm)
  have hnf : ¬ IsField A := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, hmA, Ideal.span_singleton_eq_bot]
    exact hne
  have hp : (IsLocalRing.maximalIdeal A).IsPrincipal := ⟨⟨_, hmA⟩⟩
  exact ((IsDiscreteValuationRing.TFAE A hnf).out 0 4).2 hp
end Formalism.DV.GaussP
