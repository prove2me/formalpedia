-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms.card_hermSub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:47.301346+00:00
-- url     : https://prove2.me/submissions/ff68cd2f-95dc-4ef0-b0f6-ff757063cbf8

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySeventh
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityEighth
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_reductionMapsOfForms_exists_unit_quot
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HermitianSublattices_card_entSub
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HermitianSublattices_card_hermSub_sq
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_card_ker_piQ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_finite_quot
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_ker_piQ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_star_mem_idQ


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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms
open HermitianSublattices idealPowerSpanBounds traceDeterminantCongruences
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable [Fact (IsFixF K F)]
variable {m r : Type} [Fintype m] [Fintype r] [DecidableEq m] [DecidableEq r]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) :
    Nat.card (hermSub r (RingHom.ker (piQ K 𝔭 k))) =
      Ideal.absNorm 𝔭 ^ (Fintype.card r * Fintype.card r) := by
  haveI := finite_quot (K := K) h𝔭 (k + 1)
  have hF : IsFixF K F := Fact.out
  obtain ⟨θ, e, he⟩ := exists_unit_quot hK h𝔭 (k + 1)
  have hJ : ∀ a ∈ RingHom.ker (piQ K 𝔭 k), star a ∈ RingHom.ker (piQ K 𝔭 k) := by
    intro a ha
    rw [ker_piQ] at ha ⊢
    exact star_mem_idQ ha
  have h1 := card_hermSub_sq (r := r) hJ he
  rw [card_entSub, card_ker_piQ hK hF h𝔭 k, ← pow_mul, mul_comm 2, pow_mul] at h1
  exact Nat.pow_left_injective (by norm_num) h1
end Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms
