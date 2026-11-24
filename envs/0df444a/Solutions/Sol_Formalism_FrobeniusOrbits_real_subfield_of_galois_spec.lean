-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.real_subfield_of_galois_spec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:22.794867+00:00
-- url     : https://prove2.me/submissions/9ebca824-878c-47ec-a66a-df11b4cd73c4

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_RealCyclotomicSubfield
import Theorems.Thm_Formalism_FrobeniusOrbits_RealCyclotomicSubfield_fix_on_adjoin
import Theorems.Thm_Formalism_FrobeniusOrbits_RealCyclotomicSubfield_real_subfield_real_embeddings
import Theorems.Thm_Formalism_FrobeniusOrbits_RealCyclotomicSubfield_finrank_real_subfield
import Theorems.Thm_Formalism_FrobeniusOrbits_RealCyclotomicSubfield_maxReal_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Polynomial
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open RealCyclotomicSubfield
namespace Formalism.FrobeniusOrbits
theorem _root_.solution (hSpec : HostGalSpec) : TwoPowerCyclotomicLayerRealSubfieldCharacterization := by
  intro e q d hq L _ _ ζ a b h
  have hζ : IsPrimitiveRoot ζ (2 ^ (e + 2)) := h.1
  refine ⟨?_, maxReal_iff hζ, finrank_real_subfield hζ, real_subfield_real_embeddings hζ, ?_⟩
  · exact hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  · intro σ
    obtain ⟨-, -, h3, -⟩ := hSpec e q d hq L ζ a b h σ
    haveI : Fact (1 < 2 ^ (e + 2)) := ⟨by
      calc 1 < 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (e + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)⟩
    have key := h3 1
    have hc1 : hcl e 1 = 1 := QuotientGroup.mk_one _
    simp only [Units.val_one, ZMod.val_one, pow_one, hc1] at key
    rw [key]
    constructor
    · intro hσ
      exact fix_on_adjoin (t := ζ + ζ⁻¹) σ (le_sup_right : F1 ζ ≤ E0 a b ⊔ F1 ζ) hσ
    · intro hfix
      have h4 := hfix (thE ζ a b) (mem_adjoin_simple_self ℚ _)
      rw [h4]
      rfl
end Formalism.FrobeniusOrbits
