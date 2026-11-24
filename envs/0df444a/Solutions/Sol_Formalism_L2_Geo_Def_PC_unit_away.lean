-- Prove2me | solution 1 for Formalism.L2.Geo.Def.PC.unit_away
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:51:09.540805+00:00
-- url     : https://prove2.me/submissions/73ba6026-ba04-4a6f-88ca-11a10ec1dff0

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_GeometryDefinitions_PClassD
import Theorems.Thm_Formalism_UG_P_afsplitI_ne
import Theorems.Thm_Formalism_UG_P_afsplitI_self
import Theorems.Thm_Formalism_UG_P_levelaf_algebraMap_ne_zero
import Theorems.Thm_Formalism_UG_P_levelaf_finite_places
import Theorems.Thm_Formalism_UG_P_levelaf_int_mem_v


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG Formalism.UG.P
open Formalism Formalism.L2 Formalism.L2.Geo Formalism.L2.Geo.Def Formalism.L2.Geo.Def.PC
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
namespace Formalism.L2.Geo.Def.PC
theorem _root_.solution (D : 𝓞 F) (hD : D ≠ 0) :
    ∃ (T : Finset (HeightOneSpectrum (𝓞 F))) (u : 𝔸), u ∈ intAd F ∧
      (1 : 𝔸) = algebraMap (𝓞 F) 𝔸 D * u + ∑ v ∈ T, afsplitI v 1 := by
  classical
  have hmem : ∀ w : HeightOneSpectrum (𝓞 F),
      (if Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) D) < 1 then 0
        else (algebraMap (𝓞 F) (w.adicCompletion F) D)⁻¹) ∈ w.adicCompletionIntegers F := by
    intro w
    split_ifs with h
    · exact zero_mem _
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀]
      have h1 : Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) D) ≤ 1 := levelaf_int_mem_v w D
      have h2 : Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) D) = 1 := le_antisymm h1 (not_lt.1 h)
      rw [h2, inv_one]
  let u : 𝔸 := ⟨fun w => if Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) D) < 1 then 0
        else (algebraMap (𝓞 F) (w.adicCompletion F) D)⁻¹, Filter.Eventually.of_forall hmem⟩
  refine ⟨(levelaf_finite_places D hD).toFinset, u, hmem, ?_⟩
  refine FiniteAdeleRing.ext _ fun w => ?_
  have hsum : (∑ v ∈ (levelaf_finite_places D hD).toFinset, afsplitI v 1 : 𝔸) w =
      if w ∈ (levelaf_finite_places D hD).toFinset then 1 else 0 := by
    change evalV F w (∑ v ∈ (levelaf_finite_places D hD).toFinset, afsplitI v 1 : 𝔸) = _
    rw [map_sum]
    split_ifs with h
    · rw [Finset.sum_eq_single_of_mem w h]
      · exact afsplitI_self w 1
      · intro b _ hb; exact afsplitI_ne b w hb.symm 1
    · refine Finset.sum_eq_zero fun b hb => afsplitI_ne b w ?_ 1
      rintro rfl; exact h hb
  rw [afsplit_add_apply, afsplit_mul_apply, hsum]
  show (1 : w.adicCompletion F) = algebraMap (𝓞 F) (w.adicCompletion F) D *
    (if Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) D) < 1 then 0
        else (algebraMap (𝓞 F) (w.adicCompletion F) D)⁻¹) + _
  by_cases h : Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) D) < 1
  · have h' : w ∈ (levelaf_finite_places D hD).toFinset := by simpa using h
    rw [if_pos h, if_pos h', mul_zero, zero_add]
  · have h' : w ∉ (levelaf_finite_places D hD).toFinset := by simpa using h
    rw [if_neg h, if_neg h', add_zero, mul_inv_cancel₀ (levelaf_algebraMap_ne_zero w D hD)]
end Formalism.L2.Geo.Def.PC
