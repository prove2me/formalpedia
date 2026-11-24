-- Prove2me | solution 1 for Formalism.UG.P.csGlob_N_fg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:56:30.599477+00:00
-- url     : https://prove2.me/submissions/5d2de980-14fc-4646-9938-b769a977cc7d

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlobApprox
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Theorems.Thm_Formalism_UG_P_adelstab_dual
import Theorems.Thm_Formalism_UG_P_adelstab_tr_mem
import Theorems.Thm_Formalism_UG_P_sf_den


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ι" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
namespace Formalism.UG.P
theorem _root_.solution : (csGlobN F E).FG := by
  classical
  set β := Module.finBasis F E
  obtain ⟨d₀, hd₀, -, hd₀i⟩ := sf_den (fun i => β i)
  set β' := (Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) β
  set W : Submodule (𝓞 F) E := Submodule.span (𝓞 F) (Set.range fun i => d₀⁻¹ * β' i)
  have hle : csGlobN F E ≤ W := by
    intro e he
    have h1 := adelstab_dual β d₀ hd₀i e (adelstab_tr_mem e he)
    let Lm : E →ₗ[𝓞 F] E := (LinearMap.mulLeft F d₀⁻¹).restrictScalars (𝓞 F)
    have h2 := Submodule.mem_map_of_mem (f := Lm) h1
    rw [Submodule.map_span] at h2
    have h3 : Lm (d₀ * e) = e := by
      simp only [Lm, LinearMap.coe_restrictScalars, LinearMap.mulLeft_apply]
      rw [← mul_assoc, inv_mul_cancel₀ hd₀, one_mul]
    rw [h3] at h2
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  have : Module.Finite (𝓞 F) W := Module.Finite.span_of_finite _ (Set.finite_range _)
  have : IsNoetherian (𝓞 F) W := inferInstance
  have : IsNoetherian (𝓞 F) (csGlobN F E) := isNoetherian_of_le hle
  exact Module.Finite.iff_fg.mp inferInstance
end Formalism.UG.P
