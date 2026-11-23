-- Prove2me | solution 1 for Formalism.UG.P.levelv_S_le_range
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:02.131919+00:00
-- url     : https://prove2.me/submissions/280619a7-a045-4718-bd5f-2e695511c876

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
open IsDedekindDomain NumberField
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))
namespace Formalism.UG.P
theorem _root_.solution (y : E ⊗[F] v.adicCompletion F) (hy : y ∈ lvS F E v) :
    y ∈ (levelvPsi F E v).range := by
  have hle : lvS F E v ≤ levelvT F E v := by
    apply Subring.closure_le.mpr
    rintro z (⟨⟨e, he⟩, rfl⟩ | ⟨⟨x, hx⟩, rfl⟩)
    · obtain ⟨e', rfl⟩ := RingHom.mem_range.mp he
      show algebraMap (𝓞 E) E e' ⊗ₜ[F] (1 : v.adicCompletion F) ∈ (levelvPsi F E v).range
      simpa using levelv_tmul_mem_range v e' 1
    · show (1 : E) ⊗ₜ[F] x ∈ (levelvPsi F E v).range
      have h := levelv_tmul_mem_range (E := E) v 1 ⟨x, hx⟩
      first
        | exact h
        | (rw [map_one] at h; exact h)
        | simpa using h
  exact hle hy
end Formalism.UG.P
