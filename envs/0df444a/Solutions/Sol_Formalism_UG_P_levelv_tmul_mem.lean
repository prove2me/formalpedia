-- Prove2me | solution 1 for Formalism.UG.P.levelv_tmul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:23:29.274949+00:00
-- url     : https://prove2.me/submissions/32fedf09-a3bd-408e-bb7a-5495d228ac88

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
theorem _root_.solution (e : E) (he : e ∈ intOE E) (x : v.adicCompletion F)
    (hx : x ∈ v.adicCompletionIntegers F) : e ⊗ₜ[F] x ∈ lvS F E v := by
  have h1 : e ⊗ₜ[F] (1 : v.adicCompletion F) ∈ lvS F E v := by
    apply Subring.subset_closure
    exact Set.mem_union_left _ ⟨⟨e, he⟩, rfl⟩
  have h2 : (1 : E) ⊗ₜ[F] x ∈ lvS F E v := by
    apply Subring.subset_closure
    exact Set.mem_union_right _ ⟨⟨x, hx⟩, rfl⟩
  simpa using mul_mem h1 h2
end Formalism.UG.P
