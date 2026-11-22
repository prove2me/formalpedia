-- Prove2me | solution 1 for Formalism.UG.P.levelv_mem_lat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:52:10.669832+00:00
-- url     : https://prove2.me/submissions/1a92fc18-30da-4424-85a1-0fe8af2f8fb4

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
  (v : HeightOneSpectrum (𝓞 F)) {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution (x : n → E ⊗[F] v.adicCompletion F) :
    x ∈ stdLat (n := n) ↥(lvS F E v) ↔ ∀ j, x j ∈ lvS F E v := by
  rw [stdLat, Submodule.mem_pi]
  refine ⟨fun h j => ?_, fun h j _ => ?_⟩
  · obtain ⟨s, hs⟩ := LinearMap.mem_range.mp (h j (Set.mem_univ j))
    rw [← hs]
    exact s.2
  · exact LinearMap.mem_range.mpr ⟨⟨x j, h j⟩, rfl⟩
end Formalism.UG.P
