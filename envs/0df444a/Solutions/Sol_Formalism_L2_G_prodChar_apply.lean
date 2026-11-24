-- Prove2me | solution 1 for Formalism.L2.G.prodChar_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:01:33.835281+00:00
-- url     : https://prove2.me/submissions/14786284-f6ea-42ef-8b4a-40b1629802f3

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_LevelCharts_SignBlockDeterminant
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_LevelCharts_AtGGlob

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NumberField IsDedekindDomain Formalism.UG
open scoped TensorProduct
open Formalism Formalism.L2 Formalism.L2.G
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
namespace Formalism.L2.G
theorem _root_.solution {Z : Type} [CommGroup Z] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin N) (E ⊗[F] v.adicCompletion F)))
    (lam : ∀ v, v ∈ S → (Uloc v →* Z)) (Up : Subgroup (GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))
    (h : ∀ v ∈ S, Up ≤ (Uloc v).comap (bc (prV (E := E) v))) (x : Up) :
    prodChar S Uloc lam Up h x =
      ∏ v ∈ S.attach, lam v.1 v.2 ⟨bc (prV (E := E) v.1) (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), h v.1 v.2 x.2⟩ := by
  simp only [prodChar, MonoidHom.finsetProd_apply]
  rfl
end Formalism.L2.G
