-- Prove2me | solution 1 for Formalism.L2.G.Triv.proG_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:01:34.028463+00:00
-- url     : https://prove2.me/submissions/67b70d03-8949-4d31-bd0d-391bde67da6a

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_TrivialTransfer_ProGTransfer
import Theorems.Thm_Formalism_BasicNotions_Spaces_baseGram_isHermitian


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions
open scoped TensorProduct
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Triv
variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
namespace Formalism.L2.G.Triv
theorem _root_.solution (h1 : IwProG) (h2 : ProGTransfer) (L : ColLevel R F E sp gp C A clsLat) (hp : ∀ i, (gp i).Prime)
    (hdet : IsUnit sp.gram0.det)
    (halg : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal) (a : v.adicCompletion F),
      L.splitG i v h ((1 : E) ⊗ₜ[F] a) = (a, a)) : L.ProG := fun i v h =>
  h2 F E R.k sp.cm.sig sp.gram0 sp.baseGram_isHermitian hdet v (L.splitG i v h) (L.splitG_sig i v h) (halg i v h) (L.frG i v h)
    (iwU F R.k v) (L.Uloc v) (L.Uloc_le v) (L.Uloc_g i v h) (gp i) (h1 F R.k v (gp i) (hp i) h)
end Formalism.L2.G.Triv
