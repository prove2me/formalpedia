-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.LatticeIndexBis.idx_map_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:35:27.773798+00:00
-- url     : https://prove2.me/submissions/442c005f-1d2c-460a-9e79-340a56ea15c3

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_BetaSesquilinearity
import Definitions.Def_Formalism_LogFactorialIndices_LogProductFormula
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SubspaceLatticeIndexSigned
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LatticeIndexBis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeBaseChangeAlt
open Module
open Formalism.LatticeBaseChangeAlt.LatticeIndexBis
namespace Formalism.LatticeBaseChangeAlt.LatticeIndexBis
theorem _root_.solution {O Y X : Type} [CommRing O] [AddCommGroup Y] [Module O Y]
    [AddCommGroup X] [Module O X] (ι : Y →ₗ[O] X) (hι : Function.Injective ι)
    (P Q : Submodule O Y) :
    Formalism.LatticeIndexTer.idx O X (P.map ι) (Q.map ι) = Formalism.LatticeIndexTer.idx O Y P Q := by
  have key : ∀ P₁ Q₁ : Submodule O Y,
      Module.length O (↥(P₁.map ι) ⧸ Submodule.comap (P₁.map ι).subtype (Q₁.map ι)) =
        Module.length O (↥P₁ ⧸ Submodule.comap P₁.subtype Q₁) := by
    intro P₁ Q₁
    let e : P₁ ≃ₗ[O] P₁.map ι := Submodule.equivMapOfInjective ι hι P₁
    have hm : (Submodule.comap P₁.subtype Q₁).map (e : P₁ →ₗ[O] P₁.map ι) =
        Submodule.comap (P₁.map ι).subtype (Q₁.map ι) := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨(y : Y), hy, rfl⟩
      · intro hz
        obtain ⟨q, hq, hqz⟩ := hz
        obtain ⟨p, hp, hpz⟩ := z.2
        refine ⟨⟨p, hp⟩, ?_, Subtype.ext hpz⟩
        have hpq : q = p := hι (hqz.trans hpz.symm)
        show p ∈ Q₁
        rw [← hpq]
        exact hq
    exact (Submodule.Quotient.equiv _ _ e hm).length_eq.symm
  unfold Formalism.LatticeIndexTer.idx Formalism.LatticeIndexTer.qlen
  rw [key P Q, key Q P]
end Formalism.LatticeBaseChangeAlt.LatticeIndexBis
