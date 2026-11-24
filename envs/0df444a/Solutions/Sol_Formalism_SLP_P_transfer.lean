-- Prove2me | solution 1 for Formalism.SLP.P.transfer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:28:46.015957+00:00
-- url     : https://prove2.me/submissions/1e2ab66e-89cd-409d-8d5d-fef1a884b266

import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
import Mathlib
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_SubgroupCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.SLP Formalism.SLP.P
open AddSubgroup
namespace Formalism.SLP.P
theorem _root_.solution {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] (e : G ≃+ G') (n : ℕ)
    (h : ∀ j : ℕ, 1 ≤ j → {H : AddSubgroup G' | H.index = j}.Finite ∧
      {H : AddSubgroup G' | H.index = j}.ncard ≤ j ^ n) :
    ∀ j : ℕ, 1 ≤ j → {H : AddSubgroup G | H.index = j}.Finite ∧
      {H : AddSubgroup G | H.index = j}.ncard ≤ j ^ n := by
  intro j hj
  obtain ⟨hfin, hcard⟩ := h j hj
  let f : AddSubgroup G → AddSubgroup G' := fun H => H.comap e.symm.toAddMonoidHom
  have hmaps : ∀ H ∈ {H : AddSubgroup G | H.index = j},
      f H ∈ {H : AddSubgroup G' | H.index = j} := by
    intro H hH
    show (H.comap e.symm.toAddMonoidHom).index = j
    rw [index_comap_of_surjective _ e.symm.surjective]
    exact hH
  have hinj : Set.InjOn f {H : AddSubgroup G | H.index = j} :=
    (comap_injective e.symm.surjective).injOn
  refine ⟨Set.Finite.of_finite_image (hfin.subset ?_) hinj, ?_⟩
  · rintro _ ⟨H, hH, rfl⟩
    exact hmaps H hH
  exact (Set.ncard_le_ncard_of_injOn f hmaps hinj hfin).trans hcard
end Formalism.SLP.P
