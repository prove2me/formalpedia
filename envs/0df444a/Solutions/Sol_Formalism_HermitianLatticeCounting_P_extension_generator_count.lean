-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.extension_generator_count
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:14.332869+00:00
-- url     : https://prove2.me/submissions/1b996418-65d8-493f-851c-8ab538f59822

import Definitions.Def_Formalism_FlagUnipotentLattices_IdealCountLeW
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Lemmata_GeneralBFactSecondMore_Imports
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open NumberField
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : ExtGen := by
  intro R Q _ _ _ N e₁ e₂ s t hs ht
  choose t' ht' using fun i => Submodule.Quotient.mk_surjective N (t i)
  refine ⟨Fin.append s t', ?_⟩
  have hsub1 : N ≤ Submodule.span R (Set.range (Fin.append s t')) := by
    rw [← hs]; apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩; exact ⟨Fin.castAdd e₂ i, by simp⟩
  have hsub2 : Submodule.span R (Set.range t') ≤ Submodule.span R (Set.range (Fin.append s t')) := by
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩; exact ⟨Fin.natAdd e₁ i, by simp⟩
  rw [eq_top_iff]
  intro x _
  have hx : (Submodule.Quotient.mk x : Q ⧸ N) ∈ Submodule.span R (Set.range t) := by rw [ht]; trivial
  have hmap : Submodule.span R (Set.range t) = (Submodule.span R (Set.range t')).map N.mkQ := by
    rw [Submodule.map_span, ← Set.range_comp]
    congr 1
    ext z; constructor
    · rintro ⟨i, rfl⟩; exact ⟨i, ht' i⟩
    · rintro ⟨i, rfl⟩; exact ⟨i, (ht' i).symm⟩
  rw [hmap] at hx
  obtain ⟨w, hw, hwx⟩ := hx
  have : x - w ∈ N := by
    rw [← Submodule.Quotient.eq]; exact hwx.symm
  have hx2 : x = (x - w) + w := by abel
  rw [hx2]
  exact Submodule.add_mem _ (hsub1 this) (hsub2 hw)
end Formalism.HermitianLatticeCounting.P
