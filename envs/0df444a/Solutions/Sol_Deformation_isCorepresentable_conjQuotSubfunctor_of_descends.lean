-- Prove2me | solution 1 for Deformation.isCorepresentable_conjQuotSubfunctor_of_descends
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/a106d3c6-055f-5867-a05f-3bc0bf89aa71

import Mathlib
import Definitions.Def_Deformations_ConjQuotSubfunctor
import Definitions.Def_Deformations_ClosedSubalgebra
import Definitions.Def_Mathlib_CategoryTheory_Corepresentable
import Theorems.Thm_Deformation_exists_weaklyInitial_elements_conjQuotSubfunctor
import Theorems.Thm_Deformation_exists_cond_lift_traceAlgebra
import Theorems.Thm_Deformation_hom_ext_of_mk_mapRepn_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_isCorepresentable_conjQuotSubfunctor_of_descends

p2m_open "CategoryTheory CategoryTheory.Limits"

universe u

set_option backward.isDefEq.respectTransparency false in

theorem solution
    {n : Type} [Fintype n] [DecidableEq n] {G : Type u} [Group G] [TopologicalSpace G]
    {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞] [Finite (IsLocalRing.ResidueField 𝓞)]
    {F : CategoryTheory.Subfunctor (Deformation.repnFunctor n G 𝓞)}
    (hconj : Deformation.ConjStable n F) (hrefl : Deformation.ReflectedByInjective n F)
    (hwi : ∃ T : F.toFunctor.Elements, ∀ X, Nonempty (T ⟶ X))
    (hdesc : ∀ (A : Deformation.ProartinianCat 𝓞), ∀ ρ' ∈ F.obj A, Deformation.TraceAlgebra.Descends ρ') :
    (Deformation.conjQuotSubfunctor n F).toFunctor.IsCorepresentable := by
  classical
  obtain ⟨T₀pre, hT₀pre⟩ := hwi
  obtain ⟨T₀, hT₀⟩ := Deformation.exists_weaklyInitial_elements_conjQuotSubfunctor n T₀pre hT₀pre
  obtain ⟨ρ', hρ'mem, hρ'eq⟩ := (Deformation.mem_conjQuotSubfunctor_obj_iff n T₀.2.1).mp T₀.2.2
  obtain ⟨σ, hσmem, hσgen, hσpush⟩ :=
    Deformation.exists_cond_lift_traceAlgebra hconj hrefl hρ'mem (hdesc T₀.1 ρ' hρ'mem)
  set e : (Deformation.conjQuotSubfunctor n F).toFunctor.Elements :=
    (Deformation.conjQuotSubfunctor n F).toFunctor.elementsMk (Deformation.TraceAlgebra.obj ρ')
      ⟨Quotient.mk'' σ, Deformation.mk_mem_conjQuotSubfunctor_obj n hσmem⟩ with he
  have hι : (Deformation.conjQuotSubfunctor n F).toFunctor.map (Deformation.TraceAlgebra.ι ρ') e.2 = T₀.2 := by
    refine Subtype.ext ?_
    show (Deformation.repnQuotFunctor n G 𝓞).map (Deformation.TraceAlgebra.ι ρ') (Quotient.mk'' σ) = T₀.2.1
    rw [← hρ'eq]
    exact hσpush
  have he_weak : ∀ X, Nonempty (e ⟶ X) := by
    intro X
    obtain ⟨f⟩ := hT₀ X
    exact ⟨CategoryOfElements.homMk e T₀ (Deformation.TraceAlgebra.ι ρ') hι ≫ f⟩
  have he_uniq : ∀ (X : (Deformation.conjQuotSubfunctor n F).toFunctor.Elements) (f g : e ⟶ X), f = g := by
    intro X f g
    refine CategoryOfElements.ext _ f g ?_
    refine Deformation.hom_ext_of_mk_mapRepn_eq hσgen ?_
    have h1 : (Deformation.repnQuotFunctor n G 𝓞).map f.val (Quotient.mk'' σ) = X.2.1 := congrArg Subtype.val f.2
    have h2 : (Deformation.repnQuotFunctor n G 𝓞).map g.val (Quotient.mk'' σ) = X.2.1 := congrArg Subtype.val g.2
    exact h1.trans h2.symm
  exact (Functor.corepresentableByOfIsInitial e
    (IsInitial.ofUniqueHom (fun X => (he_weak X).some)
      (fun X m => he_uniq X m (he_weak X).some))).isCorepresentable

end S_Deformation_isCorepresentable_conjQuotSubfunctor_of_descends
end P2MW
export P2MW.S_Deformation_isCorepresentable_conjQuotSubfunctor_of_descends (solution)
