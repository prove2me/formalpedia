-- Prove2me | solution 1 for CompactnessConjecture.symplecticQuadrangle_no_kQuotient_of_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:02.568649+00:00
-- url     : https://prove2.me/submissions/d13ac12d-c8f8-4682-8a5e-090200af8ec9

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_symplecticQuadrangle_kTemplate_has_line_gamma
import Theorems.Thm_CompactnessConjecture_symplecticQuadrangle_no_line_gamma_of_odd

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution
    (htwo : (2 : K) ≠ 0)
    {f : KVertex → KVertex} (hf : KAdmissible f) :
    (quotientGraph kTemplate f).Free
      (symplecticQuadrangle K) := by
  rintro ⟨copy⟩
  let hom : kTemplate →g symplecticQuadrangle K :=
    copy.toHom.comp (kQuotientProjectionHom hf)
  have hcopies : ∀ i : Fin 2,
      Set.InjOn hom {v : KVertex | v.1 = i} := by
    intro i u hu v hv huv
    change
      copy (⟨f u, u, rfl⟩ : Set.range f) =
        copy (⟨f v, v, rfl⟩ : Set.range f)
      at huv
    apply hf.2 i hu hv
    exact congrArg Subtype.val (copy.injective huv)
  obtain ⟨i, L, hL⟩ :=
    symplecticQuadrangle_kTemplate_has_line_gamma
      K hom hcopies
  exact symplecticQuadrangle_no_line_gamma_of_odd K htwo
    (kGammaHomCopy hom hcopies i) L hL
end CompactnessConjecture
