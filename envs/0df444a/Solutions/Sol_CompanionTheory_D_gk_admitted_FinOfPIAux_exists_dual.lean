-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.FinOfPIAux.exists_dual
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:35.117035+00:00
-- url     : https://prove2.me/submissions/c1684ff6-0f69-44fa-b949-e43bac73008f

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_URepSchur
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_FinOfPI
import Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_diag_apply
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_coe_restrict_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil
attribute [local simp] CompanionTheory.LimBd.URep.UnitaryRep.coe_restrict_apply


attribute [local simp] CompanionTheory.D.gk.admitted.FinOfPIAux.diag_apply

set_option autoImplicit false
open scoped InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
open CompanionTheory.D.gk.admitted.FinOfPIAux
variable {G : Type} [Group G] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [CompleteSpace H]
namespace CompanionTheory.D.gk.admitted.FinOfPIAux
theorem _root_.solution {n : ℕ} (y : Fin n → H) (hy : LinearIndependent ℂ y) :
    ∃ φ : Fin n → H →L[ℂ] ℂ, ∀ i j, φ i (y j) = if i = j then 1 else 0 := by
  let S := Submodule.span ℂ (Set.range y)
  have : FiniteDimensional ℂ S := FiniteDimensional.span_of_finite ℂ (Set.finite_range y)
  let b := Module.Basis.span hy
  have h : ∀ i, ∃ ψ : H →L[ℂ] ℂ, ∀ s : S, ψ s = b.coord i s := by
    intro i
    obtain ⟨ψ, hψ, -⟩ := exists_extension_norm_eq S (LinearMap.toContinuousLinearMap (b.coord i))
    exact ⟨ψ, hψ⟩
  choose φ hφ using h
  refine ⟨φ, fun i j => ?_⟩
  have : (b j : H) = y j := congrArg Subtype.val (Module.Basis.span_apply hy j)
  rw [← this, hφ, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  simp [eq_comm]
end CompanionTheory.D.gk.admitted.FinOfPIAux
