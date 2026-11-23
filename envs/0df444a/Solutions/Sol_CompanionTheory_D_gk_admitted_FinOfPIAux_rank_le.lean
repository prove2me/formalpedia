-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.FinOfPIAux.rank_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:51:42.886966+00:00
-- url     : https://prove2.me/submissions/d5a0a93e-27de-4a18-bfb5-fa93c59bf821

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_URepSchur
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_FinOfPI
import Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_diag_apply
import Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_stdPoly_apply
import Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_exists_dual
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
theorem _root_.solution (E : H →L[ℂ] H) (M : ℕ) (h : ∀ a : Fin M → H →L[ℂ] H, stdPoly E a = 0) :
    Module.rank ℂ (LinearMap.range (E : H →ₗ[ℂ] H)) ≤ M := by
  by_contra hlt
  have hle : ((M + 1 : ℕ) : Cardinal) ≤ Module.rank ℂ (LinearMap.range (E : H →ₗ[ℂ] H)) := by
    rw [Nat.cast_succ]
    exact Cardinal.natCast_add_one_le_iff.mpr (not_le.mp hlt)
  obtain ⟨v, hv⟩ := Module.le_rank_iff.mp hle
  have hy : LinearIndependent ℂ fun i => (v i : H) :=
    hv.map' (LinearMap.range (E : H →ₗ[ℂ] H)).subtype (Submodule.ker_subtype _)
  obtain ⟨φ, hφ⟩ := exists_dual _ hy
  choose x hx using fun i => (v i).2
  have hx' : ∀ i, E (x i) = v i := hx
  let φ' : ℕ → H →L[ℂ] ℂ := fun i => if hi : i < M + 1 then φ ⟨i, hi⟩ else 0
  let x' : ℕ → H := fun i => if hi : i < M + 1 then x ⟨i, hi⟩ else 0
  have hφ' : ∀ i ≤ M, ∀ j ≤ M, φ' i (E (x' j)) = if i = j then 1 else 0 := by
    intro i hi j hj
    simp only [φ', x', dif_pos (Nat.lt_succ_of_le hi), dif_pos (Nat.lt_succ_of_le hj), hx', hφ, Fin.mk.injEq]
  have h1 := stdPoly_apply E M φ' x' hφ'
  rw [h] at h1
  have h2 := hφ' 0 (Nat.zero_le _) 0 (Nat.zero_le _)
  rw [← h1] at h2
  simp at h2
end CompanionTheory.D.gk.admitted.FinOfPIAux
