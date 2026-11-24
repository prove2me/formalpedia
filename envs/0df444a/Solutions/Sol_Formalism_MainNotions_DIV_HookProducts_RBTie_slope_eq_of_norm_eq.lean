-- Prove2me | solution 1 for Formalism.MainNotions.DIV.HookProducts.RBTie.slope_eq_of_norm_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:39:02.647564+00:00
-- url     : https://prove2.me/submissions/9b92757e-4423-40e9-a1d4-101d12793d10

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_SharpRestriction_Divisibility_HookProducts_RBTieSlope
import Theorems.Thm_Formalism_HN_Rerealization_covol_rk_eq
import Theorems.Thm_Formalism_HN_Rerealization_eq_of_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.DIV Formalism.MainNotions.DIV.HookProducts Formalism.MainNotions.DIV.HookProducts.RBTie
namespace Formalism.MainNotions.DIV.HookProducts.RBTie
theorem _root_.solution {R V E F : Type*} [Ring R] [AddCommGroup V] [Module R V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (ρ : V →+ E) (ρ₂ : V →+ F) (hn : ∀ x, ‖ρ₂ x‖ = ‖ρ x‖) (N : Submodule R V) :
    Formalism.HN.slope ρ₂ N = Formalism.HN.slope ρ N := by
  classical
  have memL : ∀ y : E, y ∈ Formalism.HN.zl ρ N ↔ ∃ x ∈ N.toAddSubgroup, ρ x = y := by
    intro y
    show y ∈ (N.toAddSubgroup.map ρ) ↔ _
    exact AddSubgroup.mem_map
  have memM : ∀ y : F, y ∈ Formalism.HN.zl ρ₂ N ↔ ∃ x ∈ N.toAddSubgroup, ρ₂ x = y := by
    intro y
    show y ∈ (N.toAddSubgroup.map ρ₂) ↔ _
    exact AddSubgroup.mem_map
  let pre : Formalism.HN.zl ρ N → V := fun y => Classical.choose ((memL y).1 y.2)
  have pre_mem : ∀ y, pre y ∈ N.toAddSubgroup := fun y =>
    (Classical.choose_spec ((memL y).1 y.2)).1
  have pre_eq : ∀ y, ρ (pre y) = y := fun y => (Classical.choose_spec ((memL y).1 y.2)).2
  let f0 : Formalism.HN.zl ρ N →+ Formalism.HN.zl ρ₂ N :=
    AddMonoidHom.mk' (fun y => ⟨ρ₂ (pre y), (memM _).2 ⟨pre y, pre_mem y, rfl⟩⟩) (by
      intro y z
      apply Subtype.ext
      show ρ₂ (pre (y + z)) = ρ₂ (pre y) + ρ₂ (pre z)
      rw [← map_add]
      apply Formalism.HN.Rerealization.eq_of_eq ρ ρ₂ hn
      rw [map_add, pre_eq, pre_eq, pre_eq]
      rfl)
  have f0_apply : ∀ y, ((f0 y : Formalism.HN.zl ρ₂ N) : F) = ρ₂ (pre y) := fun y => rfl
  have f0_norm : ∀ y, ‖((f0 y : Formalism.HN.zl ρ₂ N) : F)‖ = ‖(y : E)‖ := by
    intro y
    rw [f0_apply, hn, pre_eq]
  have hinj : Function.Injective f0 := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    have h0 : ‖(y : E)‖ = 0 := by
      rw [← f0_norm, hy]
      simp
    exact Subtype.ext (norm_eq_zero.1 h0)
  have hsurj : Function.Surjective f0 := by
    rintro ⟨z, hz⟩
    obtain ⟨x, hx, rfl⟩ := (memM z).1 hz
    refine ⟨⟨ρ x, (memL _).2 ⟨x, hx, rfl⟩⟩, Subtype.ext ?_⟩
    rw [f0_apply]
    exact Formalism.HN.Rerealization.eq_of_eq ρ ρ₂ hn (pre_eq _)
  let e : Formalism.HN.zl ρ N ≃+ Formalism.HN.zl ρ₂ N := AddEquiv.ofBijective f0 ⟨hinj, hsurj⟩
  have e_norm : ∀ y, ‖e y‖ = ‖y‖ := fun y => f0_norm y
  have e_symm_norm : ∀ z, ‖e.symm z‖ = ‖z‖ := by
    intro z
    rw [← e_norm (e.symm z), e.apply_symm_apply]
  have iso : Isometry e := AddMonoidHomClass.isometry_of_norm e e_norm
  have iso_symm : Isometry e.symm := AddMonoidHomClass.isometry_of_norm e.symm e_symm_norm
  have hiff : DiscreteTopology (Formalism.HN.zl ρ N) ↔ DiscreteTopology (Formalism.HN.zl ρ₂ N) := by
    constructor
    · intro h
      exact iso_symm.isEmbedding.discreteTopology
    · intro h
      exact iso.isEmbedding.discreteTopology
  have hrk : Formalism.F.rk (Formalism.HN.zl ρ₂ N) = Formalism.F.rk (Formalism.HN.zl ρ N) := by
    unfold Formalism.F.rk
    exact e.toIntLinearEquiv.finrank_eq.symm
  have hcov : Formalism.F.covol (Formalism.HN.zl ρ₂ N) = Formalism.F.covol (Formalism.HN.zl ρ N) := by
    by_cases h : DiscreteTopology (Formalism.HN.zl ρ N)
    · exact (Formalism.HN.Rerealization.covol_rk_eq ρ ρ₂ hn N.toAddSubgroup h (hiff.1 h)).1
    · have h' : ¬ DiscreteTopology (Formalism.HN.zl ρ₂ N) := fun h' => h (hiff.2 h')
      unfold Formalism.F.covol
      rw [dif_neg h, dif_neg h']
  unfold Formalism.HN.slope Formalism.F.slope Formalism.F.deg
  rw [hcov, hrk]
end Formalism.MainNotions.DIV.HookProducts.RBTie
