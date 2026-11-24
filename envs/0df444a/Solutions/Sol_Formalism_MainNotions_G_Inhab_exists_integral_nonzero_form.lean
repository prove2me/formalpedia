-- Prove2me | solution 1 for Formalism.MainNotions.G.Inhab.exists_integral_nonzero_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:54:17.883674+00:00
-- url     : https://prove2.me/submissions/b1735230-5050-42f3-9d7a-83f925d480cb

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLoc
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataForm
import Theorems.Thm_Formalism_MainNotions_G_Inhab_one_mem_Htup
import Theorems.Thm_Formalism_MainNotions_G_Inhab_one_mem_HtupW
import Theorems.Thm_Formalism_MainNotions_G_Inhab_oneFn_pos
import Theorems.Thm_Formalism_MainNotions_G_Inhab_oneFn_mem
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.Inhab
open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial
variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}
namespace Formalism.MainNotions.G.Inhab
theorem _root_.solution (h : HidaSetting p n' W Qq O Kf ι σ j w) :
    ∃ F : (gat1 h).Fn, F ∈ (gat1 h).M ∧ F ∈ (gat1 h).Mna ∧ F ≠ 0 := by
  have h0 : ∀ v, (gat1 h).P.lam0 v = fun _ _ => 0 := by
    intro v
    rfl
  have hχ : ∀ i, ((gat1 h).lev i).χ = 1 := by
    intro i
    rfl
  have hc : Nonempty (gat1 h).comp := by
    first
      | exact ⟨()⟩
      | (unfold gat1; exact (rfl : 1 = 1))
  obtain ⟨i0⟩ := hc
  let L0 : (gat1 h).P.Tup := fun v => colSpan ((gat1 h).P.W v)
    (1 : Matrix (Fin ((gat1 h).P.m + 1)) (Fin ((gat1 h).P.m + 1)) ((gat1 h).P.Qq v))
  have hL0 : (gat1 h).P.IsLatTup L0 := fun v => ⟨1, by simp, rfl⟩
  refine ⟨fun _ => oneFn (gat1 h).P, ?_, ?_, ?_⟩
  · simp only [GAtP.M, GAtP.funMod, Submodule.mem_pi]
    intro i _
    exact oneFn_mem (gat1 h).P ((gat1 h).lev i) h0 (hχ i) _ (fun L => one_mem_HtupW _ h0 L)
  · simp only [GAtP.Mna, GAtP.funMod, Submodule.mem_pi]
    intro i _
    exact oneFn_mem (gat1 h).P ((gat1 h).lev i) h0 (hχ i) _ (fun L => one_mem_Htup _ h0 L)
  · intro hF
    have h1 := congrFun (congrFun hF i0) L0
    simp only [Pi.zero_apply] at h1
    rw [oneFn_pos _ hL0] at h1
    exact one_ne_zero h1
end Formalism.MainNotions.G.Inhab
