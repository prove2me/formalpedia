-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.closedEqNabla_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:08.924878+00:00
-- url     : https://prove2.me/submissions/7f702ea7-9622-4637-b0ab-ee3f9c63a221

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_ClosedEqNabla
import Theorems.Thm_Formalism_GradedWeylDivisibility_lclosedeq_fd
import Theorems.Thm_Formalism_GradedWeylDivisibility_hwNe
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivStable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution (h1 : HWInClosed) (h2 : FockQPos) (h3 : FockQBilin) (h4 : FockQRowDivAdj) :
    ClosedEqNabla := by
  intro r n hn ν hν M hMV hMc hhw
  have hfdV : FiniteDimensional ℚ (dualWeyl ℚ r n ν) := lclosedeq_fd r n ν
  have hfdM : FiniteDimensional ℚ M := Submodule.finiteDimensional_of_le hMV
  let B := lclosedeq_B (σ := Fin r × Fin n) h2 h3
  have hB : ∀ f g, B f g = fockQ f g := fun _ _ => rfl
  let N : Submodule ℚ (MvPolynomial (Fin r × Fin n) ℚ) :=
    { carrier := {x | x ∈ dualWeyl ℚ r n ν ∧ ∀ g ∈ M, fockQ x g = 0}
      add_mem' := by
        rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
        refine ⟨Submodule.add_mem _ hx hy, fun g hg => ?_⟩
        rw [← hB, map_add, LinearMap.add_apply, hB, hB, hx' g hg, hy' g hg, add_zero]
      zero_mem' := ⟨Submodule.zero_mem _, fun g _ => by rw [← hB, map_zero, LinearMap.zero_apply]⟩
      smul_mem' := by
        rintro c x ⟨hx, hx'⟩
        refine ⟨Submodule.smul_mem _ c hx, fun g hg => ?_⟩
        rw [← hB, map_smul, LinearMap.smul_apply, hB, hx' g hg, smul_zero] }
  have hNV : N ≤ dualWeyl ℚ r n ν := fun x hx => hx.1
  have hNc : RowDivClosed N := by
    intro a b k f hf
    obtain ⟨hf1, hf2⟩ := hf
    refine ⟨rowDivStable ℚ r n ν a b k f hf1, fun g hg => ?_⟩
    rw [h4, hf2 _ (hMc b a k g hg)]
  have hN : N = ⊥ := by
    by_contra hne
    have hmem := h1 r n hn ν hν N hNV hNc hne
    have h0 := hmem.2 _ hhw
    have hpos := (h2 _ (hw ℚ hn ν) 0).2 (hwNe ℚ r n hn ν)
    linarith
  let BM := B.restrict M
  have hBM : ∀ x y : M, BM x y = fockQ (x : MvPolynomial (Fin r × Fin n) ℚ) y := fun _ _ => rfl
  have key : ∀ x : M, (∀ y : M, BM x y = 0) → x = 0 := by
    intro x hx
    by_contra hne
    have hx0 : (x : MvPolynomial (Fin r × Fin n) ℚ) ≠ 0 := fun h => hne (Subtype.ext h)
    have hpos := (h2 _ (x : MvPolynomial (Fin r × Fin n) ℚ) 0).2 hx0
    have h0 := hx x
    rw [hBM] at h0
    linarith
  have hnd : BM.Nondegenerate := by
    refine ⟨key, fun y hy => key y fun x => ?_⟩
    rw [hBM, (h2 _ _ _).1, ← hBM]
    exact hy x
  apply le_antisymm hMV
  intro f hf
  let φ : Module.Dual ℚ M := (B f).domRestrict M
  let p : M := (BM.toDual hnd).symm φ
  have hp : ∀ g : M, fockQ (p : MvPolynomial (Fin r × Fin n) ℚ) g = fockQ f g := by
    intro g
    have := LinearMap.BilinForm.apply_toDual_symm_apply (hB := hnd) φ g
    exact this
  have hd : f - p ∈ N := by
    refine ⟨Submodule.sub_mem _ hf (hMV p.2), fun g hg => ?_⟩
    rw [← hB, map_sub, LinearMap.sub_apply, hB, hB, ← hp ⟨g, hg⟩, sub_self]
  rw [hN] at hd
  have hfp : f = p := sub_eq_zero.mp ((Submodule.mem_bot ℚ).mp hd)
  rw [hfp]
  exact p.2
end Formalism.GradedWeylDivisibility
