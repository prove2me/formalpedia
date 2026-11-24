-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.weyl_shift_eq_map_det_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:33:48.492316+00:00
-- url     : https://prove2.me/submissions/b7f96ea5-9a47-4728-845c-0d58165196b8

import Definitions.Def_Formalism_PieriBlockIdeals_ExZTranslate
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Theorems.Thm_Formalism_CohomologicalDescent_LA_divided_power_stable_det_mul
import Theorems.Thm_Formalism_CohomologicalDescent_LA_det_mul_divided_power_mem
import Theorems.Thm_Formalism_CohomologicalDescent_LA_highest_weight_shift_eq_det_mul
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply


section
open MvPolynomial
noncomputable section
namespace Formalism.CohomologicalDescent.LA
open Formalism.GradedWeylDivisibility
private theorem divOp_mem_weyl (R : Type) [CommRing R] {r : ℕ} (μ : Fin r → ℕ)
    (a b : Fin r) (k : ℕ) (f : MvPolynomial (Fin r × Fin r) R)
    (hf : f ∈ weyl R r r le_rfl μ) : rowDiv R a b k f ∈ weyl R r r le_rfl μ := by
  unfold weyl at hf ⊢
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    exact Submodule.subset_span ⟨(a, b, k) :: w, rfl⟩
  | zero => simp [rowDiv]
  | add x y _ _ hx hy =>
    unfold rowDiv at hx hy ⊢
    rw [map_add, Polynomial.coeff_add]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    unfold rowDiv at hx ⊢
    rw [map_smul, Polynomial.coeff_smul]
    exact Submodule.smul_mem _ c hx
private theorem applyWord_mem_of_stable' (R : Type) [CommRing R] {r : ℕ}
    (L : Submodule R (MvPolynomial (Fin r × Fin r) R))
    (hs : ∀ (a b : Fin r) (k : ℕ) (f : MvPolynomial (Fin r × Fin r) R), f ∈ L →
      rowDiv R a b k f ∈ L) (w : List (Fin r × Fin r × ℕ)) (f : MvPolynomial (Fin r × Fin r) R)
    (hf : f ∈ L) : applyWord R w f ∈ L := by
  induction w with
  | nil => exact hf
  | cons x w ih => exact hs x.1 x.2.1 x.2.2 _ ih
private theorem hw_mem_weyl (R : Type) [CommRing R] {r : ℕ} (μ : Fin r → ℕ) :
    hw R le_rfl μ ∈ weyl R r r le_rfl μ := by
  unfold weyl
  exact Submodule.subset_span ⟨[], rfl⟩
private theorem genericDet_mul_applyWord_mem (R : Type) [CommRing R] {r : ℕ}
    (W : Submodule R (MvPolynomial (Fin r × Fin r) R))
    (hW : ∀ (a b : Fin r) (k : ℕ) (f : MvPolynomial (Fin r × Fin r) R), f ∈ W →
      rowDiv R a b k f ∈ W) (w : List (Fin r × Fin r × ℕ)) (f : MvPolynomial (Fin r × Fin r) R)
    (hf : genericDet R r * f ∈ W) : genericDet R r * applyWord R w f ∈ W := by
  induction w with
  | nil => exact hf
  | cons x w ih => exact det_mul_divided_power_mem R W hW x.1 x.2.1 x.2.2 _ ih
end Formalism.CohomologicalDescent.LA
end
end

set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LA
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LA
theorem _root_.solution (R : Type) [CommRing R] {r : ℕ} (ν : Fin r → ℕ) :
    weyl R r r le_rfl (fun a => ν a + 1) =
      (weyl R r r le_rfl ν).map (LinearMap.mulLeft R (genericDet R r)) := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨w, rfl⟩
    simp only [SetLike.mem_coe]
    rw [highest_weight_shift_eq_det_mul]
    exact applyWord_mem_of_stable' R ((weyl R r r le_rfl ν).map (LinearMap.mulLeft R (genericDet R r)))
      (fun a b k f hf => divided_power_stable_det_mul R (weyl R r r le_rfl ν) (divOp_mem_weyl R ν) a b k f hf)
      w _ (Submodule.mem_map.mpr ⟨_, hw_mem_weyl R ν, by simp⟩)
  · rw [Submodule.map_le_iff_le_comap]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨w, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulLeft_apply]
    apply genericDet_mul_applyWord_mem R (weyl R r r le_rfl (fun a => ν a + 1))
      (divOp_mem_weyl R (fun a => ν a + 1)) w
    rw [← highest_weight_shift_eq_det_mul]
    exact hw_mem_weyl R _
end Formalism.CohomologicalDescent.LA
