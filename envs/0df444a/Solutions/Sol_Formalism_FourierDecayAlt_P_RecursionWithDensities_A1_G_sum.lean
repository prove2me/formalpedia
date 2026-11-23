-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RecursionWithDensities.A1.G_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:40:34.513516+00:00
-- url     : https://prove2.me/submissions/e8b810cf-c27c-4ff4-8741-456ecf14c85f

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequalitySplitBySize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_A1_mk_eq_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RecursionWithDensities Formalism.FourierDecayAlt.P.RecursionWithDensities.A1
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TA Finset
open scoped ComplexConjugate InnerProductSpace
open Classical
variable {α : Type}
variable {E : Type} [AddCommGroup E]
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.A1
theorem _root_.solution (L : AddSubgroup E) (S : Finset E) (Th : E → α → α → ℂ) (R : Finset E)
    (hR : ∀ x ∈ R, ∀ y ∈ R, x - y ∈ L → x = y) :
    ∃ S' : Finset E, S' ⊆ S ∧ (∀ x ∈ S', ∃ t ∈ R, x - t ∈ L) ∧
      (∀ x ∈ S', ∀ y ∈ S', x - y ∈ L → x = y) ∧
      ∀ h h', ∑ t ∈ R, G L S Th (t : E ⧸ L) h h' = ∑ t₁ ∈ S', Th t₁ h h' := by
  let f : E → E := fun t => if hc : ∃ t₁ ∈ S, (t₁ : E ⧸ L) = (t : E ⧸ L) then hc.choose else t
  have hf : ∀ t : E, (∃ t₁ ∈ S, (t₁ : E ⧸ L) = (t : E ⧸ L)) → f t ∈ S ∧ (f t : E ⧸ L) = (t : E ⧸ L) := by
    intro t hc
    simp only [f, dif_pos hc]
    exact hc.choose_spec
  have hG : ∀ (t : E) (h h' : α), G L S Th (t : E ⧸ L) h h' =
      if (∃ t₁ ∈ S, (t₁ : E ⧸ L) = (t : E ⧸ L)) then Th (f t) h h' else 0 := by
    intro t h h'
    by_cases hc : ∃ t₁ ∈ S, (t₁ : E ⧸ L) = (t : E ⧸ L)
    · rw [if_pos hc]
      unfold G
      simp only [f, dif_pos hc]
    · rw [if_neg hc]
      unfold G
      simp only [dif_neg hc]
  let R' := R.filter fun t : E => ∃ t₁ ∈ S, (t₁ : E ⧸ L) = (t : E ⧸ L)
  have hinj : Set.InjOn f R' := by
    intro x hx y hy hxy
    have hx' := Finset.mem_filter.mp hx
    have hy' := Finset.mem_filter.mp hy
    have e1 := (hf x hx'.2).2
    have e2 := (hf y hy'.2).2
    have : (x : E ⧸ L) = (y : E ⧸ L) := by rw [← e1, ← e2, hxy]
    exact hR x hx'.1 y hy'.1 ((mk_eq_iff L x y).mp this)
  refine ⟨R'.image f, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    exact (hf t (Finset.mem_filter.mp ht).2).1
  · intro x hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨t, (Finset.mem_filter.mp ht).1, (mk_eq_iff L _ _).mp (hf t (Finset.mem_filter.mp ht).2).2⟩
  · intro x hx y hy hxy
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp hy
    have e1 := (hf t (Finset.mem_filter.mp ht).2).2
    have e2 := (hf t' (Finset.mem_filter.mp ht').2).2
    have hc : (f t : E ⧸ L) = (f t' : E ⧸ L) := (mk_eq_iff L _ _).mpr hxy
    rw [e1, e2] at hc
    rw [hR t (Finset.mem_filter.mp ht).1 t' (Finset.mem_filter.mp ht').1 ((mk_eq_iff L t t').mp hc)]
  · intro h h'
    rw [Finset.sum_image hinj]
    simp only [hG]
    rw [Finset.sum_filter]
end Formalism.FourierDecayAlt.P.RecursionWithDensities.A1
