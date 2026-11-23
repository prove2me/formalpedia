-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RecursionWithDensities.B1.thetaDomination_dp_of_krPSD_of_domMin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:52:27.663872+00:00
-- url     : https://prove2.me/submissions/84f5e224-1371-4e6d-ab7c-e5f370cf4942

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequalitySplitBySize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_A1_psd_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_A1_mk_eq_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_B1_psd_congr
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_RecursionWithDensities_B1_psd_restrict__26d2ae93ba06
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_B1_mk_eq_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_B1_sel_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_B1_sel_mk
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_B1_join_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_B1_join_not_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_B1_ThR_psd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RecursionWithDensities Formalism.FourierDecayAlt.P.RecursionWithDensities.B1
open Finset Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data Formalism.FourierDecayAlt.TC
open scoped ComplexOrder
open Classical
variable {E W : Type} [Field E]
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.B1
theorem _root_.solution (D : Data E W) (T : Tower E) (Th : ℕ → ℕ → E → Pt E → Pt E → ℂ) (hK : KrPSD D)
    (hE : EBounds D) (hD : DomMin D T Th) : (Dp D T Th).ThetaDomination := by
  intro i s hs hsi hi
  obtain ⟨h1, h2, h3⟩ := hD i s hs hsi hi
  have hr : 1 ≤ s ∧ s ≤ i ∧ i ≤ D.r + 1 := ⟨hs, hsi, hi⟩
  refine ⟨hE i (by omega) hi, ?_, ?_, ?_⟩
  · intro t _ Y _
    show PSDOn Y (fun h h' => ThR D T Th i s t h h' - blk (KrR D T i) s t t h h')
    by_cases ht : t ∈ T.Sg (i - s + 1) s
    · have hg : good (D.La (i - s + 1) s) (T.Sg (i - s + 1) s) (t : E ⧸ D.La (i - s + 1) s) :=
        ⟨t, ht, rfl⟩
      refine psd_restrict' Y (h1 t ht) (fun x y hxy => ?_) (fun x y hxy => ?_)
      · simp only [ThR, if_pos (And.intro hr hg), blk, KrR, join_mem T hs hsi ht, if_pos hxy]
        rw [h2 _ (sel_mem hg) t ht ((mk_eq_iff _ _ _).1 (sel_mk hg)) x hxy.1 y hxy.2]
      · simp only [ThR, blk, KrR, join_mem T hs hsi ht, if_neg hxy, ite_self, sub_zero]
    · refine psd_congr (fun x _ y _ => ?_) (ThR_psd D T Th hK hD i s t Y)
      simp only [blk, KrR, join_not_mem T ht, false_and, if_false, sub_zero]
  · intro t t' htt
    show ThR D T Th i s t = ThR D T Th i s t'
    have e : (t : E ⧸ D.La (i - s + 1) s) = t' := (mk_eq_iff _ _ _).2 htt
    funext h h'
    simp only [ThR, e]
  · intro S hS Y _
    show PSDOn Y (fun h h' => (1 + (D.e i : ℂ)) * KrR D T (i - s) h h' - ∑ t ∈ S, ThR D T Th i s t h h')
    set L := D.La (i - s + 1) s with hL
    set G := T.Sg (i - s + 1) s with hG
    set S' : Finset E := (S.filter (fun t : E => good L G (t : E ⧸ L))).image
      (fun t : E => sel L G (t : E ⧸ L)) with hS'
    have hsub : S' ⊆ G := by
      intro x hx
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hx
      exact sel_mem (Finset.mem_filter.1 ht).2
    have hinc : ∀ t ∈ S', ∀ t' ∈ S', t - t' ∈ L → t = t' := by
      intro a ha b hb hab
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 ha
      obtain ⟨t', ht', rfl⟩ := Finset.mem_image.1 hb
      have e := (mk_eq_iff L _ _).2 hab
      rw [sel_mk (Finset.mem_filter.1 ht).2, sel_mk (Finset.mem_filter.1 ht').2] at e
      rw [e]
    have hinj : Set.InjOn (fun t : E => sel L G (t : E ⧸ L))
        (S.filter (fun t : E => good L G (t : E ⧸ L)) : Finset E) := by
      intro a ha b hb hab
      have ha' := Finset.mem_filter.1 (Finset.mem_coe.1 ha)
      have hb' := Finset.mem_filter.1 (Finset.mem_coe.1 hb)
      have e : (a : E ⧸ L) = b := by
        rw [← sel_mk ha'.2, ← sel_mk hb'.2]; exact congrArg _ hab
      exact hS a ha'.1 b hb'.1 ((mk_eq_iff L _ _).1 e)
    refine psd_restrict' Y (h3 S' hsub hinc) (fun x y hxy => ?_) (fun x y hxy => ?_)
    · have hsum : ∑ t ∈ S, ThR D T Th i s t x y = ∑ t₁ ∈ S', Th i s t₁ x y := by
        rw [hS', Finset.sum_image (f := fun t₁ => Th i s t₁ x y) hinj, Finset.sum_filter]
        refine Finset.sum_congr rfl fun t _ => ?_
        by_cases hg : good L G (t : E ⧸ L)
        · simp only [ThR, if_pos hg, if_pos hxy]
          exact if_pos (And.intro hr hg)
        · have : ¬ ((1 ≤ s ∧ s ≤ i ∧ i ≤ D.r + 1) ∧ good L G (t : E ⧸ L)) := fun h => hg h.2
          simp only [ThR, if_neg hg]
          exact if_neg this
      rw [hsum]
      simp only [KrR, if_pos hxy]
    · have : ∀ t ∈ S, ThR D T Th i s t x y = 0 := by
        intro t _
        simp only [ThR, if_neg hxy, ite_self]
      rw [Finset.sum_eq_zero this]
      simp only [if_neg hxy, KrR, mul_zero, sub_zero]
end Formalism.FourierDecayAlt.P.RecursionWithDensities.B1
