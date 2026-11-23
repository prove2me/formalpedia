-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx8.t_UniformMajorantOn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:41:40.119313+00:00
-- url     : https://prove2.me/submissions/65f1b20a-cff5-4a4b-8e5b-2d8547a1e7e0

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_tb_iff_ta
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_t_UniformMajorant
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_psd_pull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexOrder ComplexConjugate Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx8
namespace Formalism.FourierDecayAlt.P.Jx8
theorem _root_.solution : UniformMajorantOn := by
  classical
  intro E α _ A N B L L' hyp
  obtain ⟨Th', hTh'⟩ := t_UniformMajorant E {h // h ∈ A} (fun t t' h h' => N t t' h.1 h'.1)
    (fun h h' => B h.1 h'.1) L L' (by
    intro F'
    obtain ⟨Th, h1, h2, h3, h4, h5, h6⟩ := hyp (F'.image Subtype.val) (by
      intro h hh; obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 hh; exact x.2)
    have hm : ∀ x ∈ F', (x : α) ∈ F'.image Subtype.val := fun x hx => Finset.mem_image_of_mem _ hx
    let f : F' → (F'.image Subtype.val : Finset α) := fun x => ⟨x.1.1, hm x.1 x.2⟩
    refine ⟨fun t h h' => Th t h.1 h'.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro t t' ht ht' h hh h' hh' hne
      exact h1 t t' ht ht' h.1 (hm h hh) h'.1 (hm h' hh') hne
    · intro t ht; exact psd_pull f (fun _ _ => rfl) (h2 t ht)
    · intro t t' htt h hh h' hh'; exact h3 t t' htt h.1 (hm _ hh) h'.1 (hm _ hh')
    · intro t; exact psd_pull f (fun _ _ => rfl) (h4 t)
    · intro t ht; exact psd_pull f (fun _ _ => rfl) (h5 t ht)
    · intro R hR; exact psd_pull f (fun _ _ => rfl) (h6 R hR))
  let Th : E → α → α → ℂ := fun t h h' =>
    if hh : h ∈ A ∧ h' ∈ A then Th' t ⟨h, hh.1⟩ ⟨h', hh.2⟩ else 0
  have hT : ∀ t x y (hx : x ∈ A) (hy : y ∈ A), Th t x y = Th' t ⟨x, hx⟩ ⟨y, hy⟩ :=
    fun t x y hx hy => dif_pos ⟨hx, hy⟩
  have hz : ∀ t x y, ¬ (x ∈ A ∧ y ∈ A) → Th t x y = 0 := fun t x y h => dif_neg h
  have part1 : ∀ F : Finset α, (∀ h ∈ F, h ∈ A) → (LocSys.mk N Th B L L').Ok F := by
    intro F hF
    obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hTh' (F.subtype (· ∈ A))
    let f : F → (F.subtype (· ∈ A) : Finset {h // h ∈ A}) :=
      fun x => ⟨⟨x.1, hF x.1 x.2⟩, Finset.mem_subtype.2 x.2⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro t t' ht ht' h hh h' hh' hne
      exact g1 t t' ht ht' ⟨h, hF h hh⟩ (Finset.mem_subtype.2 hh) ⟨h', hF h' hh'⟩
        (Finset.mem_subtype.2 hh') hne
    · intro t ht; exact psd_pull f (fun _ _ => rfl) (g2 t ht)
    · intro t t' htt h hh h' hh'
      show Th t h h' = Th t' h h'
      rw [hT t h h' (hF h hh) (hF h' hh'), hT t' h h' (hF h hh) (hF h' hh')]
      exact g3 t t' htt ⟨h, hF h hh⟩ (Finset.mem_subtype.2 hh) ⟨h', hF h' hh'⟩
        (Finset.mem_subtype.2 hh')
    · intro t
      exact psd_pull f (fun x y => hT t x.1 y.1 (hF x.1 x.2) (hF y.1 y.2)) (g4 t)
    · intro t ht
      refine psd_pull f (fun x y => ?_) (g5 t ht)
      show Th t x.1 y.1 - N t t x.1 y.1 = _
      rw [hT t x.1 y.1 (hF x.1 x.2) (hF y.1 y.2)]
    · intro R hR
      refine psd_pull f (fun x y => ?_) (g6 R hR)
      show B x.1 y.1 - ∑ t ∈ R, Th t x.1 y.1 = _
      rw [Finset.sum_congr rfl fun t _ => hT t x.1 y.1 (hF x.1 x.2) (hF y.1 y.2)]
  refine ⟨Th, part1, hz, ?_⟩
  intro t F
  have hA : ∀ h ∈ F.filter (· ∈ A), h ∈ A := fun h hh => (Finset.mem_filter.1 hh).2
  have hd : TB.PSDOn (F.filter (· ∈ A)) (Th t) := (part1 _ hA).2.2.2.1 t
  obtain ⟨q1, q2⟩ := (tb_iff_ta _ _).1 hd
  rw [tb_iff_ta]
  refine ⟨?_, ?_⟩
  · intro x hx y hy
    by_cases h : x ∈ A ∧ y ∈ A
    · exact q1 x (Finset.mem_filter.2 ⟨hx, h.1⟩) y (Finset.mem_filter.2 ⟨hy, h.2⟩)
    · rw [hz t x y h, hz t y x (fun h' => h ⟨h'.2, h'.1⟩), map_zero]
  · intro a
    have inner : ∀ x, ∑ y ∈ F.filter (· ∈ A), conj (a x) * Th t x y * a y =
        ∑ y ∈ F, conj (a x) * Th t x y * a y := fun x =>
      Finset.sum_filter_of_ne (fun y _ hne => by
        by_contra hy
        exact hne (by rw [hz t x y (fun h => hy h.2)]; simp))
    have outer : ∑ x ∈ F.filter (· ∈ A), ∑ y ∈ F, conj (a x) * Th t x y * a y =
        ∑ x ∈ F, ∑ y ∈ F, conj (a x) * Th t x y * a y :=
      Finset.sum_filter_of_ne (fun x _ hne => by
        by_contra hx
        exact hne (Finset.sum_eq_zero fun y _ => by rw [hz t x y (fun h => hx h.1)]; simp))
    have := q2 a
    simp only [inner] at this
    rw [outer] at this
    exact this
end Formalism.FourierDecayAlt.P.Jx8
