-- Prove2me | solution 1 for CauchyRiemannIndex.eq_of_continuous_periodic_ae_eq
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-09T16:39:25.529865+00:00
-- url     : https://prove2.me/submissions/24a66e36-ff5b-47ac-af44-689da09e24b6

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order



namespace CauchyRiemannIndex

open MeasureTheory Filter Topology Set
open scoped ENNReal

/-- Two continuous maps on `ℝ × ℝ`, `1`-periodic in `t`, that agree `cylMeasure`-a.e. are equal. -/
theorem eq_of_continuous_periodic_ae_eq {E : Type*} [TopologicalSpace E] [T2Space E]
    {g h : ℝ × ℝ → E} (hg : Continuous g) (hh : Continuous h)
    (hgp : ∀ s t, g (s, t + 1) = g (s, t)) (hhp : ∀ s t, h (s, t + 1) = h (s, t))
    (hae : g =ᵐ[cylMeasure] h) : g = h := by
  set U : Set (ℝ × ℝ) := {x | g x ≠ h x} ∩ (univ ×ˢ Ioo (0 : ℝ) 1) with hU
  have hUo : IsOpen U :=
    (isOpen_ne_fun hg hh).inter (isOpen_univ.prod isOpen_Ioo)
  have hU0 : volume U = 0 := by
    have h1 : cylMeasure {x | g x ≠ h x} = 0 := hae
    have h2 : volume ({x | g x ≠ h x} ∩ (univ ×ˢ Ico (0 : ℝ) 1)) = 0 :=
      le_antisymm ((Measure.le_restrict_apply _ _).trans_eq h1) (zero_le)
    exact measure_mono_null (inter_subset_inter_right _ (prod_mono subset_rfl Ioo_subset_Ico_self)) h2
  have hUe : U = ∅ := (hUo.measure_eq_zero_iff volume).1 hU0
  have hon : ∀ s, ∀ t ∈ Ioo (0 : ℝ) 1, g (s, t) = h (s, t) := by
    intro s t ht
    by_contra hne
    have : (s, t) ∈ U := ⟨hne, mem_univ _, ht⟩
    rw [hUe] at this; exact this
  funext x
  obtain ⟨s, t⟩ := x
  have hIcc : EqOn (fun t => g (s, t)) (fun t => h (s, t)) (Icc (0 : ℝ) 1) := by
    rw [← closure_Ioo zero_ne_one]
    exact EqOn.closure (fun t ht => hon s t ht) (hg.comp (Continuous.prodMk_right s))
      (hh.comp (Continuous.prodMk_right s))
  have pg : Function.Periodic (fun t => g (s, t)) 1 := fun t => hgp s t
  have ph : Function.Periodic (fun t => h (s, t)) 1 := fun t => hhp s t
  have eg := pg.sub_int_mul_eq (x := t) ⌊t⌋
  have eh := ph.sub_int_mul_eq (x := t) ⌊t⌋
  rw [mul_one] at eg eh
  rw [← eg, ← eh]
  exact hIcc ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩

end CauchyRiemannIndex

open CauchyRiemannIndex

open MeasureTheory

theorem solution {E : Type*} [TopologicalSpace E] [T2Space E]
    {g h : ℝ × ℝ → E} (hg : Continuous g) (hh : Continuous h)
    (hgp : ∀ s t, g (s, t + 1) = g (s, t)) (hhp : ∀ s t, h (s, t + 1) = h (s, t))
    (hae : g =ᵐ[cylMeasure] h) : g = h :=
  eq_of_continuous_periodic_ae_eq hg hh hgp hhp hae
