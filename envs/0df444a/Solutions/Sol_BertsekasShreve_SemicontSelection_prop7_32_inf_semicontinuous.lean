-- Prove2me | solution 1 for BertsekasShreve.SemicontSelection.prop7_32_inf_semicontinuous
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T14:37:13.837384+00:00
-- url     : https://prove2.me/submissions/edf9bd99-a056-4777-bdbd-757e66575bda

import Mathlib

set_option autoImplicit false

open TopologicalSpace in
theorem solution {X Y : Type*}
    [TopologicalSpace X] [MetrizableSpace X] [TopologicalSpace Y] [MetrizableSpace Y]
    (f : X × Y → EReal) :
    (LowerSemicontinuous f → CompactSpace Y →
      LowerSemicontinuous (fun x => ⨅ y, f (x, y)) ∧
      ∀ x, Nonempty Y → ∃ y, f (x, y) = ⨅ y', f (x, y')) ∧
    (UpperSemicontinuous f → UpperSemicontinuous (fun x => ⨅ y, f (x, y))) := by
  refine ⟨fun hf hY => ⟨?_, ?_⟩, fun hf => ?_⟩
  · intro x₀ c hc
    obtain ⟨c', hcc', hc'⟩ := exists_between hc
    have hP : ∀ y ∈ (Set.univ : Set Y),
        ∀ᶠ z : X × Y in nhds (x₀, y), c' < f (z.1, z.2) := by
      intro y _
      have h1 : c' < f (x₀, y) := lt_of_lt_of_le hc' (iInf_le _ y)
      simpa using hf (x₀, y) c' h1
    have := IsCompact.eventually_forall_of_forall_eventually (x₀ := x₀)
      (P := fun x y => c' < f (x, y)) isCompact_univ hP
    filter_upwards [this] with x hx
    exact lt_of_lt_of_le hcc' (le_iInf fun y => (hx y (Set.mem_univ y)).le)
  · intro x hne
    have hcont : Continuous (fun y : Y => (x, y)) := Continuous.prodMk_right x
    have hl : LowerSemicontinuous (fun y : Y => f (x, y)) := hf.comp hcont
    obtain ⟨a, -, ha⟩ := (hl.lowerSemicontinuousOn Set.univ).exists_isMinOn
      Set.univ_nonempty isCompact_univ
    refine ⟨a, le_antisymm (le_iInf fun y => ha (Set.mem_univ y)) (iInf_le _ a)⟩
  · apply upperSemicontinuous_iInf
    intro y
    exact hf.comp (Continuous.prodMk_left y)
