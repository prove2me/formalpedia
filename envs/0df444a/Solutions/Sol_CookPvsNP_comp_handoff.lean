-- Prove2me | solution 1 for CookPvsNP.comp_handoff
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T09:08:40.989359+00:00
-- url     : https://prove2.me/submissions/e258321c-722c-4e72-b665-2ba21319ba10

import Theorems.Thm_CookPvsNP_comp_conversion
import Theorems.Thm_CookPvsNP_comp_output_form

set_option autoImplicit false
open CookPvsNP

/-- A halted ordinary output becomes the exact initial input of the second simulation. -/
theorem solution {S A B : Type} [Fintype A] [Fintype B]
    (j₁ : S ↪ A) (j₂ : S ↪ B) (M₁ : TM A) (M₂ : TM B)
    (c : Cfg A M₁.Q) (w : List S) (hn : M₁.IsHalting c)
    (hout : M₁.output c = w.map (some ∘ j₁)) :
    ∃ d : CompSecondFrame A B M₂.Q,
      (compTM j₁ j₂ M₁ M₂).run (2 * c.right.length + 6) (compFirstCfg c) = d.encode ∧
      d.source = M₂.init (w.map j₂) ∧ d.right.length ≤ c.right.length := by
  obtain ⟨n, h⟩ := comp_output_form j₁ M₁ c w hout
  refine ⟨compConvertedFrame j₁ j₂ M₂.q₀ c.left w n, ?_, ?_, ?_⟩
  · have hc := comp_conversion j₁ j₂ M₁ M₂ c.state c.left w n hn
    simpa only [← h] using hc
  · cases w <;> simp [compConvertedFrame, CompSecondFrame.source, TM.init,
      List.map_map, Function.comp_def]
  · have hr := congrArg (fun c : Cfg A M₁.Q => c.right.length) h
    simp only [compWordCfg, List.length_append, List.length_tail, List.length_map,
      List.length_replicate] at hr
    simp only [compConvertedFrame, List.length_tail, List.length_map]
    omega

#print axioms solution
