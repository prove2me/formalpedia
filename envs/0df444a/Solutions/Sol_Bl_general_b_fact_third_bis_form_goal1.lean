-- Prove2me | solution 1 for Bl.general_b_fact_third_bis_form.goal1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:41:24.205567+00:00
-- url     : https://prove2.me/submissions/4a595771-604c-4af5-b731-70bdc81096a0

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactThirdBisForm_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_third_bis_form
namespace Bl.general_b_fact_third_bis_form
theorem _root_.solution :
  ∀ {ι P β : Type} [inst : Fintype.{0} ι] [inst_1 : Fintype.{0} P] [inst_2 : MeasurableSpace.{0} β]
  (μ0 : MeasureTheory.Measure.{0} β) [MeasureTheory.SigmaFinite.{0} μ0],
  MeasureTheory.MeasurePreserving.{0, 0} (fun (x : ι → P → β) (p : P) (v : ι) ↦ x v p)
    (MeasureTheory.Measure.pi.{0, 0} fun (x : ι) ↦ MeasureTheory.Measure.pi.{0, 0} fun (x : P) ↦ μ0)
    (MeasureTheory.Measure.pi.{0, 0} fun (x : P) ↦ MeasureTheory.Measure.pi.{0, 0} fun (x : ι) ↦ μ0) := by
  intro ι P β _ _ _ μ0 _
  have hf : Measurable (fun (x : ι → P → β) (p : P) (v : ι) ↦ x v p) := by
    refine measurable_pi_iff.mpr fun p => measurable_pi_iff.mpr fun v => ?_
    exact (measurable_pi_apply p).comp (measurable_pi_apply v)
  refine ⟨hf, ?_⟩
  refine (MeasureTheory.Measure.pi_eq_generateFrom
    (C := fun _ => Set.pi Set.univ '' Set.pi Set.univ fun _ => {s : Set β | MeasurableSet s})
    (fun _ => generateFrom_pi) (fun _ => isPiSystem_pi)
    (fun _ => MeasureTheory.Measure.FiniteSpanningSetsIn.pi fun _ => μ0.toFiniteSpanningSetsIn)
    ?_).symm
  intro s hs
  choose t ht hts using hs
  have hmt : ∀ p v, MeasurableSet (t p v) := fun p v => ht p v (Set.mem_univ v)
  have hs' : s = fun p => Set.pi Set.univ (t p) := funext fun p => (hts p).symm
  subst hs'
  have hpre : (fun (x : ι → P → β) (p : P) (v : ι) ↦ x v p) ⁻¹'
      Set.pi Set.univ (fun p => Set.pi Set.univ (t p)) =
      Set.pi Set.univ (fun v => Set.pi Set.univ (fun p => t p v)) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ_pi]
    exact forall_comm
  have hmeas : MeasurableSet (Set.pi Set.univ (fun p => Set.pi Set.univ (t p))) :=
    MeasurableSet.univ_pi fun p => MeasurableSet.univ_pi fun v => hmt p v
  rw [MeasureTheory.Measure.map_apply hf hmeas, hpre, MeasureTheory.Measure.pi_pi]
  simp only [MeasureTheory.Measure.pi_pi]
  exact Finset.prod_comm
end Bl.general_b_fact_third_bis_form
