-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.paired_streams
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:02:22.082367+00:00
-- url     : https://prove2.me/submissions/e9068908-8374-41db-96d6-aab50c38b206

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

theorem solution (μ ν : Measure Bool) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    let μs := Measure.infinitePi fun _ : ℕ => μ
    let νs := Measure.infinitePi fun _ : ℕ => ν
    (μs.prod νs).map (fun p n => (p.1 n, p.2 n)) =
      Measure.infinitePi (fun _ : ℕ => μ.prod ν) := by
  classical
  dsimp only
  let μs := Measure.infinitePi fun _ : ℕ => μ
  let νs := Measure.infinitePi fun _ : ℕ => ν
  let pair : ((ℕ → Bool) × (ℕ → Bool)) → (ℕ → Bool × Bool) := fun p n => (p.1 n, p.2 n)
  have hpair : Measurable pair := by fun_prop
  change (μs.prod νs).map pair = _
  apply Measure.eq_infinitePi
  intro s t ht
  have hm : MeasurableSet (Set.pi (↑s : Set ℕ) t) := MeasurableSet.pi s.countable_toSet (fun i _ => ht i)
  rw [Measure.map_apply hpair hm]
  let e := MeasurableEquiv.arrowProdEquivProdArrow Bool Bool s
  let r : ((ℕ → Bool) × (ℕ → Bool)) → ((s → Bool) × (s → Bool)) := fun p => (s.restrict p.1, s.restrict p.2)
  have hr : Measurable r := by fun_prop
  have hmapr : (μs.prod νs).map r = (Measure.pi (fun _ : s => μ)).prod (Measure.pi (fun _ : s => ν)) := by
    change (μs.prod νs).map (Prod.map s.restrict s.restrict) = _
    rw [← Measure.map_prod_map μs νs (by fun_prop) (by fun_prop)]
    rw [Measure.infinitePi_map_restrict, Measure.infinitePi_map_restrict]
  have he : (Measure.pi (fun _ : s => μ.prod ν)).map e =
      (Measure.pi (fun _ : s => μ)).prod (Measure.pi (fun _ : s => ν)) :=
    (measurePreserving_arrowProdEquivProdArrow Bool Bool s (fun _ => μ) (fun _ => ν)).map_eq
  have he' : ((Measure.pi (fun _ : s => μ)).prod (Measure.pi (fun _ : s => ν))).map e.symm = Measure.pi (fun _ : s => μ.prod ν) := by
    rw [← he, Measure.map_map e.symm.measurable e.measurable]
    simp
  let u : Set (s → Bool × Bool) := Set.univ.pi (fun i => t i.val)
  have hu : MeasurableSet u := MeasurableSet.univ_pi (fun i => ht i.val)
  have heq : pair ⁻¹' Set.pi (↑s : Set ℕ) t = (e.symm ∘ r) ⁻¹' u := by
    ext p
    simp [pair, e, r, u, Set.mem_pi, MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow]
  rw [heq, ← Measure.map_apply (e.symm.measurable.comp hr) hu, ← Measure.map_map e.symm.measurable hr, hmapr, he', Measure.pi_pi]
  simpa using (Finset.prod_attach s (fun i => (μ.prod ν) (t i)))
