-- Prove2me | solution 1 for FamousTheorems.vitali_convergence
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T18:25:47.042003+00:00
-- url     : https://prove2.me/submissions/29b21909-d018-4d9d-a859-10fc895b27fe

import Mathlib

theorem solution {α β : Type*} {m : MeasurableSpace α} [NormedAddCommGroup β] {μ : MeasureTheory.Measure α} {p : ENNReal}
    {f : ℕ → α → β} {g : α → β} (hp : 1 ≤ p) (hp' : p ≠ ⊤) (hf : ∀ n, MeasureTheory.MemLp (f n) p μ)
    (hg : MeasureTheory.MemLp g p μ) :
    MeasureTheory.TendstoInMeasure μ f Filter.atTop g ∧ MeasureTheory.UnifIntegrable f p μ ∧
        MeasureTheory.UnifTight f p μ ↔
      Filter.Tendsto (fun n => MeasureTheory.eLpNorm (f n - g) p μ) Filter.atTop (nhds 0) :=
  MeasureTheory.tendstoInMeasure_iff_tendsto_Lp hp hp' hf hg
