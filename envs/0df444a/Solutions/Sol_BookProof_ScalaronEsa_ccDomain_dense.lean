-- Prove2me | solution 1 for BookProof.ScalaronEsa.ccDomain_dense
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T09:45:21.334411+00:00
-- url     : https://prove2.me/submissions/a9fc92d0-7e2d-450a-92c8-df95d5cfc541

-- Generated from ChapterScalaronCoreEsa.lean — solution of BookProof.ScalaronEsa.ccDomain_dense
import Mathlib
import Definitions.Def_ChapterScalaronCoreEsa
import Theorems.Thm_BookProof_ScalaronEsa_ccInclLM_apply
open BookProof.ScalaronEsa



open Filter Topology MeasureTheory SchwartzMap


open BookProof.StrichartzWave BookProof.FarisLavine BookProof.Starobinsky
open BookProof.QuantumGravityDensitized BookProof.StoneBridge BookProof.NavierStokesFlow
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

set_option maxHeartbeats 1000000 in
theorem solution : Dense ((ccDomain E : Submodule ℂ (Lp ℂ 2 (volume : Measure E))) :
    Set (Lp ℂ 2 (volume : Measure E))) := by

  have hd : Dense {f : Lp ℂ 2 (volume : Measure E) | ∃ g, (f : E → ℂ) =ᵐ[volume] g ∧
      HasCompactSupport g ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g} :=
    MeasureTheory.Lp.dense_hasCompactSupport_contDiff (by norm_num)
  refine Dense.mono ?_ hd
  rintro f ⟨g, hfg, hgc, hgs⟩
  refine ⟨⟨hgc.toSchwartzMap hgs, hgc⟩, ?_⟩
  rw [ccInclLM_apply]
  refine MeasureTheory.Lp.ext ?_
  filter_upwards [(hgc.toSchwartzMap hgs).coeFn_toLp 2 (volume : Measure E), hfg]
    with x hx hy
  rw [hx, hy]
  rfl
