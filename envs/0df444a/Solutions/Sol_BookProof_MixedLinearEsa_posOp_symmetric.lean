-- Prove2me | solution 1 for BookProof.MixedLinearEsa.posOp_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T11:28:33.075499+00:00
-- url     : https://prove2.me/submissions/2526c456-5ec7-4d92-9ab5-3a677b75bf20

-- Generated from ChapterMixedLinearEsa.lean — theorem BookProof.MixedLinearEsa.posOp_symmetric
import Definitions.Def_ChapterFourierMultiplierEsa
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterMixedLinearEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave
open BookProof.MixedLinearEsa



open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv
open BookProof.StrichartzWave BookProof.FourierMultiplierEsa BookProof.FarisLavine

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
open BookProof.MixedLinearEsa

theorem solution(b : V) :
    SymmetricOn (schwartzDomain V) (opL2 (posOp b)) := by
  intro x y
  have hg : (fun z : V => ((inner ℝ z b : ℝ) : ℂ)).HasTemperateGrowth := by fun_prop
  obtain ⟨f, rfl⟩ : ∃ f, (BookProof.StrichartzWave.schwartzEquiv V) f = x :=
    ⟨_, (BookProof.StrichartzWave.schwartzEquiv V).apply_symm_apply x⟩
  obtain ⟨g, rfl⟩ : ∃ g, (BookProof.StrichartzWave.schwartzEquiv V) g = y :=
    ⟨_, (BookProof.StrichartzWave.schwartzEquiv V).apply_symm_apply y⟩
  have hc : ∀ h : 𝓢(V, ℂ), ((BookProof.StrichartzWave.schwartzEquiv V h :
      BookProof.StrichartzWave.schwartzDomain V) : MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure V))
      = SchwartzMap.toLpCLM ℂ ℂ 2 MeasureTheory.volume h := fun h => rfl
  simp only [BookProof.StrichartzWave.opL2, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, ContinuousLinearMap.coe_coe, hc, SchwartzMap.toLpCLM_apply,
    SchwartzMap.inner_toL2_toL2_eq]
  congr 1
  funext z
  simp [posOp, hg, Complex.conj_ofReal]
  ring
