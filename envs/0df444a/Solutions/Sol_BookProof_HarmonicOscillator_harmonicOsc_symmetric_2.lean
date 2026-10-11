-- Prove2me | solution 2 for BookProof.HarmonicOscillator.harmonicOsc_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T09:07:07.661774+00:00
-- url     : https://prove2.me/submissions/aa45a843-eb88-4791-87dd-3a082a562e51

-- Generated from ChapterHarmonicOscillatorEsa.lean — theorem BookProof.HarmonicOscillator.harmonicOsc_symmetric
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterStrichartzHermiteQG
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterHarmonicOscillatorEsa
import Definitions.Def_ChapterFarisLavineCore
open BookProof.HarmonicOscillator



open MeasureTheory Polynomial BookProof.HermiteCore BookProof.HermiteStrichartzQG
open BookProof.FarisLavine
open BookProof.HarmonicOscillator

theorem solution: SymmetricOn hermiteCore harmonicOscOp := by
  intro x y
  simp only [harmonicOscOp, hermiteCoreOp, hermiteDiagOp, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv]
  rw [← LinearIsometryEquiv.inner_map_map hermiteRepr, LinearIsometryEquiv.apply_symm_apply]
  rw [← LinearIsometryEquiv.inner_map_map hermiteRepr (x : L2R), LinearIsometryEquiv.apply_symm_apply]
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  congr 1
  funext n
  simp [mulHamiltonian, mulSymbolOp, mulSymbolFun, hermiteDiagRestrict]
  ring
