-- Prove2me | solution 1 for FreeEnergyPrinciple.gaussianVariationalFreeEnergy_eq_meanSquare_add_surprisal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T03:16:35.165736+00:00
-- url     : https://prove2.me/submissions/4b5721e5-03b5-4757-ad06-21425066d7e4

import Mathlib
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Definitions.Def_fep2_gaussian_vfe

set_option autoImplicit false

open FreeEnergyPrinciple InformationTheory in
theorem solution
    (model : ScalarGaussianFilterModel) (prior : ScalarGaussianBelief)
    (observation recognitionMean : ℝ) :
    gaussianVariationalFreeEnergy model prior observation recognitionMean =
      (recognitionMean - posteriorMean model prior observation) ^ 2 /
          (2 * (posteriorVariance model prior : ℝ)) +
        evidenceSurprisal model prior observation := by
  unfold gaussianVariationalFreeEnergy
  have hlaw : (posteriorBelief model prior observation).law =
      (posteriorFamily model prior).law (posteriorMean model prior observation) := rfl
  rw [hlaw, FixedVarianceGaussian.klDiv_law_eq_meanSquare, ENNReal.toReal_ofReal (by positivity)]
  rfl
#print axioms solution
