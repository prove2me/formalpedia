-- Prove2me | solution 1 for BasisWeightLearning.Exact.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:43:50.479485+00:00
-- url     : https://prove2.me/submissions/df3b3eed-cc24-4c28-85b8-b7d8d9ffbeaf

import Definitions.Def_BasisWeightLearning_Exact_PolynomialWeights

open BasisWeightLearning.Exact in
theorem solution (a b : BasisWeightLearning.Exact.Weight) :
    BasisWeightLearning.Exact.evaluate a + BasisWeightLearning.Exact.evaluate b =
      BasisWeightLearning.Exact.evaluate (a + b) ∧
    BasisWeightLearning.Exact.evaluate a * BasisWeightLearning.Exact.evaluate b =
      BasisWeightLearning.Exact.evaluate (a * b) := by
  constructor <;> funext θ <;> simp [BasisWeightLearning.Exact.evaluate]
