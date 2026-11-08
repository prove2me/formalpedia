-- Prove2me | solution 1 for BasisWeightLearning.Exact.corollary_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:07:11.357786+00:00
-- url     : https://prove2.me/submissions/884a973f-65f6-43de-84e6-bf28f825ec6c

import Definitions.Def_BasisWeightLearning_Exact_ExpectedReward
import Definitions.Def_BasisWeightLearning_Exact_PolynomialData

open BasisWeightLearning.Exact in
theorem solution {A S : Type} [Fintype A] [Nonempty A] [Fintype S] [Nonempty S]
    (M : HiddenModel Theta A S) (hM : M.Valid)
    (D : PolynomialData A S) (hA1 : D.Represents M) (a : A) :
    BasisWeightLearning.Exact.expectedReward M a = evaluate (expectedWeight D a) := by
  funext θ
  obtain ⟨hp, hr⟩ := hA1
  simp only [BasisWeightLearning.Exact.expectedReward, expectedWeight, evaluate, Polynomial.eval_finset_sum,
    Polynomial.eval_mul]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  have h1 := congrFun (hp a s) θ
  have h2 := congrFun (hr a s) θ
  simp only [evaluate] at h1 h2
  rw [h1, h2]
