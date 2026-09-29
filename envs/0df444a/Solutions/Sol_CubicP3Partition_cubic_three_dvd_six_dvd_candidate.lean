-- Prove2me | solution 1 for CubicP3Partition.cubic_three_dvd_six_dvd_candidate
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T00:46:35.777531+00:00
-- url     : https://prove2.me/submissions/69bd27d1-b421-4490-b6c9-2c64f4e636c6

import Definitions.Def_cubic_p3_partition_models

namespace CubicP3Partition

universe u

noncomputable section


end
end CubicP3Partition

open CubicP3Partition
universe u
theorem solution
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V}
    (hCubic : Cubic G) (hThree : 3 ∣ Fintype.card V) :
    6 ∣ Fintype.card V := by
  classical
  have hdegree : ∀ v : V, G.degree v = 3 := by
    intro v
    rw [← SimpleGraph.card_neighborSet_eq_degree]
    let e : {w : V // G.Adj v w} ≃ G.neighborSet v :=
      { toFun := fun w => ⟨w.1, w.2⟩
        invFun := fun w => ⟨w.1, w.2⟩
        left_inv := by intro w; rfl
        right_inv := by intro w; rfl }
    have hc := Fintype.card_congr e
    have hcubicv : Fintype.card {w : V // G.Adj v w} = 3 := by
      simpa only [degree, Nat.card_eq_fintype_card] using hCubic v
    exact hc.symm.trans hcubicv
  have hsum := G.sum_degrees_eq_twice_card_edges
  have hdeg : (∑ v : V, G.degree v) = 3 * Fintype.card V := by
    simp_rw [hdegree]
    simp [Nat.mul_comm]
  have heq : 3 * Fintype.card V = 2 * G.edgeFinset.card := hdeg.symm.trans hsum
  have hmod : Fintype.card V % 2 = 0 := by omega
  have hEven : 2 ∣ Fintype.card V := Nat.dvd_of_mod_eq_zero hmod
  have hcop : Nat.Coprime 2 3 := by decide
  have hsix : 2 * 3 ∣ Fintype.card V :=
    hcop.mul_dvd_of_dvd_of_dvd hEven hThree
  simpa using hsix

