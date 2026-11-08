-- Prove2me | solution 1 for CompOT.SinkhornConv.hilbertDist_div_inv_identity
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:34:33.943995+00:00
-- url     : https://prove2.me/submissions/dba55af5-b7b6-4d1f-af8a-351e2ad1e152

import Mathlib
import Definitions.Def_CompOT_SinkhornConv_hilbertDist

open Matrix

open CompOT.SinkhornConv in
theorem solution {m : ℕ} (v v' : Fin m → ℝ)
    (hv : ∀ k, 0 < v k) (hv' : ∀ k, 0 < v' k) :
    hilbertDist v v' = hilbertDist (v / v') 1 ∧
      hilbertDist (v / v') 1 = hilbertDist (1 / v) (1 / v') := by
  have e1 : ∀ i j, (v / v') i * (1 : Fin m → ℝ) j / ((v / v') j * (1 : Fin m → ℝ) i)
      = v i * v' j / (v j * v' i) := by
    intro i j
    simp only [Pi.div_apply, Pi.one_apply, mul_one]
    rw [div_div_div_eq, mul_comm (v' i) (v j)]
  have e2 : ∀ i j, (1 / v) i * (1 / v') j / ((1 / v) j * (1 / v') i)
      = v j * v' i / (v i * v' j) := by
    intro i j
    simp only [Pi.div_apply, Pi.one_apply]
    rw [one_div_mul_one_div, one_div_mul_one_div, div_div_div_eq, one_mul, mul_one]
  constructor
  · unfold hilbertDist
    congr 1
    exact iSup_congr fun i => iSup_congr fun j => (e1 i j).symm
  · unfold hilbertDist
    congr 1
    let T : Fin m → Fin m → ℝ := fun i j => v i * v' j / (v j * v' i)
    calc (⨆ i, ⨆ j, (v / v') i * (1 : Fin m → ℝ) j / ((v / v') j * (1 : Fin m → ℝ) i))
        = ⨆ i, ⨆ j, T i j := iSup_congr fun i => iSup_congr fun j => e1 i j
      _ = ⨆ q : Fin m × Fin m, T q.1 q.2 :=
          (Finite.ciSup_prod (fun q : Fin m × Fin m => T q.1 q.2)).symm
      _ = ⨆ q : Fin m × Fin m, T q.2 q.1 :=
          ((Equiv.prodComm (Fin m) (Fin m)).iSup_comp (g := fun q : Fin m × Fin m => T q.1 q.2)).symm
      _ = ⨆ i, ⨆ j, T j i := Finite.ciSup_prod (fun q : Fin m × Fin m => T q.2 q.1)
      _ = ⨆ i, ⨆ j, (1 / v) i * (1 / v') j / ((1 / v) j * (1 / v') i) :=
          iSup_congr fun i => iSup_congr fun j => (e2 i j).symm
