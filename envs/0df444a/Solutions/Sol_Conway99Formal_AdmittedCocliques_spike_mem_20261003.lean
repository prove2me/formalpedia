-- Prove2me | solution 1 for Conway99Formal.AdmittedCocliques.spike_mem_20261003
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T00:39:07.817656+00:00
-- url     : https://prove2.me/submissions/eebec0ef-5715-4190-8b27-eba10367e33d

import Definitions.Def_Conway99_Admitted_Cocliques_20261003

set_option autoImplicit false

namespace Conway99Formal.AdmittedCocliques

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [AddCommGroup E] [Module ℝ E]

theorem third_mem_of_seven_thirds_mem (L : AddSubgroup E) {d : E}
    (hd : d ∈ L) (hseven : (7 : ℝ) • ((1 / 3 : ℝ) • d) ∈ L) :
    (1 / 3 : ℝ) • d ∈ L := by
  have htwo : (2 : ℝ) • d ∈ L := by
    have heq : (2 : ℝ) • d = d + d := by module
    rw [heq]
    exact L.add_mem hd hd
  have h := L.sub_mem hseven htwo
  convert h using 1 <;> module

theorem cocliqueVector_seven (point : V → E) (C : Finset V) :
    (7 : ℝ) • cocliqueVector point C = ∑ u ∈ C, point u := by
  simp [cocliqueVector, smul_smul]

end Conway99Formal.AdmittedCocliques

open Conway99Formal.AdmittedCocliques

theorem solution {V E : Type*} [Fintype V] [DecidableEq V]
    [AddCommGroup E] [Module ℝ E]
    (L : AddSubgroup E) (point : V → E)
    (hpoint : ∀ p, point p ∈ L)
    (hdiff : ∀ p q, (1 / 3 : ℝ) • (point p - point q) ∈ L)
    (C : Finset V) (hcard : C.card = 22) (hC : Admitted L point C) (p : V) :
    spikeVector point C p ∈ L := by
  let z := cocliqueVector point C
  let d := point p - z
  have hd : d ∈ L := L.sub_mem (hpoint p) hC
  have hsum : (∑ q ∈ C, (1 / 3 : ℝ) • (point p - point q)) ∈ L := by
    exact L.sum_mem (fun q hq => hdiff p q)
  have hfive : (5 : ℝ) • point p ∈ L := by
    have heq : (5 : ℝ) • point p =
        point p + point p + point p + point p + point p := by module
    rw [heq]
    exact L.add_mem (L.add_mem (L.add_mem (L.add_mem (hpoint p) (hpoint p))
      (hpoint p)) (hpoint p)) (hpoint p)
  have hseven : (7 : ℝ) • ((1 / 3 : ℝ) • d) ∈ L := by
    have heq : (7 : ℝ) • ((1 / 3 : ℝ) • d) =
        (∑ q ∈ C, (1 / 3 : ℝ) • (point p - point q)) - (5 : ℝ) • point p := by
      have hz : (7 : ℝ) • z = ∑ q ∈ C, point q := cocliqueVector_seven point C
      have hconstant : (∑ q ∈ C, point p) = (22 : ℝ) • point p := by
        calc
          (∑ q ∈ C, point p) = (C.card : ℕ) • point p := by simp
          _ = (22 : ℕ) • point p := by rw [hcard]
          _ = (22 : ℝ) • point p :=
            (Nat.cast_smul_eq_nsmul (R := ℝ) 22 (point p)).symm
      have hrewrite : (∑ q ∈ C, (1 / 3 : ℝ) • (point p - point q)) =
          (1 / 3 : ℝ) • ((22 : ℝ) • point p - (7 : ℝ) • z) := by
        rw [← Finset.smul_sum, Finset.sum_sub_distrib, hconstant, ← hz]
      rw [hrewrite]
      dsimp [d, z]
      module
    rw [heq]
    exact L.sub_mem hsum hfive
  exact third_mem_of_seven_thirds_mem L hd hseven

#print axioms solution
