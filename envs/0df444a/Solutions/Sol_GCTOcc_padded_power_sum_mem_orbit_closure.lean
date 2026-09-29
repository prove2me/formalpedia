-- Prove2me | solution 1 for GCTOcc.padded_power_sum_mem_orbit_closure
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T06:24:13.554354+00:00
-- url     : https://prove2.me/submissions/c236e317-0ffd-4739-9e2b-33784e73f57d

import Mathlib
import Definitions.Def_GCTOcc_occurrence

/-! Disproof of 04d2b62a `GCTOcc.padded_power_sum_mem_orbit_closure`.

At `n = 0` the hypotheses `1 ≤ k`, `s * k ≤ n` allow `s = 0` with any `k ≥ 1`. Then every factor is a
zeroth power, so the polynomial is the constant `k`. But `detPoly 0 = 1` (the empty determinant),
substitution fixes `1`, so the orbit closure of `detPoly 0` is `{1}`. For `k = 2` the constant `2` is
not in it: its constant coefficient would have to be a limit of the constant sequence `1`. -/

set_option autoImplicit false

open MvPolynomial Filter

theorem dpGCT_04d2_det0 : GCTOcc.detPoly 0 = 1 := by
  simp [GCTOcc.detPoly]

theorem dpGCT_04d2_subst0 (g : Matrix (Fin 0 × Fin 0) (Fin 0 × Fin 0) ℂ) :
    GCTOcc.substLin 0 g (GCTOcc.detPoly 0) = 1 := by
  rw [dpGCT_04d2_det0]
  simp [GCTOcc.substLin]

open GCTOcc in
theorem solution : ¬ (∀ (n s k : ℕ) (hk : 1 ≤ k) (hsk : s * k ≤ n)
    (a : Fin n × Fin n → ℂ) (phi : Fin k → Fin n × Fin n → ℂ),
    (linForm n a) ^ (n - s) * (∑ i : Fin k, (linForm n (phi i)) ^ s)
      ∈ orbitClosure n (detPoly n)) := by
  intro H
  have h := H 0 0 2 (by norm_num) (by norm_num) (fun _ => 0) (fun _ _ => 0)
  obtain ⟨g, -, hlim⟩ := h
  have h0 := hlim 0
  simp only [dpGCT_04d2_subst0] at h0
  have hc := tendsto_nhds_unique tendsto_const_nhds h0
  simp at hc
  have h2 : (2 : MvPolynomial ((ℕ × ℕ)) ℂ) = C 2 := (map_ofNat C 2).symm
  rw [h2, coeff_zero_C] at hc
  norm_num at hc
