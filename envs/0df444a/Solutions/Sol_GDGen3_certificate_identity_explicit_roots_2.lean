-- Prove2me | solution 2 for GDGen3.certificate_identity_explicit_roots
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:26:39.205176+00:00
-- url     : https://prove2.me/submissions/f1be20b6-cd26-4059-9b00-cc279b776b91

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase
import Theorems.Thm_GDGen3_certificate_identity_general
import Theorems.Thm_GDGen3_rootXi_zero
import Theorems.Thm_GDGen3_rootXi_pos
import Theorems.Thm_GDGen3_rootXi_quad
import Theorems.Thm_GDGen3_rootXi_quad7
import Theorems.Thm_GDGen3_rootXi_pin

noncomputable section

open Finset

open GDGen3

theorem solution
    (r : ℝ) (N : ℕ) (hN : 1 ≤ N) (hr : 0 < r) (hr1 : r < 1)
    (f : ℕ → ℝ) (P : ℕ → ℕ → ℝ) (R : ℕ → ℝ) (X0 : ℝ)
    (hP : ∀ i j, P i j = P j i) :
    certSum r N (rootXi r N) f P R = certRhs r N P R X0 := by
  exact certificate_identity_general r N hN (rootXi r N) hr hr1
    (fun i hi => rootXi_pos r hr hr1 N i hi) (rootXi_zero r N)
    (fun i hi => rootXi_quad r hr hr1 N i hi)
    (fun i hi => rootXi_quad7 r hr hr1 N i hi) (rootXi_pin r hr hr1 N hN) f P R X0 hP
