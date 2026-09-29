-- Prove2me | solution 1 for Freiman.form_unimodular_minimum
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:24:30.982974+00:00
-- url     : https://prove2.me/submissions/d1341901-f5ad-4269-8004-d728ffa1ae03

import Definitions.Def_Freiman_reducedForms
import Theorems.Thm_Freiman_form_unimodular_lattice_bijection
import Theorems.Thm_Freiman_form_transform_value

open Freiman

theorem solution (A B C : ℝ) (a b c d : ℤ) (hdet : formUnimodular a b c d) :
    quadraticMinimum (transformedA A B C a b c d) (transformedB A B C a b c d)
      (transformedC A B C a b c d) = quadraticMinimum A B C := by
  unfold quadraticMinimum
  congr 1
  ext v
  constructor
  · rintro ⟨p, q, hpq, hv⟩
    exact ⟨a*p+b*q, c*p+d*q, (form_unimodular_lattice_bijection a b c d hdet).1 p q hpq,
      hv.trans (congrArg abs (form_transform_value A B C a b c d p q))⟩
  · rintro ⟨r, s, hrs, hv⟩
    obtain ⟨p, q, hpq, hr, hs⟩ := (form_unimodular_lattice_bijection a b c d hdet).2 r s hrs
    refine ⟨p, q, hpq, ?_⟩
    rw [form_transform_value, hr, hs]
    exact hv
