-- Prove2me | solution 2 for DiazModulus.candidate_one_self_conj_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T10:17:49.02172+00:00
-- url     : https://prove2.me/submissions/6a11752a-3f19-4aff-b256-2ed5444d68ec

import Definitions.Def_DiazModulus
import Definitions.Def_Diaz_Instantiation
import Theorems.Thm_DiazModulus_hermite_lindemann_holds
import Theorems.Thm_DiazModulus_diaz_locus_dictionary
import Theorems.Thm_Diaz_indep_three

open Complex ComplexConjugate

/-- The `Q̄`-action on `ℂ` is multiplication by the underlying complex number. -/
private theorem dzb_qbar_smul (a : ↥DiazModulus.Qbar) (z : ℂ) : a • z = (a : ℂ) * z := rfl

open DiazModulus in
theorem solution {u : ℂ} (h : IsCandidate u) :
    LinearIndependent (↥Qbar) ![(1 : ℂ), u, conj u] := by
  obtain ⟨hu0, hexp, hrho⟩ := (diaz_locus_dictionary.2 u).1 h
  have hQ : u * conj u ∈ Qbar := mem_Qbar_iff.mpr hrho
  have hQtr : Transcendental ℚ u := fun hal => hermite_lindemann_holds u hu0 hal hexp
  have : Algebra.IsAlgebraic ℚ (↥Qbar) := diaz_locus_dictionary.1 ▸ Diaz.QbarIsAlgebraic
  have hT : Transcendental (↥Qbar) u :=
    (Algebra.IsAlgebraic.transcendental_iff ℚ (↥Qbar)).mp hQtr
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hrel : (g 0 : ℂ) + (g 1 : ℂ) * u + (g 2 : ℂ) * conj u = 0 := by
    rw [Fin.sum_univ_three] at hg
    simpa [dzb_qbar_smul] using hg
  obtain ⟨hA, hB, hC⟩ :=
    Diaz.indep_three (K := Qbar) hT hQ (g 0).2 (g 1).2 (g 2).2 hrel
  fin_cases i
  · exact ZeroMemClass.coe_eq_zero.mp hA
  · exact ZeroMemClass.coe_eq_zero.mp hB
  · exact ZeroMemClass.coe_eq_zero.mp hC
