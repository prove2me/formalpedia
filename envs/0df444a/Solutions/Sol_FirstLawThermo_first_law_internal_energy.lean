-- Prove2me | solution 1 for FirstLawThermo.first_law_internal_energy
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-10T13:17:43.681025+00:00
-- url     : https://prove2.me/submissions/af6a14df-5c20-4bdb-8ece-769943d2fac4

import Theorems.Thm_FirstLawThermo_exists_isInternalEnergy
import Theorems.Thm_FirstLawThermo_isInternalEnergy_unique_up_to_const

open FirstLawThermo

theorem solution {σ : Type*} (procs : Set (Process σ)) (O : σ)
    (hcomp : ClosedUnderComp procs) (hnull : ContainsNull procs)
    (hpath : AdiabaticWorkPathIndependent procs) (hlink : AdiabaticallyLinkedTo procs O) :
    (∃ U : σ → ℝ, IsInternalEnergy procs U) ∧
      ∀ U U' : σ → ℝ, IsInternalEnergy procs U → IsInternalEnergy procs U' →
        ∃ c : ℝ, ∀ A : σ, U' A = U A + c := by
  obtain ⟨U, hU, -⟩ := exists_isInternalEnergy procs O hcomp hnull hpath hlink
  exact ⟨⟨U, hU⟩, fun U U' hU hU' =>
    isInternalEnergy_unique_up_to_const procs O hlink U U' hU hU'⟩
