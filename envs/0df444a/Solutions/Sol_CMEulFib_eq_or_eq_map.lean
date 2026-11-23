-- Prove2me | solution 1 for CMEulFib.eq_or_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:36:46.252089+00:00
-- url     : https://prove2.me/submissions/93a203ca-0d38-48ad-b5a0-fdd6fa677b88

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMEulerProducts_StepRegroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMDegreeEquality_FinrankEqTwo
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMEulerProducts_FibreShapeOf
import Theorems.Thm_CMEulFib_mem_map_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open CMEulFib
open Formalism.L2.SG.MassRatio Formalism.HermitianLatticesTheory
namespace CMEulFib
theorem _root_.solution {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (σ : B ≃+* B)
    (hinv : ∀ x, σ (σ x) = x) (hfix : ∀ x : B, σ x = x → x ∈ Set.range (algebraMap A B))
    (P Q : Ideal B) [hP : P.IsMaximal] [hQ : Q.IsMaximal]
    (hPQ : Q.comap (algebraMap A B) = P.comap (algebraMap A B)) :
    Q = P ∨ Q = P.map σ := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  have hσP : (P.map σ).IsMaximal := Ideal.map_isMaximal_of_equiv σ
  have ha : ¬ Q ≤ P := fun hle => h1 (hQ.eq_of_le hP.ne_top hle)
  have hb : ¬ Q ≤ P.map σ := fun hle => h2 (hQ.eq_of_le hσP.ne_top hle)
  obtain ⟨a, haQ, haP⟩ := SetLike.not_le_iff_exists.mp ha
  obtain ⟨b, hbQ, hbP⟩ := SetLike.not_le_iff_exists.mp hb
  obtain ⟨x, hxQ, hxP, hxσ⟩ : ∃ x ∈ Q, x ∉ P ∧ x ∉ P.map σ := by
    by_cases h3 : a ∈ P.map σ
    · by_cases h4 : b ∈ P
      · refine ⟨a + b, Q.add_mem haQ hbQ, fun h => haP ?_, fun h => hbP ?_⟩
        · simpa using P.sub_mem h h4
        · simpa using (P.map σ).sub_mem h h3
      · exact ⟨b, hbQ, h4, hbP⟩
    · exact ⟨a, haQ, haP, h3⟩
  have hfx : σ (x * σ x) = x * σ x := by rw [map_mul, hinv, mul_comm]
  obtain ⟨y, hy⟩ := hfix _ hfx
  have hyQ : y ∈ Q.comap (algebraMap A B) := by
    rw [Ideal.mem_comap, hy]
    exact Q.mul_mem_right _ hxQ
  rw [hPQ, Ideal.mem_comap, hy] at hyQ
  rcases hP.isPrime.mem_or_mem hyQ with h5 | h5
  · exact hxP h5
  · exact hxσ ((mem_map_iff σ hinv P x).mpr h5)
end CMEulFib
