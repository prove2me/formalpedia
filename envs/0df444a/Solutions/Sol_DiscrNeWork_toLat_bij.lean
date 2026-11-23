-- Prove2me | solution 1 for DiscrNeWork.toLat_bij
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:33.120802+00:00
-- url     : https://prove2.me/submissions/8296c6d1-2c0f-4c54-8ba9-ca677791cbc3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DiscrNe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NonzeroDiscriminants_DiscLat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ModularForm EisensteinSeries UpperHalfPlane
noncomputable section
open DiscrNeWork
namespace DiscrNeWork
theorem _root_.solution (a : ℂ) (ha : a ≠ 0) (τ : ℍ) : Function.Bijective (toLat a ha τ) := by
  constructor
  · intro v v' hvv
    have h1 : a * ((v.1 0 : ℂ) * τ + v.1 1) = a * ((v'.1 0 : ℂ) * τ + v'.1 1) :=
      congrArg Subtype.val hvv
    have h2 := mul_left_cancel₀ ha h1
    obtain ⟨e0, e1⟩ := lin_inj τ h2
    apply Subtype.ext
    funext i
    fin_cases i
    · exact e0
    · exact e1
  · rintro ⟨w, hw, hw0⟩
    have hw' := hw
    rw [PI.lat2, AddSubgroup.mem_closure_pair] at hw'
    obtain ⟨m, n, hmn⟩ := hw'
    have hv : (![n, m] : Fin 2 → ℤ) ∈ nz := by
      intro h
      apply hw0
      have hn : n = 0 := congrFun h 0
      have hm : m = 0 := congrFun h 1
      rw [← hmn, hn, hm]
      simp
    refine ⟨⟨![n, m], hv⟩, ?_⟩
    apply Subtype.ext
    show a * ((((![n, m] : Fin 2 → ℤ) 0 : ℤ) : ℂ) * (τ : ℂ) + (((![n, m] : Fin 2 → ℤ) 1 : ℤ) : ℂ)) = w
    have e0 : (![n, m] : Fin 2 → ℤ) 0 = n := rfl
    have e1 : (![n, m] : Fin 2 → ℤ) 1 = m := rfl
    rw [e0, e1, ← hmn, zsmul_eq_mul, zsmul_eq_mul]
    ring
end DiscrNeWork
