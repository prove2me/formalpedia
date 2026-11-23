-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.std_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:55.723145+00:00
-- url     : https://prove2.me/submissions/fe4e8229-7eed-4845-b90c-8fbb36a073ec

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_SmallPI

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
namespace CompanionTheory.D.gk.admitted
theorem _root_.solution {A : Type} [Ring A] [Algebra ℂ A] [Module.Finite ℂ A] {M : ℕ} (hM : Module.finrank ℂ A < M)
    (b : Fin M → A) :
    ∑ π : Equiv.Perm (Fin M), ((Equiv.Perm.sign π : ℤ) : A) * (List.ofFn fun i => b (π i)).prod = 0 := by
  have hdep : ¬ LinearIndependent ℂ b := fun h => by
    have := h.fintype_card_le_finrank
    rw [Fintype.card_fin] at this
    omega
  have h := (MultilinearMap.alternatization (MultilinearMap.mkPiAlgebraFin ℂ M A)).map_linearDependent b hdep
  rw [MultilinearMap.alternatization_apply] at h
  rw [← h]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [MultilinearMap.domDomCongr_apply, MultilinearMap.mkPiAlgebraFin_apply, Units.smul_def, zsmul_eq_mul]
end CompanionTheory.D.gk.admitted
