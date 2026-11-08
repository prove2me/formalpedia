-- Prove2me | solution 1 for DRBatchBandit.eq_A9_regret_le_two_sup
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T23:33:26.196961+00:00
-- url     : https://prove2.me/submissions/768dbc44-c301-4eee-bef8-606d0061bb73

import Mathlib
import Definitions.Def_OfflinePolicyLearning_Regret_Setting
import Definitions.Def_DRBatchBandit_RobustValue
import Definitions.Def_DRBatchBandit_Estimator

open OfflinePolicyLearning.Regret

open DRBatchBandit in
theorem solution {X : Type*} [MeasurableSpace X] {d : ℕ} (M : Model X d) (δ : ℝ)
    (Pol : Set (X → Fin d)) {n : ℕ} (D : Fin n → Obs X d) (πhat : X → Fin d)
    (hmem : πhat ∈ Pol) (hmax : ∀ π ∈ Pol, QhatDRO M δ D π ≤ QhatDRO M δ D πhat)
    (T : ℝ) (hT : ∀ π ∈ Pol, |QhatDRO M δ D π - QDRO M δ π| ≤ T) :
    RDRO M δ Pol πhat ≤ 2 * T := by
  unfold RDRO
  haveI : Nonempty Pol := ⟨⟨πhat, hmem⟩⟩
  have hs : (⨆ π' : Pol, QDRO M δ π'.1) ≤ QDRO M δ πhat + 2 * T := by
    apply ciSup_le
    intro π'
    have h1 := abs_le.mp (hT π'.1 π'.2)
    have h2 := abs_le.mp (hT πhat hmem)
    have h3 := hmax π'.1 π'.2
    linarith [h1.1, h1.2, h2.1, h2.2]
  linarith
