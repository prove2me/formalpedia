-- Prove2me | solution 1 for CompanionTheory.LimBd.SchurHpk.memLp_of_ds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:42:19.092715+00:00
-- url     : https://prove2.me/submissions/82bcbe75-0a24-482f-b0a6-130b2cf499a1

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurOrthogonality
import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurH
import Theorems.Thm_CompanionTheory_LimBd_SchurHpk_iota_measEmb
import Theorems.Thm_CompanionTheory_LimBd_SchurHpk_exists_map_iota

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.LimBd CompanionTheory.LimBd.SchurHpk
open MeasureTheory Matrix Topology PI.UpqRep CompanionTheory.LimBd.URep
open scoped InnerProductSpace ENNReal
variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
omit [CompleteSpace H]
namespace CompanionTheory.LimBd.SchurHpk
theorem _root_.solution {lam : Fin (2 * r + k + 1) → ℝ}
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)} (h : IsDSHpk k r ε lam σ)
    {μG : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hμ : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG) (v w : H) :
    MemLp (fun x : Formalism.QuantumDeterminants.Mt k r => ⟪w, σ (Matrix.of x) v⟫_ℂ) 2 μG := by
  obtain ⟨P, ⟨hP, -⟩, -, -, -, -, hsq, -⟩ := h
  obtain ⟨c, -, hcT, rfl⟩ := exists_map_iota hP hμ
  rw [(iota_measEmb hP).memLp_map_measure_iff]
  exact (hsq v w).smul_measure hcT
end CompanionTheory.LimBd.SchurHpk
