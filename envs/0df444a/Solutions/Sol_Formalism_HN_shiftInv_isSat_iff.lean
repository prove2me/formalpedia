-- Prove2me | solution 1 for Formalism.HN.shiftInv_isSat_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:54:26.390692+00:00
-- url     : https://prove2.me/submissions/f976afc5-80ae-4193-a87f-b7d003c62fe3

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance
import Theorems.Thm_Formalism_HN_shiftInv_zl_mono
import Theorems.Thm_Formalism_F_saturProps
import Theorems.Thm_Formalism_HN_real_saturation_property
import Theorems.Thm_Formalism_HN_saturation_basic_properties


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN
universe u v w w₂
namespace Formalism.HN
theorem _root_.solution {R V E : Type*} [Ring R] [AddCommGroup V] [Module R V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (ρ : V →+ E)
    {L : Submodule R V} (hL : IsLat ρ L) (N : Submodule R V) :
    IsSat ρ L N ↔
      N ≤ L ∧ ∀ N' : Submodule R V, N ≤ N' → N' ≤ L → rk ρ N' = rk ρ N → N' = N := by
  have hB := saturation_basic_properties R V E ρ L hL
  constructor
  · intro hN
    exact ⟨hN.1, fun N' h₁ h₂ h₃ => hB.2.2.1 N N' hN h₁ h₂ h₃⟩
  · rintro ⟨hNL, hmax⟩
    obtain ⟨N', hNN', hN'L, himg⟩ := real_saturation_property R V E ρ L N hL hNL
    have hsat := Formalism.F.saturProps E (zl ρ L) (zl ρ N) hL.2
      (shiftInv_zl_mono ρ hNL)
    have hrk : rk ρ N' = rk ρ N := by
      show Formalism.F.rk (zl ρ N') = Formalism.F.rk (zl ρ N)
      rw [himg]
      exact hsat.2.2
    have heq : N' = N := hmax N' hNN' hN'L hrk
    refine ⟨hNL, ?_⟩
    rw [← heq, himg]
    exact hsat.1
end Formalism.HN
