-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.proj_fixC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:11:52.903464+00:00
-- url     : https://prove2.me/submissions/07d586d9-f9dd-422e-be44-046937caadae

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_InitPartZeroXMul
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FirstWeightLeOfSupport
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_hwc_le_isoCC
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_typeProj_glActC
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_exists_hwC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (T : Set (Fin r → ℤ))
    (P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hP : IsTypeProj p LL j Cs T P) (S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
    (hSP : S ≤ Pol p r LL) (hS : ∀ c ∈ Cs, ∀ d ∈ Cs, ∀ x ∈ S, glAct p LL j c d x ∈ S) (hPS : ∀ x ∈ S, P x ∈ S)
    (hT : ∀ h ∈ S, h ≠ 0 → ∀ μ, h ∈ HWC p LL j Cs μ → μ ∈ T) : ∀ x ∈ S, P x = x := by
  have hPid : ∀ y, P (P y) = P y := fun y => LinearMap.congr_fun hP.1 y
  have hK0 : ∀ y ∈ S, P y = 0 → y = 0 := by
    intro y hy hPy
    by_contra hy0
    obtain ⟨h, hhK, hh0, μ, hμ⟩ := exists_hwC LL j Cs (S ⊓ LinearMap.ker P) (le_trans inf_le_left hSP)
      (fun c hc d hd z hz => by
        rw [Submodule.mem_inf, LinearMap.mem_ker] at hz ⊢
        exact ⟨hS c hc d hd z hz.1, by rw [typeProj_glActC LL j Cs T P hP c hc d hd z, hz.2, map_zero]⟩)
      y (Submodule.mem_inf.mpr ⟨hy, hPy⟩) hy0
    rw [Submodule.mem_inf, LinearMap.mem_ker] at hhK
    have hT' := hT h hhK.1 hh0 μ hμ
    have hrange : h ∈ LinearMap.range P := by
      rw [hP.2.1]
      exact (le_iSup₂ (f := fun la (_ : la ∈ T) => IsoC p LL j Cs la) μ hT') (hwc_le_isoCC LL j Cs μ hμ)
    obtain ⟨z, rfl⟩ := hrange
    apply hh0
    rw [← hPid z]
    exact hhK.2
  intro x hx
  have := hK0 (P x - x) (sub_mem (hPS x hx) hx) (by rw [map_sub, hPid, sub_self])
  exact sub_eq_zero.mp this
end Formalism.InvariantFactorPaths.L4
