-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.eproj_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:06.701784+00:00
-- url     : https://prove2.me/submissions/d9c4024b-692f-4e66-b3e6-31230a37eaeb

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RestrictionMinMaxIntHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_wtsp_mono
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_eproj_fix
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_lowIm_keep
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply



set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (LL : Letters N) (j : ℕ) (ρ : Fin r) (w1 w2 : Fin r → ℤ)
    (HeightBoundSetup LogBallEstimates : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (h1 : IsEProj p LL j ρ w1 HeightBoundSetup) (h2 : IsEProj p LL j ρ w2 LogBallEstimates)
    (Q : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hQ : ∀ c ∈ univ.erase ρ, ∀ d ∈ univ.erase ρ, ∀ x, Q (glAct p LL j c d x) = glAct p LL j c d (Q x))
    (hW : ∀ x ∈ WtSpC p LL j univ w1, Q x ∈ WtSpC p LL j univ w2) :
    ∀ F ∈ WtSpC p LL j univ w1, LogBallEstimates (Q F) = Q (HeightBoundSetup F) := by
  intro F hF
  obtain ⟨i1, r1, k1⟩ := h1
  obtain ⟨i2, r2, k2⟩ := h2
  have hP1 : HeightBoundSetup F ∈ HWC p LL j (univ.erase ρ) w1 ⊓ WtSpC p LL j univ w1 := by
    rw [← r1]; exact LinearMap.mem_range_self HeightBoundSetup F
  have hfix1 : HeightBoundSetup (HeightBoundSetup F) = HeightBoundSetup F := LinearMap.congr_fun i1 F
  have hK : F - HeightBoundSetup F ∈ LinearMap.ker HeightBoundSetup ⊓ WtSpC p LL j univ w1 := by
    refine Submodule.mem_inf.mpr ⟨?_, Submodule.sub_mem _ hF (Submodule.mem_inf.mp hP1).2⟩
    rw [LinearMap.mem_ker, map_sub, hfix1, sub_self]
  rw [k1] at hK
  obtain ⟨hKL, hKW⟩ := Submodule.mem_inf.mp hK
  have hQK : Q (F - HeightBoundSetup F) ∈ LinearMap.ker LogBallEstimates ⊓ WtSpC p LL j univ w2 := by
    rw [k2]
    exact Submodule.mem_inf.mpr ⟨lowIm_keep LL j ρ Q hQ _ hKL, hW _ hKW⟩
  have hQH : Q (HeightBoundSetup F) ∈ HWC p LL j (univ.erase ρ) w2 ⊓ WtSpC p LL j univ w2 := by
    obtain ⟨hH, hWW⟩ := Submodule.mem_inf.mp hP1
    have hQW := hW _ hWW
    refine Submodule.mem_inf.mpr ⟨?_, hQW⟩
    simp only [HWC, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at hH ⊢
    refine ⟨wtsp_mono LL j _ w2 hQW, fun c d hcd => ?_⟩
    rw [← hQ c hcd.1 d hcd.2.1, hH.2 c d hcd, map_zero]
  have e2 : LogBallEstimates (Q (HeightBoundSetup F)) = Q (HeightBoundSetup F) := eproj_fix LL j ρ w2 LogBallEstimates ⟨i2, r2, k2⟩ _ hQH
  have e3 : LogBallEstimates (Q (F - HeightBoundSetup F)) = 0 := (Submodule.mem_inf.mp hQK).1
  have hsplit : Q F = Q (HeightBoundSetup F) + Q (F - HeightBoundSetup F) := by
    rw [← map_add]; simp
  rw [hsplit, map_add, e2, e3, add_zero]
end Formalism.InvariantFactorPaths.L4
