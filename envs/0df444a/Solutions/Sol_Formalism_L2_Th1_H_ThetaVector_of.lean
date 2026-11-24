-- Prove2me | solution 1 for Formalism.L2.Th1.H.ThetaVector_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:38:52.868749+00:00
-- url     : https://prove2.me/submissions/fa1c073d-4d1d-4120-9054-fe71537a90a4

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_LineTransport
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlockFirstBlockEmb
import Theorems.Thm_Formalism_L2_Th1_H_isSemiChar_congr
import Theorems.Thm_Formalism_L2_Th1_H_InterTh_of
import Theorems.Thm_Formalism_L2_Th1_H_heisenbergAnalytic
import Theorems.Thm_Formalism_L2_Th1_H_semicharacterHom
import Theorems.Thm_Formalism_L2_Th1_H_standardFormBasic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
namespace Formalism.L2.Th1.H
theorem _root_.solution (hLine : LineTransport) (hStd : ThStd) (hF0 : ProductThetaMem) (hSD : StdSelfDual)
    (hSC : StdSemiChar) (hIso : ThIsom) (h4 : FourthRoot) : ThetaVector := by
  intro L ω₀ n _ _ h Λ α β g D κ hκ
  have hHerm : IsHerm (stdH L (Fin 4 × n)) := (standardFormBasic L (Fin 4 × n)).2.1
  have hβ1 : IsSemiChar (stdH L (Fin 4 × n)) (stdLat L (Fin 4 × n)) β :=
    isSemiChar_congr _ _ _ _ D.betaStd (hSC L ω₀ (Fin 4 × n) D.per)
  obtain ⟨hFmem, hF1⟩ := hF0 L ω₀ (Fin 4 × n) D.per D.half β D.betaStd
  have hFne : F0 L ω₀ (Fin 4 × n) ≠ 0 := by
    intro h0
    rw [h0] at hF1
    simp at hF1
  obtain ⟨hIne, hIline⟩ := hLine (Fin 4 × n → ℂ) (stdH L (Fin 4 × n)) hHerm (stdLat L (Fin 4 × n))
    (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) β (hSD L _) D.selfDual hβ1 D.betaSemi
    D.idx₁ D.idx₂ _ hFmem hFne (fun F hF => ⟨F 0, hStd L ω₀ _ D.per D.half β D.betaStd F hF⟩)
  have hImem := InterTh_of semicharacterHom heisenbergAnalytic (Fin 4 × n → ℂ) (stdH L (Fin 4 × n)) hHerm
    (stdLat L (Fin 4 × n)) (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) β D.betaSemi
    D.idx₁ _ hFmem
  have hβg : (fun v => β (g v)) = fun x => ∏ a, α (slice a x) := funext D.betaAlpha
  have hiso := hIso (Fin 4 × n → ℂ) (Fin 4 × n → ℂ) (matH (blk4 h)) (stdH L (Fin 4 × n)) g D.isom
    (pow4 Λ) β
  rw [hβg] at hiso
  have hK : kernel4 L ω₀ Λ β g ∈ Th (matH (blk4 h)) (fun x => ∏ a, α (slice a x)) (pow4 Λ) :=
    (hiso _).1 hImem
  have hK0 : kernel4 L ω₀ Λ β g ≠ 0 := by
    intro h0
    apply hIne
    funext w
    have := congrFun h0 (g.symm w)
    simpa [kernel4] using this
  have hP : κ • kernel4 L ω₀ Λ β g ∈ Th (matH (blk4 h)) (fun x => ∏ a, α (slice a x)) (pow4 Λ) :=
    Submodule.smul_mem _ κ hK
  have hP0 : κ • kernel4 L ω₀ Λ β g ≠ 0 := smul_ne_zero hκ hK0
  have hPline : ∀ G ∈ Th (matH (blk4 h)) (fun x => ∏ a, α (slice a x)) (pow4 Λ),
      ∃ c : ℂ, G = c • (κ • kernel4 L ω₀ Λ β g) := by
    intro G hG
    have hG' : (fun w => G (g.symm w)) ∈ Th (stdH L (Fin 4 × n)) β
        (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) := by
      refine (hiso _).2 ?_
      simpa using hG
    obtain ⟨c, hc⟩ := hIline _ hG'
    refine ⟨c * κ⁻¹, funext fun z => ?_⟩
    have h1 := congrFun hc (g z)
    simp only [LinearEquiv.symm_apply_apply, Pi.smul_apply, smul_eq_mul] at h1
    simp only [Pi.smul_apply, smul_eq_mul, kernel4]
    rw [h1]
    field_simp
  obtain ⟨hex, huniq⟩ := h4 n h Λ α D.alpha0 _ hP hP0 hPline
  refine ⟨hex, fun θ hθ hθP => ⟨?_, huniq θ hθ hθP⟩⟩
  rintro rfl
  apply hP0
  rw [← hθP]
  funext z
  exact Finset.prod_eq_zero (Finset.mem_univ (0 : Fin 4)) rfl
end Formalism.L2.Th1.H
