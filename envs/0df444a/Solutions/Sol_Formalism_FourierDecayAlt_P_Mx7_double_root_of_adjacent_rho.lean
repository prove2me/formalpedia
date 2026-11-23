-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.double_root_of_adjacent_rho
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:40:52.64533+00:00
-- url     : https://prove2.me/submissions/1e707b4d-b408-40e0-a193-8d3619aefd52

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_ord
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_rho_inj
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_tyInterlaces
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_ord
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_tyInterlaces


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx7
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset Polynomial
noncomputable section
namespace Formalism.FourierDecayAlt.P.Mx7
theorem _root_.solution (P : Par) (hP : P.OK) (π : Ty P) : ∀ l ∈ Icc 1 (P.k - 1), ∀ m ∈ Icc 1 (P.k - 1),
    (rho P π m : ℂ) = (rho P π l : ℂ) + 1 → (Nrm P l π : ℂ) = 0 ∧ (NrmDown P m π : ℂ) = 0 ∧
      (X + C ((rho P π l : ℂ) + 1)) * (X + C ((rho P π l : ℂ) + 1)) ∣ q1P P := by
  intro l hl m hm h
  have hl' := Finset.mem_Icc.1 hl
  have hr : rho P π m = rho P π l + 1 := by exact_mod_cast h
  have hml : m < l := by
    rcases lt_trichotomy m l with h1 | h1 | h1
    · exact h1
    · rw [h1] at hr; linarith
    · have := Mx3.rho_inj P hP π l m hl hm h1; linarith
  refine ⟨?_, ?_, ?_⟩
  · have : ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l - 1) = 0 :=
      Finset.prod_eq_zero (i := m) (Finset.mem_erase.2 ⟨ne_of_lt hml, hm⟩) (by rw [hr]; ring)
    unfold Nrm
    rw [this, mul_zero, div_zero, Complex.ofReal_zero]
  · have : ∏ j ∈ (Icc 1 (P.k - 1)).erase m, (rho P π j - rho P π m + 1) = 0 :=
      Finset.prod_eq_zero (i := l) (Finset.mem_erase.2 ⟨ne_of_gt hml, hl⟩) (by rw [hr]; ring)
    unfold NrmDown
    rw [this, zero_mul, div_zero, Complex.ofReal_zero]
  · have hI := Mx3.tyInterlaces P hP π
    have o3 := (Mx3.ord P.k P.u P.u' (rho P π) hI l hl).2.2.1 m hm hml
    have b := hI l hl
    have hu : P.u l = rho P π l + 1 / 2 := by linarith [o3.1, b.1]
    have hu' : P.u' l = rho P π l + 1 / 2 := by linarith [o3.2, b.2.1]
    have hd : (X + C (1 / 2 + (P.u l : ℂ))) * (X + C (1 / 2 + (P.u' l : ℂ))) ∣ q1P P :=
      Finset.dvd_prod_of_mem (fun i => (X + C (1 / 2 + (P.u i : ℂ))) * (X + C (1 / 2 + (P.u' i : ℂ))))
        (Finset.mem_Icc.2 ⟨hl'.1, by omega⟩)
    have e1 : (1 / 2 + (P.u l : ℂ)) = (rho P π l : ℂ) + 1 := by rw [hu]; push_cast; ring
    have e2 : (1 / 2 + (P.u' l : ℂ)) = (rho P π l : ℂ) + 1 := by rw [hu']; push_cast; ring
    rwa [e1, e2] at hd
end Formalism.FourierDecayAlt.P.Mx7
