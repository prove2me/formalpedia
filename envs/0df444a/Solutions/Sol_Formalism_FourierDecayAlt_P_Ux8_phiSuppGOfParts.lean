-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux8.phiSuppGOfParts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:13:34.140735+00:00
-- url     : https://prove2.me/submissions/704f51fa-6df1-42c8-9316-c9d5bca0a9e2

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SeminormCompletion
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux8_cont_Gf
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux8_cont_DjU
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux8_Rw_vanish
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Rw_vanish


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux8
open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P.Ux8
theorem _root_.solution : PhiSuppGOfParts := by
  intro hGf _ hZh
  intro k p s ρ Wp Wq _ _ _ _ _ ι _ U C₂ hOk f Z _ γ _ hγS
  obtain ⟨_, _, hz, hz', _, hχ, hχε, _, hsupp, _⟩ := hOk
  obtain ⟨_, _, hχ0⟩ := hχ
  obtain ⟨_, _, hχε0⟩ := hχε
  have hlow : Gf k ρ (lowV k (p + s) ρ U.z) (lowV k (p + s) ρ U.z') γ < U.ε' := not_le.mp (fun h => hγS h)
  let O : Set (B.Mat k (p + s + ρ)) :=
    {g | DjU k (p + s) ρ g ∉ tsupport U.χ} ∪ {g | Gf k (p + s + ρ) U.z U.z' g < U.ε}
  have hO : IsOpen O :=
    ((isClosed_tsupport U.χ).isOpen_compl.preimage (cont_DjU k (p + s) ρ)).union
      (isOpen_Iio.preimage (cont_Gf k (p + s + ρ) U.z U.z'))
  have hOz : ∀ g ∈ O, cutDG k (p + s) ρ U.z U.z' U.χ U.χε f g = 0 := by
    intro g hg
    rcases hg with hg | hg
    · have h0 : U.χ (DjU k (p + s) ρ g) = 0 := by
        by_contra hne
        exact hg (subset_tsupport _ hne)
      show (U.χ (DjU k (p + s) ρ g) * ((U.χε (Gf k (p + s + ρ) U.z U.z' g) : ℝ) : ℂ)) • f g = 0
      rw [h0, zero_mul, zero_smul]
    · show (U.χ (DjU k (p + s) ρ g) * ((U.χε (Gf k (p + s + ρ) U.z U.z' g) : ℝ) : ℂ)) • f g = 0
      rw [hχε0 _ hg, Complex.ofReal_zero, mul_zero, zero_smul]
  have hzero : ∀ ξ, U.F1 f (gaXi k ρ U.σ U.d ξ Z γ) = 0 := by
    intro ξ
    have hg₀O : gaXi k ρ U.σ U.d ξ Z γ ∈ O := by
      by_cases hw : DjU k (p + s) ρ (gaXi k ρ U.σ U.d ξ Z γ) ∈ tsupport U.χ
      · refine Or.inr ?_
        have hdet : DjU k (p + s) ρ (gaXi k ρ U.σ U.d ξ Z γ) = (ZjH U.σ U.d ξ.2 Z).det := by
          show (Zh k (p + s) ρ ((Rn k (p + s) ρ ξ.1.1)⁻¹ * mMap k (p + s) ρ (ZjH U.σ U.d ξ.2 Z) γ *
            Rn k (p + s) ρ ξ.1.2)).det = _
          rw [hZh k (p + s) ρ ξ.1.1 ξ.1.2 (ZjH U.σ U.d ξ.2 Z) γ]
        show Gf k (p + s + ρ) U.z U.z' ((Rn k (p + s) ρ ξ.1.1)⁻¹ * mMap k (p + s) ρ (ZjH U.σ U.d ξ.2 Z) γ *
          Rn k (p + s) ρ ξ.1.2) < U.ε
        rw [hGf k (p + s) ρ U.z U.z' hz hz' ξ.1.1 ξ.1.2 (ZjH U.σ U.d ξ.2 Z) γ]
        rw [hdet] at hw
        have hne : (ZjH U.σ U.d ξ.2 Z).det ≠ 0 := fun h => hχ0 (h ▸ hw)
        have hN : 0 < Complex.normSq (ZjH U.σ U.d ξ.2 Z).det := Complex.normSq_pos.2 hne
        have hs := hsupp _ hw
        rw [← Complex.normSq_eq_norm_sq] at hs
        calc Complex.normSq (ZjH U.σ U.d ξ.2 Z).det * Gf k ρ (lowV k (p + s) ρ U.z) (lowV k (p + s) ρ U.z') γ
            < Complex.normSq (ZjH U.σ U.d ξ.2 Z).det * U.ε' := mul_lt_mul_of_pos_left hlow hN
          _ ≤ U.ε := by linarith [hs]
      · exact Or.inl hw
    funext i
    show B.opApply (U.Θ i) (cutDG k (p + s) ρ U.z U.z' U.χ U.χε f) (gaXi k ρ U.σ U.d ξ Z γ) = 0
    unfold B.opApply
    apply List.sum_eq_zero
    intro y hy
    obtain ⟨T, _, rfl⟩ := List.mem_map.1 hy
    rw [Rw_vanish hO hOz T.word _ hg₀O, map_zero]
  show ∫ ξ, psiStar k ρ U.σ U.z U.z' ξ • U.F1 f (gaXi k ρ U.σ U.d ξ Z γ) ∂(muXi k p s ρ U.σ) = 0
  simp only [hzero, smul_zero, MeasureTheory.integral_zero]
end Formalism.FourierDecayAlt.P.Ux8
