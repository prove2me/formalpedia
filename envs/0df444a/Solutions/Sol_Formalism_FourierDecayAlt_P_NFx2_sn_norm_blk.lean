-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.sn_norm_blk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:35:09.675751+00:00
-- url     : https://prove2.me/submissions/0e12dd3a-bced-4c25-b9aa-68d694cfcbf1

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_ss_pj_none
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sn_raises
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sn_e_self
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sn_norm_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_nrm_key


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Polynomial
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFx2
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.NF
noncomputable section
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {L : R.LevelData A P.r}
  {κ : (M.Ty P → ℂ) →ₐ[ℂ] A} {SS : ℕ → A}
namespace Formalism.FourierDecayAlt.P.NFx2
theorem _root_.solution (hc : RelCore (⟨L, κ, SS⟩ : Q.NFData P A)) (hs : Fr.IsStarLevel L) (hP : P.OK)
    (hNF : M.NrmFacts) (hRP : M.RealPoints)
    {QQ : ℂ → Matrix (Fin 2) (Fin 2) A}
    (h22 : ∀ Y, QQ Y 1 1 = L.GG * xA κ Y)
    (h21 : ∀ Y, QQ Y 1 0 = L.GG * xA κ Y * L.l0 Y + Q.NFData.weightedSumBis (⟨L, κ, SS⟩ : Q.NFData P A) Y)
    (h12 : ∀ Y, QQ Y 0 1 = L.GG * xA κ Y * L.m0 Y + Q.NFData.S12 (⟨L, κ, SS⟩ : Q.NFData P A) Y)
    (hD3 : ∀ Y, QQ Y 0 0 * QQ (Y + 1) 1 1 - QQ Y 0 1 * QQ (Y + 1) 1 0 = algebraMap ℂ A (M.qC P Y))
    (hD4 : ∀ Y, QQ Y 1 0 * QQ (Y + 1) 1 1 = QQ Y 1 1 * QQ (Y + 1) 1 0) (hpoly : IsPF fun Y => QQ Y 0 0)
    {l : ℕ} (hl : l ∈ Icc 1 (P.k - 1)) (τ : M.Ty P) :
    star (SS l) * SS l * proj κ τ = ((M.Nrm P l τ : ℝ) : ℂ) • proj κ τ := by
  by_cases hτ : ∃ τ', M.Up P l τ τ'
  · obtain ⟨τ', hU⟩ := hτ
    have hpos := ((hNF P hP l hl τ).1 τ' hU).1
    set den : ℝ := (∏ j ∈ (Icc 1 (P.k - 1)).erase l, (M.rho P τ j - M.rho P τ l)) *
        ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (M.rho P τ j - M.rho P τ l - 1) with hden
    have hd : den ≠ 0 := by
      intro h0; unfold M.Nrm at hpos; rw [← hden, h0, div_zero] at hpos; exact lt_irrefl _ hpos
    have key := Mx3.nrm_key P hP l hl τ
    rw [← hden] at key
    have e := sn_norm_eq hc hs h22 h21 h12 hD3 hD4 hpoly hl τ
    rw [sn_e_self, ← hden, (hRP P τ _).2,
      show I.qpoly P.k P.T P.T' P.u P.u' (-M.rho P τ l - 1) = -(M.Nrm P l τ * den) by linarith] at e
    have hdC : ((den : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hd
    have e3 : ((den : ℝ) : ℂ) • (star (SS l) * SS l * proj κ τ) =
        ((den : ℝ) : ℂ) • (((M.Nrm P l τ : ℝ) : ℂ) • proj κ τ) := by
      rw [eq_neg_of_add_eq_zero_right e, smul_smul]; push_cast; rw [neg_smul, neg_neg, mul_comm]
    exact smul_right_injective A hdC e3
  · rw [mul_assoc, ss_pj_none κ (sn_raises hc) hτ, mul_zero, (hNF P hP l hl τ).2.1 hτ]; simp
end Formalism.FourierDecayAlt.P.NFx2
