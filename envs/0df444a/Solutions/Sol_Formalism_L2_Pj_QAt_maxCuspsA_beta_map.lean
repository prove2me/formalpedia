-- Prove2me | solution 1 for Formalism.L2.Pj.QAt.maxCuspsA_beta_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:43:52.117125+00:00
-- url     : https://prove2.me/submissions/2ab8e006-0d87-46df-bf49-cb91ba98430e

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMeanContinuity
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsPfA
import Theorems.Thm_Formalism_L2_Pj_QAt_maxCuspsA_kappa_cc
import Theorems.Thm_Formalism_L2_Pj_FJ_FnVia_smul_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G.FD NumberField Matrix Formalism.L2.Pj.FJ Complex
open scoped ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.QAt
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}
namespace Formalism.L2.Pj.QAt
theorem _root_.solution (X : Data E r) (la : Wt X.Ψ r) (η : Fin ρ → E) (a : E)
    (ha : cc a = a) (τ : X.Ψ) :
    (mcBeta X la η a).map τ.1 =
      (((ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters.per X la a τ : ℝ) : ℂ) * (-(I * X.c τ))) • mcMηc τ.1 η := by
  have hτ : ∀ x : E, τ.1 (cc x) = (starRingEnd ℂ) (τ.1 x) := fun x => by
    first
    | exact IsCMField.complexEmbedding_complexConj τ.1 x
    | exact IsCMField.complexEmbedding_complexConj (K := E) τ.1 x
    | simp [cc, IsCMField.complexEmbedding_complexConj]
    | simp [cc]
  have gen : ∀ z : ℂ, z.re = 0 → ‖z‖ = |z.im| := fun z hz0 => by
    have hz : z = (z.im : ℂ) * I := Complex.ext (by simp [hz0]) (by simp)
    rw [hz]
    simp
  have hk : τ.1 X.κ0 = -(I * (X.c τ : ℂ)) := by
    have h1 : (starRingEnd ℂ) (τ.1 X.κ0) = -τ.1 X.κ0 := by
      rw [← hτ, maxCuspsA_kappa_cc, map_neg]
    have hre : (τ.1 X.κ0).re = 0 := by
      have h2 := congrArg Complex.re h1
      simp only [Complex.conj_re, Complex.neg_re] at h2
      linarith
    have hnorm : ‖τ.1 X.κ0‖ = X.c τ := by
      have h2 : ‖τ.1 (2 * X.ξ0)‖ = X.c τ := by
        rw [map_mul, norm_mul, map_ofNat, Data.c]
        first
        | norm_num
        | simp
      rcases X.κ0_xi with h | h
      · rw [h, h2]
      · rw [h, map_neg, norm_neg, h2]
    have hz : τ.1 X.κ0 = ((τ.1 X.κ0).im : ℂ) * I := Complex.ext (by simp [hre]) (by simp)
    have hn : |(τ.1 X.κ0).im| = X.c τ := by rw [← gen _ hre, hnorm]
    rw [abs_of_neg (X.κ0_sign τ)] at hn
    rw [hz, ← hn]
    push_cast
    ring
  have ha' : (((τ.1 a).re : ℝ) : ℂ) = τ.1 a := Complex.conj_eq_iff_re.mp (by rw [← hτ, ha])
  ext i j
  simp only [mcBeta, mcMη, mcMηc, Matrix.map_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul,
    map_mul, map_natCast, hτ, hk, ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters.per]
  push_cast
  rw [ha']
  ring
end Formalism.L2.Pj.QAt
