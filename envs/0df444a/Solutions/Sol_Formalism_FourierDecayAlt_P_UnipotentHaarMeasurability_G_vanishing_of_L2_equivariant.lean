-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability.G.vanishing_of_L2_equivariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:41:23.812479+00:00
-- url     : https://prove2.me/submissions/a0ae80f2-4c41-4ebd-8153-ecdf94b41605

import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_BesselOrbitConvolutions_BesselNonvanishingReduction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_VanishingOfL2Equivariant
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_BesselOrbitConvolutions_VanishingOfL2Equivariant
import Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_uh_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_TranslationBesselVanishing_sigma_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_TranslationBesselVanishing_smooth_translate
import Theorems.Thm_Formalism_FourierDecayAlt_P_TranslationBesselVanishing_uh_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_UnipotentHaarMeasurability_aez
import Theorems.Thm_Formalism_FourierDecayAlt_P_UnipotentHaarMeasurability_sigma_one
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_mul
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
noncomputable section
set_option maxHeartbeats 3200000
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability
open Formalism.FourierDecayAlt.ThreeDimData
open Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability.G
namespace Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability.G
theorem _root_.solution {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {h : ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Mx k r → (H →L[ℂ] H)}
    {w0 : H} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [FiniteDimensional ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {u : Fin k → ℝ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    {μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)} (hBC : CompanionTheory.D.Upq.BesselFunctionalConstruction.BeConv) (hIn : CompanionTheory.D.Upq.BesselFunctionalConstruction.Inputs)
    (hS : Side k r ε lam h σ w0 z c u π μW μN μG νq)
    {x : H} (hx : x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ) {v : H} (hv : IsAdm σ w0 v)
    (hl : ∀ ξ : Wp, PI.BesselPeriodGGP.l2SG νq (fun g => be z c π σ μW μN (σ g x) v ξ) = 0) :
    be z c π σ μW μN x v = 0 := by
  have hS' := hS
  obtain ⟨hlam, hσ, -, -, hw0, -, -, -, -, hW, hN, hG, hq⟩ := hS'
  obtain ⟨-, hBC2, hBC3, -⟩ := hBC hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS
  ext ξ
  have hc : ContinuousOn (fun g => be z c π σ μW μN (σ g x) v ξ) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :=
    (hBC3 x hx v hv).clm_apply continuousOn_const
  have heq : ∀ hh ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ n ∈ Formalism.QuantumDeterminants.Nset k r, ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      be z c π σ μW μN (σ (hh * n * g) x) v ξ = Formalism.QuantumDeterminants.psi k r z c n • π hh (be z c π σ μW μN (σ g x) v ξ) := by
    intro hh hhW n hn g hg
    have hhn : hh * n ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hhW.1 hn.1
    have hm : σ (hh * n * g) = (σ (hh * n)).comp (σ g) := TranslationBesselVanishing.sigma_mul hσ hhn hg
    rw [hm, ContinuousLinearMap.comp_apply,
      hBC2 v hv hh hhW n hn (σ g x) (TranslationBesselVanishing.smooth_translate hσ hx hg)]
    rfl
  have h0 := aez hW hN hG hq (fun g => be z c π σ μW μN (σ g x) v ξ) hc heq (hl ξ) 1 Formalism.QuantumDeterminants.WeylGroupFacts.uh_one
  simpa [sigma_one hσ] using h0
end Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability.G
