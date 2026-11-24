-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.thetaExistsStepOfSteps
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:04:38.915896+00:00
-- url     : https://prove2.me/submissions/83869597-b7a7-479a-b447-9d9e3d144889

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FiniteClassesPositiveSums
import Theorems.Thm_Formalism_FourierDecayAlt_P_FiniteClassesPositiveSums_psd_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_FiniteClassesPositiveSums_psd_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_FiniteClassesPositiveSums_finite_classes
import Theorems.Thm_Formalism_FourierDecayAlt_P_FiniteClassesPositiveSums_finsum_classes
import Theorems.Thm_Formalism_FourierDecayAlt_P_FiniteClassesPositiveSums_psd_single
import Theorems.Thm_Formalism_FourierDecayAlt_P_FiniteClassesPositiveSums_limit_core

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology Finset
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.FiniteClassesPositiveSums
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.A6.ThetaExistenceInductive := by
  intro hThOm hSupp hNsS hCOne hExh _hLF hEntry hClosed hSubseq hA2 hN1 K _ _ _ R ψ hD hch s hs hAt
    n₀ F hF
  classical
  obtain ⟨Lc, hcut, hGL⟩ := hSupp hNsS K R ψ hD (s + 1) F (by omega)
  obtain ⟨Om, hOm, hmono, hex⟩ := hExh K R ψ hD hch (s + 1) (by omega)
  choose Th hTh using fun j => hThOm hA2 hN1 K R ψ hD hch s hs hAt n₀ F Lc (Om j) hF hcut (hOm j)
  obtain ⟨hLo, hLk, -, -⟩ := hcut
  have hfin := finite_classes R hD.isOpen (Lc : Set K) hLk
  have hS : ∀ y : K ⧸ R.toAddSubgroup, (Quotient.out y : K) ∈ (Lc : Set K) → y ∈ hfin.toFinset :=
    fun y hy => hfin.mem_toFinset.2 hy
  let M : Point K → Point K → ℂ := fun h h' =>
    ((cSize R h ^ (s + 1) * cSize R h' ^ (s + 1) : ℝ) : ℂ) * N0 R ψ h h'
  obtain ⟨φ, Θ, hφ, h1, hlim⟩ := limit_core hEntry hSubseq hS M Th (fun j => (hTh j).1)
    (fun j => (hTh j).2.1) (fun j => (hTh j).2.2.1) (fun j => (hTh j).2.2.2.2.1)
  have h2 : ∀ x, IsPSD F (Θ x) := fun x =>
    hClosed _ F (fun j => Th (φ j) x) (Θ x) (fun j => (hTh _).2.1 x) (hlim x)
  have h3 : ∀ x, x ∉ (Lc : Set K) → ∀ h ∈ F, ∀ h' ∈ F, Θ x h h' = 0 := by
    intro x hx h hh h' hh'
    have := hlim x h hh h' hh'
    simp only [(hTh _).2.2.1 x hx h hh h' hh'] at this
    exact tendsto_nhds_unique tendsto_const_nhds this |>.symm
  have h4 : ∀ t : Kˣ, IsPSD F (fun h h' => Θ (t : K) h h' - Ns R ψ (s + 1) h h' t t) := by
    intro t
    obtain ⟨j0, hj0⟩ := hex t
    have hmono' : ∀ j, j0 ≤ j → (t : K) ∈ Om j := by
      intro j hj
      induction j, hj using Nat.le_induction with
      | base => exact hj0
      | succ j _ ih => exact hmono j ih
    refine hClosed _ F (fun j h h' => Th (φ (j + j0)) (t : K) h h' - Ns R ψ (s + 1) h h' t t) _
      (fun j => (hTh _).2.2.2.1 t (hmono' _ ((Nat.le_add_left _ _).trans hφ.le_apply))) ?_
    intro h hh h' hh'
    exact ((hlim (t : K) h hh h' hh').comp (tendsto_add_atTop_nat j0)).sub tendsto_const_nhds
  have h5 : IsPSD F (fun h h' => M h h' -
      ∑ᶠ y : K ⧸ R.toAddSubgroup, Θ (Quotient.out y) h h') := by
    refine hClosed _ F (fun j h h' => M h h' -
      ∑ᶠ y : K ⧸ R.toAddSubgroup, Th (φ j) (Quotient.out y) h h') _
      (fun j => (hTh _).2.2.2.2.1) ?_
    intro h hh h' hh'
    simp only [finsum_classes hS h3 hh hh', finsum_classes hS ((hTh _).2.2.1) hh hh']
    exact tendsto_const_nhds.sub (tendsto_finsetSum _ fun y _ => hlim _ h hh h' hh')
  have h6 : ∀ x, ∀ h ∈ F, ∀ h' ∈ F, modK R (pt h.1 h.2).det ≠ modK R (pt h'.1 h'.2).det →
      Θ x h h' = 0 := by
    intro x h hh h' hh' hne
    have := hlim x h hh h' hh'
    simp only [(hTh _).2.2.2.2.2 x h hh h' hh' hne] at this
    exact tendsto_nhds_unique tendsto_const_nhds this |>.symm
  refine ⟨Θ, h1, h2, ⟨Lc, hLo, hLk, h3⟩, h4, h5, h6, ?_⟩
  intro hG x
  by_cases hx : x ∈ R
  · simp only [if_pos hx]
    refine psd_congr (psd_single hS h1 h2 h3 h5 x) ?_
    intro h hh h' hh'
    simp only [M, hCOne K R ψ hD h (hG h hh), hCOne K R ψ hD h' (hG h' hh')]
    simp
  · simp only [if_neg hx]
    refine psd_congr (psd_zero F) ?_
    intro h hh h' hh'
    rw [h3 x (fun hc => hx ((hGL hG x).1 hc)) h hh h' hh']
    simp
end Formalism.FourierDecayAlt.P
