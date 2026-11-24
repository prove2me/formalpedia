-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBA.psd_iff_qf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:20:35.475847+00:00
-- url     : https://prove2.me/submissions/830900da-a1a8-4dff-8e8a-39760a18dab2

import Definitions.Def_Formalism_HermitianCurvature_StatementKB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockOfCauchySchwarz

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBA
open Formalism.FourierDecayAlt
variable {α β : Type} (Y₁ : Finset α) (Y₂ : Finset β)
namespace Formalism.FourierDecayAlt.P.PBA
theorem _root_.solution {γ : Type} (Y : Finset γ) (k : γ → γ → ℂ) :
    TB.PSDOn Y k ↔ (∀ x ∈ Y, ∀ y ∈ Y, k y x = conj (k x y)) ∧ ∀ c, 0 ≤ (qf Y k c).re := by
  classical
  have hqf : ∀ c : γ → ℂ, qf Y k c = ∑ i : Y, ∑ j : Y, conj (c i) * k i j * c j := by
    intro c
    unfold qf
    rw [← Finset.sum_coe_sort Y]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_coe_sort Y]
  have hsum : ∀ x : Y →₀ ℂ,
      (x.sum fun i xi => x.sum fun j xj => star xi * Matrix.of (fun x y : Y => k x y) i j * xj) =
        ∑ i : Y, ∑ j : Y, conj (x i) * k i j * x j := by
    intro x
    rw [Finsupp.sum_fintype _ _ (fun i => by simp)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finsupp.sum_fintype _ _ (fun j => by simp)]
    rfl
  unfold TB.PSDOn Matrix.PosSemidef
  constructor
  · rintro ⟨hH, hpos⟩
    refine ⟨fun x hx y hy => ?_, fun c => ?_⟩
    · have h1 := hH.apply ⟨y, hy⟩ ⟨x, hx⟩
      exact h1.symm
    · have h2 := hpos (Finsupp.equivFunOnFinite.symm fun i : Y => c i)
      rw [hsum] at h2
      rw [hqf]
      simpa using (Complex.le_def.mp h2).1
  · rintro ⟨hh, hq⟩
    refine ⟨Matrix.IsHermitian.ext fun i j => ?_, fun x => ?_⟩
    · simp only [Matrix.of_apply]
      rw [hh j j.2 i i.2]
      rfl
    · rw [hsum]
      have hre := hq (fun g => if h : g ∈ Y then x ⟨g, h⟩ else 0)
      rw [hqf] at hre
      have hc : ∀ i : Y, (if h : (i : γ) ∈ Y then x ⟨i, h⟩ else 0) = x i := fun i => by simp
      simp only [hc] at hre
      have him : (∑ i : Y, ∑ j : Y, conj (x i) * k i j * x j).im = 0 := by
        rw [← Complex.conj_eq_iff_im]
        simp only [map_sum, map_mul, Complex.conj_conj]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [hh i i.2 j j.2, Complex.conj_conj]
        ring
      exact Complex.le_def.mpr ⟨by simpa using hre, by rw [Complex.zero_im, him]⟩
end Formalism.FourierDecayAlt.P.PBA
