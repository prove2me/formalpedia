-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.AdmissibleUnits.norm_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:08:52.793273+00:00
-- url     : https://prove2.me/submissions/935b119c-c50e-4213-add0-42e8b027d925

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_DedekindFactorK
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_UnitsEqOneOrNegOne
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_AdmissibleUnits_conj_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
open NumberField Classical
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.AdmissibleUnits
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.AdmissibleUnits
theorem _root_.solution (d : ℕ) (hd : 0 < d) (x : K) (hx : x ^ 2 = -(d : K)) (hK : Module.finrank ℚ K = 2)
    (φ : K →+* ℂ) (α : K) : ((Algebra.norm ℚ α : ℚ) : ℝ) = ‖φ α‖ ^ 2 := by
  set ψ : K →ₐ[ℚ] ℂ := φ.toRatAlgHom
  set ψ' : K →ₐ[ℚ] ℂ := ((starRingEnd ℂ).comp φ).toRatAlgHom
  have hne : ψ ≠ ψ' := by
    intro h
    have := congrArg (fun f : K →ₐ[ℚ] ℂ => f x) h
    simp only [ψ, ψ', RingHom.toRatAlgHom_apply, RingHom.comp_apply] at this
    exact conj_ne d hd x hx φ this.symm
  have hcard : Fintype.card (K →ₐ[ℚ] ℂ) = 2 := by rw [AlgHom.card, hK]
  have huniv : (Finset.univ : Finset (K →ₐ[ℚ] ℂ)) = {ψ, ψ'} := by
    symm; apply Finset.eq_univ_of_card
    rw [Finset.card_pair hne, hcard]
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ α
  rw [huniv, Finset.prod_pair hne] at h
  simp only [ψ, ψ', RingHom.toRatAlgHom_apply, RingHom.comp_apply] at h
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
  have h' : (((Algebra.norm ℚ α : ℚ) : ℝ) : ℂ) = ((‖φ α‖ ^ 2 : ℝ) : ℂ) := by
    rw [← h]; simp
  exact_mod_cast h'
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.AdmissibleUnits
