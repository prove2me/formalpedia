-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.massTelescope_trace_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:46:15.525037+00:00
-- url     : https://prove2.me/submissions/82dba5b5-df57-40b9-9d56-18f80b2a994b

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassTelescope
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable (K : Type) [Field K] [NumberField K] [StarRing K]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (hCM : IsCMUnram K) (a : K) (ha : a ≠ 0) :
    0 < Algebra.trace ℚ K (star a * a) := by
  haveI : Nonempty (K →ₐ[ℚ] ℂ) := ⟨IsAlgClosed.lift⟩
  have key : ∀ σ : K →ₐ[ℚ] ℂ, σ (star a * a) = ((Complex.normSq (σ a) : ℝ) : ℂ) := by
    intro σ
    have h1 : σ (star a) = starRingEnd ℂ (σ a) := hCM.2.1 (σ : K →+* ℂ) a
    rw [map_mul, h1]
    exact Complex.normSq_eq_conj_mul_self.symm
  have hE : algebraMap ℚ ℂ (Algebra.trace ℚ K (star a * a)) =
      ∑ σ : K →ₐ[ℚ] ℂ, σ (star a * a) := by
    first
    | exact trace_eq_sum_embeddings ℂ
    | exact trace_eq_sum_embeddings (E := ℂ)
    | exact Algebra.trace_eq_sum_embeddings ℂ
  simp only [key] at hE
  rw [eq_ratCast (algebraMap ℚ ℂ)] at hE
  have hR := congrArg Complex.re hE
  simp only [Complex.ratCast_re, Complex.re_sum, Complex.ofReal_re] at hR
  have hpos : (0 : ℝ) < ((Algebra.trace ℚ K (star a * a) : ℚ) : ℝ) := by
    rw [hR]
    exact Finset.sum_pos (fun σ _ => Complex.normSq_pos.mpr ((map_ne_zero σ).mpr ha))
      Finset.univ_nonempty
  exact_mod_cast hpos
end Formalism.HermitianLatticesTheory
