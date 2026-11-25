-- Prove2me | solution 1 for Formalism.L2.S.Pv.SchurTens.SP_of_dense_b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:49:27.330387+00:00
-- url     : https://prove2.me/submissions/b3adc974-aab3-4509-8463-5cc1a7ab8fec

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_LimitMemLpAndIntegralEq
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_SchurTensSpan
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_SchurTensDense
import Theorems.Thm_Formalism_L2_S_Pv_SchurTens_continuous_coeff
import Theorems.Thm_Formalism_L2_S_Pv_SchurTens_memLp_of_diag
import Theorems.Thm_Formalism_L2_S_Pv_SchurTens_lintegral_of_diag
import Theorems.Thm_Formalism_L2_S_Pv_SchurTens_coeff_sub_b
import Theorems.Thm_Formalism_L2_S_Pv_SchurTens_small_of_close
import Theorems.Thm_Formalism_L2_S_Pv_SchurTens_limit_memLp_and_integral_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.SchurTens
open Formalism.L2.SG.Pf.EnergyAbs
variable {K : Type} [TopologicalSpace K] [MeasurableSpace K] [OpensMeasurableSpace K]
  {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
  {m : Measure K} {σs : K → (Hs →L[ℂ] Hs)} {D : ℝ}
namespace Formalism.L2.S.Pv.SchurTens
theorem _root_.solution (hstr : ∀ a : Hs, Continuous (fun x => σs x a)) (hD : 0 < D) (Sp : Submodule ℂ Hs)
    (hdense : Dense (Sp : Set Hs)) (a a' b' : Hs) (hB : ∀ b₀ ∈ Sp, SP m σs D a b₀ a' b')
    (hdiag : ∀ c ∈ Sp, SP m σs D a c a c) (hg : MemLp (coeff σs a' b') 2 m) (b : Hs) :
    SP m σs D a b a' b' ∧ MemLp (coeff σs a b) 2 m := by
  obtain ⟨u, hu_mem, hu⟩ := mem_closure_iff_seq_limit.1 (hdense b)
  have hf2 : ∀ n, MemLp (coeff σs a (u n)) 2 m := fun n =>
    memLp_of_diag hstr (hdiag _ (hu_mem n))
  have hFm : AEStronglyMeasurable (coeff σs a b) m :=
    (continuous_coeff hstr a b).aestronglyMeasurable
  have hpt : ∀ x, Tendsto (fun n => coeff σs a (u n) x) atTop (𝓝 (coeff σs a b x)) := by
    intro x
    show Tendsto (fun n => ⟪u n, σs x a⟫_ℂ) atTop (𝓝 ⟪b, σs x a⟫_ℂ)
    exact hu.inner tendsto_const_nhds
  have hC : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ n ≥ N, ∀ k ≥ N,
      ∫⁻ x, ‖coeff σs a (u k) x - coeff σs a (u n) x‖ₑ ^ 2 ∂m ≤ ε := by
    intro ε hε
    obtain ⟨δ, hδ, hsmall⟩ := small_of_close (‖a‖ ^ 2) (sq_nonneg _) hD ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hu.cauchySeq δ hδ
    refine ⟨N, fun n hn k hk => ?_⟩
    have hsub : ∀ x, coeff σs a (u k) x - coeff σs a (u n) x =
        coeff σs a (u k - u n) x := fun x => congrFun (coeff_sub_b (σs := σs) a (u k) (u n)) x
    calc ∫⁻ x, ‖coeff σs a (u k) x - coeff σs a (u n) x‖ₑ ^ 2 ∂m
        = ∫⁻ x, ‖coeff σs a (u k - u n) x‖ₑ ^ 2 ∂m := by simp only [hsub]
      _ = ENNReal.ofReal (‖u k - u n‖ ^ 2 * ‖a‖ ^ 2 / D) := by
          rw [lintegral_of_diag hstr (hdiag _ (Sp.sub_mem (hu_mem k) (hu_mem n))),
            mul_comm (‖a‖ ^ 2)]
      _ ≤ ε := hsmall _ (norm_nonneg _) (by rw [← dist_eq_norm]; exact hN k hk n hn)
  have hL : Tendsto (fun n => ∫ x, coeff σs a (u n) x * conj (coeff σs a' b' x) ∂m) atTop
      (𝓝 (⟪a', a⟫_ℂ * ⟪b, b'⟫_ℂ / (D : ℂ))) := by
    have e : (fun n => ∫ x, coeff σs a (u n) x * conj (coeff σs a' b' x) ∂m) =
        fun n => ⟪a', a⟫_ℂ * ⟪u n, b'⟫_ℂ / (D : ℂ) := by
      funext n
      obtain ⟨-, he⟩ := hB _ (hu_mem n)
      exact he
    rw [e]
    have hin : Tendsto (fun n => ⟪u n, b'⟫_ℂ) atTop (𝓝 ⟪b, b'⟫_ℂ) := by
      exact hu.inner tendsto_const_nhds
    exact (hin.const_mul _).div_const _
  obtain ⟨hM, hI, hE⟩ := limit_memLp_and_integral_eq (fun n => coeff σs a (u n))
    (coeff σs a b) (coeff σs a' b') hf2 hFm hg hpt hC hL
  exact ⟨And.intro hI hE, hM⟩
end Formalism.L2.S.Pv.SchurTens
