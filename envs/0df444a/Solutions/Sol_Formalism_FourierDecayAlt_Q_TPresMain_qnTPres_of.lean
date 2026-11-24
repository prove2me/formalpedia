-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TPresMain.qnTPres_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:14:21.336798+00:00
-- url     : https://prove2.me/submissions/0c8f0f9b-7def-47cf-91fd-1df4a2bfbe48

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_ExpSecondHermitianMemLevel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_SecondCapelliMinorContinuousLinear
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_tl_smooth
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_tl_local
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_tl_clm
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_one_mem_UW
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_one_mem_Nlev
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.Q.TPresMain
open Formalism.REAL Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TPresLie
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {i : Fin (r + 1)} {D : Set (Mx k r)}
section Ops
variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
end Ops
private lemma mul_mem_Slev_of_mem_UWset_of_mem_Nlev {z : (Fin (2 * r + k + 1) → ℂ)} {h m : Mx k r} (hh : h ∈ UWset k r z)
    (hm : m ∈ Nlev k r i) : h * m ∈ Slev k r z i := by
  simp only [Slev, Set.mem_setOf_eq]
  exact ⟨h, hh, m, hm, rfl⟩
end Formalism.FourierDecayAlt.Q.TPresMain
end
end

set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TPresMain
open Formalism.REAL Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TPresLie
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {i : Fin (r + 1)} {D : Set (Mx k r)}
namespace Formalism.FourierDecayAlt.Q.TPresMain
theorem _root_.solution (hT : TInvariant) : TPreservesFF := by
  intro Wp Wq _ _ _ _ k r z z' π π' i D Y p q hz hz' hDom J hJ
  simp only [FFl, Set.mem_setOf_eq] at hJ ⊢
  obtain ⟨hs, hL, hR, hW⟩ := hJ
  have hD : IsOpen D := hDom.1
  refine ⟨tl_smooth hD z z' Y p q J hs, ?_, ?_, ?_⟩
  · intro g hg n hn
    have e := hT (Wq →L[ℂ] Wp) k r z z' i D J Y p q hz hz' hDom hs (1 * n) (mul_mem_Slev_of_mem_UWset_of_mem_Nlev (one_mem_UW z) hn)
      (1 * 1) (mul_mem_Slev_of_mem_UWset_of_mem_Nlev (one_mem_UW z') one_mem_Nlev) g hg
    simp only [one_mul, mul_one] at e
    have hloc : ∀ x ∈ Glev k r i ∩ D,
        J (n * x) = (psi k r z cStd n • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) (J x) := by
      intro x hx
      rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
      exact hL x hx n hn
    rw [← e, tl_local hD z z' Y p q _ _ hloc g hg, tl_clm hD z z' Y p q _ J hs g hg,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
  · intro g hg n hn
    have e := hT (Wq →L[ℂ] Wp) k r z z' i D J Y p q hz hz' hDom hs (1 * 1) (mul_mem_Slev_of_mem_UWset_of_mem_Nlev (one_mem_UW z) one_mem_Nlev)
      (1 * n) (mul_mem_Slev_of_mem_UWset_of_mem_Nlev (one_mem_UW z') hn) g hg
    simp only [one_mul, mul_one] at e
    have hloc : ∀ x ∈ Glev k r i ∩ D,
        J (x * n) = (psi k r z' cStd n • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) (J x) := by
      intro x hx
      rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
      exact hR x hx n hn
    rw [← e, tl_local hD z z' Y p q _ _ hloc g hg, tl_clm hD z z' Y p q _ J hs g hg,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
  · intro g hg h hh h' hh'
    have e := hT (Wq →L[ℂ] Wp) k r z z' i D J Y p q hz hz' hDom hs (h * 1) (mul_mem_Slev_of_mem_UWset_of_mem_Nlev hh one_mem_Nlev)
      (h' * 1) (mul_mem_Slev_of_mem_UWset_of_mem_Nlev hh' one_mem_Nlev) g hg
    simp only [mul_one] at e
    obtain ⟨L, hLx⟩ : ∃ L : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp), ∀ A, L A = (π h).comp (A.comp (π' h')) :=
      ⟨(ContinuousLinearMap.compL ℂ Wq Wp Wp (π h)).comp ((ContinuousLinearMap.compL ℂ Wq Wq Wp).flip (π' h')),
        fun A => by simp⟩
    have hloc : ∀ x ∈ Glev k r i ∩ D, J (h * x * h') = L (J x) := by
      intro x hx
      rw [hLx]
      exact hW x hx h hh h' hh'
    rw [← e, tl_local hD z z' Y p q _ _ hloc g hg, tl_clm hD z z' Y p q L J hs g hg, hLx]
end Formalism.FourierDecayAlt.Q.TPresMain
