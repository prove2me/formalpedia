-- Prove2me | solution 1 for Formalism.L2.Th1.F.sigmaLogDeriv_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:37:44.71281+00:00
-- url     : https://prove2.me/submissions/a55e9502-d09a-4888-ab68-bdeeddac7ac9

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaLog
import Theorems.Thm_Formalism_L2_Th1_F_SigmaLog_differentiable_wFactor
import Theorems.Thm_Formalism_L2_Th1_F_SigmaLog_wFactor_ne_zero
import Theorems.Thm_Formalism_L2_Th1_F_SigmaLog_logDeriv_wFactor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open SigmaLog
namespace Formalism.L2.Th1.F
theorem _root_.solution (h1 : SigmaProdLU) (h2 : SigmaSummable) (h3 : ZetaSummable) :
    SigmaLogDeriv := by
  intro L z hz
  have hne : ∀ l : L.lattice, z ≠ (l : ℂ) := fun l h => hz (h ▸ l.2)
  have hz0 : z ≠ 0 := fun h => hz (h ▸ L.lattice.zero_mem)
  set P : ℂ → ℂ := fun z => ∏' l : L.lattice, wFactor (l : ℂ) z with hP

  have hPne : P z ≠ 0 := by
    have := tprod_one_add_ne_zero_of_summable (f := fun l : L.lattice => wFactor (l : ℂ) z - 1)
      (fun l => by simpa using wFactor_ne_zero (hne l)) (h2 L z)
    simpa [hP] using this

  have hPd : DifferentiableOn ℂ P Set.univ := by
    have ht := hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp (h1 L)
    refine ht.differentiableOn (.of_forall fun s => ?_) isOpen_univ
    exact DifferentiableOn.fun_finsetProd fun i _ => (differentiable_wFactor _).differentiableOn
  have hPdz : DifferentiableAt ℂ P z := (hPd z (Set.mem_univ z)).differentiableAt Filter.univ_mem

  have hc : HasSum (fun l : L.lattice => if (l : ℂ) = 0 then 1 / z else 0) (1 / z) := by
    have : (fun l : L.lattice => if (l : ℂ) = 0 then 1 / z else 0)
        = fun l : L.lattice => if l = 0 then 1 / z else 0 := by
      funext l; simp
    rw [this]
    exact hasSum_ite_eq 0 (1 / z)
  have hs : HasSum (fun l : L.lattice => logDeriv (wFactor (l : ℂ)) z) (wZeta L z - 1 / z) := by
    have := (h3 L z).hasSum.sub hc
    have he : (fun l : L.lattice => logDeriv (wFactor (l : ℂ)) z)
        = fun l : L.lattice => (1 / (z - (l : ℂ)) + 1 / (l : ℂ) + z / (l : ℂ) ^ 2)
            - (if (l : ℂ) = 0 then 1 / z else 0) := by
      funext l
      exact logDeriv_wFactor (hne l)
    rw [he]
    exact this
  have hlog : logDeriv P z = wZeta L z - 1 / z := by
    have := logDeriv_tprod_eq_tsum (s := Set.univ) isOpen_univ (Set.mem_univ z)
      (f := fun (l : L.lattice) (z : ℂ) => wFactor (l : ℂ) z) (fun l => wFactor_ne_zero (hne l))
      (fun l => (differentiable_wFactor _).differentiableOn) hs.summable
      (h1 L).multipliableLocallyUniformlyOn hPne
    rw [hs.tsum_eq] at this
    exact this
  have hPderiv : HasDerivAt P ((wZeta L z - 1 / z) * P z) z := by
    have := hPdz.hasDerivAt
    rw [← hlog, logDeriv_apply, div_mul_cancel₀ _ hPne]
    exact this
  have := (hasDerivAt_id z).mul hPderiv
  have he : wZeta L z * wSigma L z = 1 * P z + id z * ((wZeta L z - 1 / z) * P z) := by
    simp only [wSigma, id, hP]
    field_simp
    ring
  rw [he]
  exact this
end Formalism.L2.Th1.F
