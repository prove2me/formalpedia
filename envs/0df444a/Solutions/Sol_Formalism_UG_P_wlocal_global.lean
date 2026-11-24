-- Prove2me | solution 1 for Formalism.UG.P.wlocal_global
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:45:16.473456+00:00
-- url     : https://prove2.me/submissions/e43d5910-79d0-4e93-bb80-daceb98ee22b

import Definitions.Def_Formalism_SatakeDualWeyl_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
import Theorems.Thm_Formalism_UG_P_wlocal_local
import Theorems.Thm_Formalism_UG_P_wlocal_map_weyl
import Theorems.Thm_Formalism_UG_P_wlocal_map_rowAct
import Theorems.Thm_Formalism_UG_P_wlocal_loc
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Formalism.GradedWeylDivisibility
namespace Formalism.UG.P
theorem _root_.solution : Formalism.UG.WeylGLStable := by
  intro R _ r n hn ν g f hf
  obtain ⟨J, hJdef⟩ : ∃ J : Ideal R,
      J = Submodule.comap (LinearMap.toSpanSingleton R _ (dwAct R r n g f)) (weyl R r n hn ν) := ⟨_, rfl⟩
  have hJ : J = ⊤ := by
    by_contra hne
    obtain ⟨P, hPmax, hJP⟩ := Ideal.exists_le_maximal J hne
    haveI := hPmax.isPrime
    have hf' := wlocal_map_weyl (algebraMap R (Localization.AtPrime P)) hn ν f hf
    have hloc := wlocal_local (Localization.AtPrime P) r n hn ν
      (Units.map (algebraMap R (Localization.AtPrime P)).mapMatrix.toMonoidHom g) _ hf'
    have hg : ((Units.map (algebraMap R (Localization.AtPrime P)).mapMatrix.toMonoidHom g)⁻¹ :
        GL (Fin r) (Localization.AtPrime P)).val =
        (g⁻¹ : GL (Fin r) R).val.map (algebraMap R (Localization.AtPrime P)) := by
      first
      | rfl
      | simp [Units.coe_map_inv, RingHom.mapMatrix_apply]
    have hmem : map (algebraMap R (Localization.AtPrime P)) (dwAct R r n g f) ∈
        weyl (Localization.AtPrime P) r n hn ν := by
      unfold dwAct at hloc ⊢
      rw [hg, ← wlocal_map_rowAct] at hloc
      exact hloc
    obtain ⟨t, ht, hty⟩ := wlocal_loc P hn ν _ hmem
    have htJ : t ∈ J := by
      rw [hJdef, Submodule.mem_comap, LinearMap.toSpanSingleton_apply, MvPolynomial.smul_eq_C_mul]
      exact hty
    exact (Ideal.mem_primeCompl_iff.mp ht) (hJP htJ)
  have h1 : (1 : R) ∈ J := by
    rw [hJ]
    exact Submodule.mem_top
  rw [hJdef, Submodule.mem_comap, LinearMap.toSpanSingleton_apply, one_smul] at h1
  exact h1
end Formalism.UG.P
