-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.Part2.tauHom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:49:04.444617+00:00
-- url     : https://prove2.me/submissions/e0120188-020a-4205-9d1a-cc81717b7c2c

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_Part2_inTh_add
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_Part2_inTh_smul
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_Part2_inTh_neg
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_cast
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_cast
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_last



set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
open Formalism.HermitianLatticeCounting.P.S4aux.Part2
namespace Formalism.HermitianLatticeCounting.P.S4aux.Part2
theorem _root_.solution (H : TauWell) : TauHom := by
  intro E _ _ V _ _ h O abelian₂ θ r f f' g g' a₁ a₁' a₂ a₂' a₃ a₃' w₁ w₂ c hL hI hg hg' hfg hfg' hadm hc l1 l2 l3
  obtain ⟨p1, q1, t1⟩ := l1
  obtain ⟨p2, q2, t2⟩ := l2
  obtain ⟨p3, q3, t3⟩ := l3
  set γ : Fin r → E := fun i => a₃ i - c * a₁ i - a₂ i with hγ
  set γ' : Fin r → E := fun i => a₃' i - c * a₁' i - a₂' i with hγ'
  have eξ : (∑ i, γ i • f i) = (∑ i, a₃ i • f i) - c • (∑ i, a₁ i • f i) - (∑ i, a₂ i • f i) := by
    simp only [hγ, sub_smul, mul_smul, Finset.sum_sub_distrib, Finset.smul_sum]
  have eξ' : (∑ i, γ' i • f' i) = (∑ i, a₃' i • f' i) - c • (∑ i, a₁' i • f' i) - (∑ i, a₂' i • f' i) := by
    simp only [hγ', sub_smul, mul_smul, Finset.sum_sub_distrib, Finset.smul_sum]
  have hξ : (∑ i, γ i • f i) ∈ abelian₂ := by
    have := abelian₂.sub_mem (abelian₂.sub_mem p3 (hL c hc _ p1)) p2
    rw [eξ]; convert this using 1; rw [smul_add]; abel
  have hξ' : (∑ i, γ' i • f' i) ∈ abelian₂ := by
    have := abelian₂.sub_mem (abelian₂.sub_mem q3 (hL c hc _ q1)) q2
    rw [eξ']; convert this using 1; rw [smul_add]; abel
  have coef : ∀ (F G : Fin r → V) (b : Fin r → E), (∀ i j, h (F i) (G j) = if i = j then 1 else 0) →
      ∀ j, h (∑ i, b i • F i) (G j) = b j := by
    intro F G b hFG j
    simp [map_sum, LinearMap.sum_apply, hFG]
  have hγ'O : ∀ i, γ' i ∈ O := fun i => by
    rw [← coef f' g' γ' hfg' i]; exact hI _ hξ' _ (hg' i)
  have hdiff : InTh (θ : E) abelian₂ ((∑ i, γ' i • f' i) - (∑ i, γ i • f i)) := by
    have := inTh_add (inTh_add t3 (inTh_neg (inTh_smul hL hc t1))) (inTh_neg t2)
    rw [eξ, eξ']; convert this using 1; rw [smul_sub]; abel
  have hw := H E V h O abelian₂ θ r f f' g γ γ' hL hI hg hfg hadm hγ'O hdiff
  choose d hdO hd using hw
  have key : ((θ⁻¹ : Eˣ) : E) • (((∑ i, a₃' i • f' i) - (∑ i, a₃ i • f i))
        - c • ((∑ i, a₁' i • f' i) - (∑ i, a₁ i • f i)) - ((∑ i, a₂' i • f' i) - (∑ i, a₂ i • f i)))
      = (∑ i, γ' i • (((θ⁻¹ : Eˣ) : E) • (f' i - f i))) + ∑ i, d i • f i := by
    have e1 : ((∑ i, a₃' i • f' i) - (∑ i, a₃ i • f i))
        - c • ((∑ i, a₁' i • f' i) - (∑ i, a₁ i • f i)) - ((∑ i, a₂' i • f' i) - (∑ i, a₂ i • f i))
        = (∑ i, γ' i • f' i) - (∑ i, γ i • f i) := by
      rw [eξ, eξ', smul_sub]; abel
    rw [e1, ← Finset.sum_sub_distrib, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hdi : d i = ((θ⁻¹ : Eˣ) : E) * (γ' i - γ i) := by
      rw [hd i, ← mul_assoc]; simp
    rw [hdi]
    module
  rw [key]
  refine Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => ?_) (Submodule.sum_mem _ fun i _ => ?_)
  · exact Submodule.smul_mem _ (⟨γ' i, hγ'O i⟩ : O) (Submodule.subset_span (Or.inr ⟨i, rfl⟩))
  · exact Submodule.smul_mem _ (⟨d i, hdO i⟩ : O) (Submodule.subset_span (Or.inl ⟨i, rfl⟩))
end Formalism.HermitianLatticeCounting.P.S4aux.Part2
