-- Prove2me | solution 1 for Formalism.L2.Th1.F.S2IsogenyPsi.hasDerivAt_psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:25:02.493879+00:00
-- url     : https://prove2.me/submissions/449c3377-fbd2-48ba-a347-1e608e78f7e4

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_QuasiPeriodConstIsogeny
import Theorems.Thm_Formalism_L2_Th1_F_S2IsogenyPsi_notMem_of_dom
import Theorems.Thm_Formalism_L2_Th1_F_S2IsogenyPsi_add_dom

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
open Formalism.L2.Th1.F.S2IsogenyPsi
namespace Formalism.L2.Th1.F.S2IsogenyPsi
theorem _root_.solution (hP : IsogenyP) (hd : ZetaHasDeriv) (L : PeriodPair) (α : ℂ) (S : Finset ℂ)
    (hα : α ≠ 0) (hst : MulStable L α) (hS : IsKerReps L α S) (z : ℂ) (hz : α * z ∉ L.lattice) :
    HasDerivAt (psi L α S) 0 z := by
  have hz0 : z ∉ L.lattice := notMem_of_dom hst hz
  have hA : HasDerivAt (fun w => α * wZeta L (α * w)) (α * (-(L.weierstrassP (α * z)) * (α * 1))) z :=
    ((hd L (α * z) hz).comp z ((hasDerivAt_id' z).const_mul α)).const_mul α
  have hB : HasDerivAt (wZeta L) (-(L.weierstrassP z)) z := hd L z hz0
  have hC : HasDerivAt (fun w => ∑ P ∈ S, wZeta L (w + P)) (∑ P ∈ S, -(L.weierstrassP (z + P))) z := by
    have hC' : ∀ P ∈ S, HasDerivAt (fun w => wZeta L (w + P)) (-(L.weierstrassP (z + P))) z := by
      intro P hPS
      have hPz : z + P ∉ L.lattice := notMem_of_dom hst (add_dom (hS.1 P hPS).1 hz)
      exact (hd L (z + P) hPz).comp_add_const z P
    first
      | exact HasDerivAt.fun_sum hC'
      | (have h5 := HasDerivAt.sum hC'
         rw [Finset.sum_fn] at h5
         exact h5)
  have hD : HasDerivAt (fun w => (∑ P ∈ S, L.weierstrassP P) * w) ((∑ P ∈ S, L.weierstrassP P) * 1) z :=
    (hasDerivAt_id' z).const_mul _
  have hall := ((hA.sub hB).sub hC).sub hD
  have hiso := hP L α S hα hst hS z hz
  rw [Finset.sum_sub_distrib] at hiso
  rw [Finset.sum_neg_distrib] at hall
  first
    | (refine hall.congr_deriv ?_
       linear_combination -hiso)
    | (convert hall using 1
       linear_combination hiso)
end Formalism.L2.Th1.F.S2IsogenyPsi
