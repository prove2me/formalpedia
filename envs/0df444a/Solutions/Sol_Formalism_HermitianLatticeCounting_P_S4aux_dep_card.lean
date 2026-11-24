-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.dep_card
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:29.269616+00:00
-- url     : https://prove2.me/submissions/b14d12bf-cc5a-4464-943b-5775f7836ba0

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_dep_one
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
variable {F : Type} [Field F] [Fintype F]
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution [DecidableEq F] {m n : ℕ} (Fs : Fin m → Finset (Fin n → F)) (c : ℕ)
    (hc : ∀ j, (Fs j).card = c) [DecidablePred fun Y : Fin m → Fin n → F => LinearIndependent F Y] :
    ((Fintype.piFinset Fs).filter fun Y => ¬ LinearIndependent F Y).card * c
      ≤ Fintype.card F ^ m * c ^ m := by
  have hsub : ((Fintype.piFinset Fs).filter fun Y => ¬ LinearIndependent F Y)
      ⊆ (univ.filter fun lam : Fin m → F => lam ≠ 0).biUnion
          fun lam => (Fintype.piFinset Fs).filter fun Y => ∑ j, lam j • Y j = 0 := by
    intro Y hY
    obtain ⟨hY1, hY2⟩ := Finset.mem_filter.1 hY
    obtain ⟨lam, hl, i, hi⟩ := Fintype.not_linearIndependent_iff.1 hY2
    rw [Finset.mem_biUnion]
    refine ⟨lam, ?_, Finset.mem_filter.2 ⟨hY1, hl⟩⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro h; exact hi (by rw [h]; rfl)
  calc _ ≤ (∑ lam ∈ univ.filter (fun lam : Fin m → F => lam ≠ 0),
        ((Fintype.piFinset Fs).filter fun Y => ∑ j, lam j • Y j = 0).card) * c :=
        Nat.mul_le_mul_right _ ((Finset.card_le_card hsub).trans Finset.card_biUnion_le)
    _ = ∑ lam ∈ univ.filter (fun lam : Fin m → F => lam ≠ 0),
        ((Fintype.piFinset Fs).filter fun Y => ∑ j, lam j • Y j = 0).card * c := Finset.sum_mul _ _ _
    _ ≤ ∑ lam ∈ univ.filter (fun lam : Fin m → F => lam ≠ 0), c ^ m := by
        refine Finset.sum_le_sum fun lam hl => ?_
        have hl' : lam ≠ 0 := (Finset.mem_filter.1 hl).2
        obtain ⟨j0, hj0⟩ := Function.ne_iff.1 hl'
        exact dep_one Fs c hc lam j0 hj0
    _ = (univ.filter (fun lam : Fin m → F => lam ≠ 0)).card * c ^ m := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ _ := by
        refine Nat.mul_le_mul_right _ ?_
        calc _ ≤ (univ : Finset (Fin m → F)).card := Finset.card_filter_le _ _
          _ = _ := by simp
end Formalism.HermitianLatticeCounting.P.S4aux
