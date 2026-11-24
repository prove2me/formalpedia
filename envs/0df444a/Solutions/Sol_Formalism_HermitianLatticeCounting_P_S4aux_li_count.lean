-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.li_count
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:33.457899+00:00
-- url     : https://prove2.me/submissions/2c789efa-9500-403f-ab9a-3c95ebb0c53f

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_dep_card
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
    (hc : ∀ j, (Fs j).card = c) (hc0 : 0 < c)
    [DecidablePred fun Y : Fin m → Fin n → F => LinearIndependent F Y] :
    (((Fintype.piFinset Fs).filter fun Y => LinearIndependent F Y).card : ℝ) ≤ (c : ℝ) ^ m ∧
    (c : ℝ) ^ m - (Fintype.card F : ℝ) ^ m * (c : ℝ) ^ m / c
      ≤ (((Fintype.piFinset Fs).filter fun Y => LinearIndependent F Y).card : ℝ) := by
  have htot : (Fintype.piFinset Fs).card = c ^ m := by
    rw [Fintype.card_piFinset]; simp [hc]
  have hsplit := Finset.card_filter_add_card_filter_not (s := Fintype.piFinset Fs)
    (fun Y => LinearIndependent F Y)
  have hdep := dep_card Fs c hc
  have hdepR : (((Fintype.piFinset Fs).filter fun Y => ¬ LinearIndependent F Y).card : ℝ)
      ≤ (Fintype.card F : ℝ) ^ m * (c : ℝ) ^ m / c := by
    rw [le_div_iff₀ (by exact_mod_cast hc0)]
    exact_mod_cast hdep
  have hsR : (((Fintype.piFinset Fs).filter fun Y => LinearIndependent F Y).card : ℝ)
      + (((Fintype.piFinset Fs).filter fun Y => ¬ LinearIndependent F Y).card : ℝ) = (c : ℝ) ^ m := by
    rw [htot] at hsplit
    exact_mod_cast hsplit
  constructor
  · have : (0 : ℝ) ≤ (((Fintype.piFinset Fs).filter fun Y => ¬ LinearIndependent F Y).card : ℝ) :=
      Nat.cast_nonneg _
    linarith
  · linarith
end Formalism.HermitianLatticeCounting.P.S4aux
