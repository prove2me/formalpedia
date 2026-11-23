-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.kernel_gram_property
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:54:44.823705+00:00
-- url     : https://prove2.me/submissions/b585fc46-4ea6-42e3-871d-d435fadc3643

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Theorems.Thm_Formalism_FourierDecayAlt_P_integral_points_finite
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x4_Kp_eq_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x4_isoZZ_refl
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x4_isoZZ_symm
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x4_isoZZ_trans
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x4_card_isoZZ_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x4_psd_of_rel
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val



set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A5x4
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.A5.KpGram := by
  intro K _ _ _ R ψ hL F a
  classical
  have hfin := integral_points_finite K R ψ hL
  let I : ∀ x : Point K, Finset (Cos R x) := fun x => (hfin x).toFinset
  let S : Finset (Σ x : Point K, Cos R x) := F.sigma I
  let c : (Σ x : Point K, Cos R x) → ℂ := fun i => a i.1 * phase ψ (rep R i.2)
  let N : (Σ x : Point K, Cos R x) → (Σ x : Point K, Cos R x) → ℕ :=
    fun i j => Nat.card (isoZZ R (orbZ i.1 (rep R i.2)) (orbZ j.1 (rep R j.2)))
  have hsum : ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * Kp R ψ x y =
      ∑ i : S, ∑ j : S, c i * conj (c j) * (N i j : ℂ) := by
    rw [Finset.sum_coe_sort S (fun i => ∑ j : S, c i * conj (c j) * (N i j : ℂ))]
    have hin : ∀ i, ∑ j : S, c i * conj (c j) * (N i j : ℂ) =
        ∑ y ∈ F, ∑ q' ∈ I y, c i * conj (c ⟨y, q'⟩) * (N i ⟨y, q'⟩ : ℂ) := by
      intro i
      rw [Finset.sum_coe_sort S (fun j => c i * conj (c j) * (N i j : ℂ)), Finset.sum_sigma]
    rw [Finset.sum_congr rfl fun i _ => hin i, Finset.sum_sigma]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Kp_eq_sum R ψ x y (hfin x) (hfin y), Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q' _ => ?_
    simp only [c, N, map_mul]
    ring
  rw [hsum]
  let r : Setoid S :=
    { r := fun i j => (isoZZ R (orbZ i.1.1 (rep R i.1.2)) (orbZ j.1.1 (rep R j.1.2))).Nonempty
      iseqv := ⟨fun i => ⟨_, isoZZ_refl R _⟩, fun ⟨_, h⟩ => ⟨_, isoZZ_symm R h⟩,
        fun ⟨_, h⟩ ⟨_, h'⟩ => ⟨_, isoZZ_trans R h h'⟩⟩ }
  refine psd_of_rel r (fun i j => N i j) ?_ ?_ (fun i => c i)
  · intro i j h
    have h' : isoZZ R (orbZ i.1.1 (rep R i.1.2)) (orbZ j.1.1 (rep R j.1.2)) = ∅ :=
      Set.not_nonempty_iff_eq_empty.1 h
    simp only [N]
    rw [h']
    simp
  · rintro i j k ⟨φ, hφ⟩ ⟨φ', hφ'⟩
    exact card_isoZZ_congr R hφ' (isoZZ_trans R (isoZZ_symm R hφ) hφ')
end Formalism.FourierDecayAlt.P
