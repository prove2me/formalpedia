-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.unfolding_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:25.392873+00:00
-- url     : https://prove2.me/submissions/a4c025f4-a649-4631-87b5-60316460dbaf

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_relIndex_eq_ncard
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_mem_orbit_sub
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_ncard_conj
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_fiber_sum
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
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution : UnfoldSym := by
  intro G X _ _ μ m hμ hidx hsym hinv hfin x y
  classical
  have hfA : (MulAction.orbit G y ∩ Function.support (m x)).Finite := (hfin x).subset fun z hz => hz.2
  have hfB : (MulAction.orbit G x ∩ Function.support (m y)).Finite := (hfin y).subset fun z hz => hz.2
  rw [finsum_mem_eq_sum _ hfA, finsum_mem_eq_sum _ hfB]
  set A := hfA.toFinset with hA
  set B := hfB.toFinset with hB
  have memA : ∀ z, z ∈ A ↔ z ∈ MulAction.orbit G y ∧ m x z ≠ 0 := fun z => by simp [hA]
  have memB : ∀ z, z ∈ B ↔ z ∈ MulAction.orbit G x ∧ m y z ≠ 0 := fun z => by simp [hB]
  let R : X → X → Prop := fun z z' => ∃ g : G, g • y = z ∧ g⁻¹ • x = z'
  have hm : ∀ z z', R z z' → m x z = m y z' := by
    rintro _ _ ⟨g, rfl, rfl⟩
    rw [hsym y, ← hinv g⁻¹ x (g • y)]; simp
  have hRA : ∀ z z', R z z' → {w' | R z w'} = MulAction.orbit (MulAction.stabilizer G y) z' := by
    rintro _ _ ⟨g, rfl, rfl⟩
    ext w'
    simp only [Set.mem_ofPred_eq, mem_orbit_sub, MulAction.mem_stabilizer_iff]
    constructor
    · rintro ⟨g', h1, rfl⟩
      refine ⟨g'⁻¹ * g, ?_, by simp [mul_smul]⟩
      rw [mul_smul, ← h1]; simp
    · rintro ⟨k, hk, rfl⟩
      refine ⟨g * k⁻¹, ?_, by simp [mul_smul]⟩
      rw [mul_smul]
      congr 1
      rw [inv_smul_eq_iff, hk]
  have hRB : ∀ z z', R z z' → {w | R w z'} = MulAction.orbit (MulAction.stabilizer G x) z := by
    rintro _ _ ⟨g, rfl, rfl⟩
    ext w
    simp only [Set.mem_ofPred_eq, mem_orbit_sub, MulAction.mem_stabilizer_iff]
    constructor
    · rintro ⟨g', rfl, h1⟩
      refine ⟨g' * g⁻¹, ?_, by simp [mul_smul]⟩
      rw [mul_smul, ← h1]; simp
    · rintro ⟨k, hk, rfl⟩
      refine ⟨k * g, by simp [mul_smul], ?_⟩
      rw [mul_inv_rev, mul_smul]
      congr 1
      rw [inv_smul_eq_iff, hk]
  have hbal : ∀ z z', R z z' →
      μ x * ((MulAction.orbit (MulAction.stabilizer G x) z).ncard : ℝ)
        = μ y * ((MulAction.orbit (MulAction.stabilizer G y) z').ncard : ℝ) := by
    rintro _ _ ⟨g, rfl, rfl⟩
    have := hidx x (g • y)
    rw [relIndex_eq_ncard, relIndex_eq_ncard, hμ, ncard_conj] at this
    exact this
  have hAB : ∀ z z', R z z' → (z ∈ A ↔ z' ∈ B) := by
    intro z z' hR
    rw [memA, memB, hm z z' hR]
    obtain ⟨g, rfl, rfl⟩ := hR
    simp [MulAction.mem_orbit]
  have cA : ∀ z ∈ A, ∀ z' ∈ B, R z z' →
      (B.filter (R z)).card = (MulAction.orbit (MulAction.stabilizer G y) z').ncard := by
    intro z hz z' _ hR
    rw [← hRA z z' hR, ← Set.ncard_coe_finset]
    congr 1
    ext w'
    simp only [Finset.coe_filter, Set.mem_ofPred_eq]
    exact ⟨fun h => h.2, fun h => ⟨(hAB z w' h).1 hz, h⟩⟩
  have cB : ∀ z' ∈ B, ∀ z ∈ A, R z z' →
      (A.filter (fun w => R w z')).card = (MulAction.orbit (MulAction.stabilizer G x) z).ncard := by
    intro z' hz' z _ hR
    rw [← hRB z z' hR, ← Set.ncard_coe_finset]
    congr 1
    ext w
    simp only [Finset.coe_filter, Set.mem_ofPred_eq]
    exact ⟨fun h => h.2, fun h => ⟨(hAB w z' h).2 hz', h⟩⟩
  have eA : ∀ z ∈ A, ∃ z' ∈ B, R z z' := by
    intro z hz
    obtain ⟨g, rfl⟩ := ((memA z).1 hz).1
    have hR : R (g • y) (g⁻¹ • x) := ⟨g, rfl, rfl⟩
    exact ⟨_, (hAB _ _ hR).1 hz, hR⟩
  have eB : ∀ z' ∈ B, ∃ z ∈ A, R z z' := by
    intro z' hz'
    obtain ⟨g, rfl⟩ := ((memB z').1 hz').1
    have hR : R (g⁻¹ • y) (g • x) := ⟨g⁻¹, rfl, by simp⟩
    exact ⟨_, (hAB _ _ hR).2 hz', hR⟩
  rw [Finset.mul_sum, Finset.mul_sum,
    fiber_sum A B R (fun z => μ x * m x z) _ eA cA,
    fiber_sum B A (fun z' z => R z z') (fun z' => μ y * m y z') _ eB cB]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z' hz' => Finset.sum_congr rfl fun z hz => ?_
  split_ifs with hR
  · have h1 := hbal z z' hR
    have n1 : ((MulAction.orbit (MulAction.stabilizer G y) z').ncard : ℝ) ≠ 0 := by
      rw [← cA z hz z' hz' hR]
      have : 0 < (B.filter (R z)).card := Finset.card_pos.2 ⟨z', Finset.mem_filter.2 ⟨hz', hR⟩⟩
      exact_mod_cast this.ne'
    have n2 : ((MulAction.orbit (MulAction.stabilizer G x) z).ncard : ℝ) ≠ 0 := by
      rw [← cB z' hz' z hz hR]
      have : 0 < (A.filter (fun w => R w z')).card := Finset.card_pos.2 ⟨z, Finset.mem_filter.2 ⟨hz, hR⟩⟩
      exact_mod_cast this.ne'
    rw [hm z z' hR, div_eq_div_iff n1 n2]
    linear_combination (m y z') * h1
  · rfl
end Formalism.HermitianLatticeCounting.P.S4aux
