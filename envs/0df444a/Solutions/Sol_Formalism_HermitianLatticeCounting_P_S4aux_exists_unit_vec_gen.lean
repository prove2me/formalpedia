-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.exists_unit_vec_gen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:03.986825+00:00
-- url     : https://prove2.me/submissions/bf5bd6d1-c049-492c-b9d6-39aa0a8f4582

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_det_mul_eq_zero_of_card_lt
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_orth_pair_right
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_orth_pair_gen
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_orth_pair_left
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_orth_proj
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_gram_unit
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
variable {o O : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
  [Algebra o O] {abelian₂ : Type} [AddCommGroup abelian₂] [Module O abelian₂] [Module.Free O abelian₂]
  [Module.Finite O abelian₂] (h : abelian₂ →ₗ[O] abelian₂ →ₗ⋆[O] O)
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution [Nontrivial O] (J : Ideal O) (hJ : ∀ x ∈ J, ¬ IsUnit x)
    (hpol : ∀ C : Submodule O abelian₂, (∀ c ∈ C, ¬ IsUnit (h c c)) → ∀ c ∈ C, ∀ c' ∈ C, h c c' ∈ J)
    (hSD : SelfDual h) {κ : Type} [Fintype κ] (v : κ → abelian₂)
    (horth : ∀ i j, i ≠ j → h (v i) (v j) = 0) (hunit : ∀ i, IsUnit (h (v i) (v i)))
    (hk : Fintype.card κ < Module.finrank O abelian₂) : ∃ c, (∀ i, h c (v i) = 0) ∧ IsUnit (h c c) := by
  classical
  by_contra hcon
  push Not at hcon
  have hH := hSD.1
  let C : Submodule O abelian₂ :=
    { carrier := {c | ∀ i, h c (v i) = 0}
      add_mem' := fun {a b} ha hb i => by rw [map_add, LinearMap.add_apply, ha i, hb i, add_zero]
      zero_mem' := fun i => by simp
      smul_mem' := fun r c hc i => by rw [map_smul, LinearMap.smul_apply, hc i, smul_zero] }
  have hCJ := hpol C (fun c hc => hcon c hc)
  let b := Module.Free.chooseBasis O abelian₂
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex O abelian₂) = Module.finrank O abelian₂ :=
    (Module.finrank_eq_card_chooseBasisIndex O abelian₂).symm
  choose u hu using hunit
  let a : Module.Free.ChooseBasisIndex O abelian₂ → κ → O := fun i j => h (b i) (v j) * ((u j)⁻¹ : Oˣ)
  let cc : Module.Free.ChooseBasisIndex O abelian₂ → abelian₂ := fun i => b i - ∑ j, a i j • v j
  have hcc : ∀ i, cc i ∈ C := fun i j => orth_proj h v horth u hu (b i) j
  have hbi : ∀ i, b i = cc i + ∑ j, a i j • v j := fun i => by simp [cc]
  have hG : ∀ i l, h (b i) (b l) = ∑ j, a i j * ((u j : O) * star (a l j)) + h (cc i) (cc l) := by
    intro i l
    have e1 : h (cc i) (∑ j, a l j • v j) = 0 := by
      rw [orth_pair_gen]; exact Finset.sum_eq_zero fun j _ => by rw [hcc i j, mul_zero]
    have e2 : h (∑ j, a i j • v j) (cc l) = 0 := by
      rw [orth_pair_left]
      exact Finset.sum_eq_zero fun j _ => by rw [hH (cc l) (v j), hcc l j, star_zero, mul_zero]
    have e3 : h (∑ j, a i j • v j) (∑ j, a l j • v j) = ∑ j, a i j * ((u j : O) * star (a l j)) := by
      rw [orth_pair_left]
      exact Finset.sum_congr rfl fun j _ => by rw [orth_pair_right h v horth, hu, mul_comm (star _)]
    conv_lhs => rw [hbi i, hbi l]
    rw [map_add (h _), map_add h, LinearMap.add_apply, LinearMap.add_apply, e1, e2, e3]
    ring
  have hdet := gram_unit h hSD
  apply hJ _ _ hdet
  rw [← Ideal.Quotient.eq_zero_iff_mem, RingHom.map_det]
  let A : Matrix (Module.Free.ChooseBasisIndex O abelian₂) κ O := Matrix.of a
  let B : Matrix κ (Module.Free.ChooseBasisIndex O abelian₂) O :=
    Matrix.of fun j l => (u j : O) * star (a l j)
  have hmap : (Ideal.Quotient.mk J).mapMatrix (Matrix.of fun i l => h (b i) (b l))
      = (A.map (Ideal.Quotient.mk J)) * (B.map (Ideal.Quotient.mk J)) := by
    rw [← Matrix.map_mul]
    ext i l
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply, A, B]
    rw [hG i l, map_add, (Ideal.Quotient.eq_zero_iff_mem).2 (hCJ _ (hcc i) _ (hcc l)), add_zero]
  rw [hmap]
  apply det_mul_eq_zero_of_card_lt
  rw [hcard]
  exact hk
end Formalism.HermitianLatticeCounting.P.S4aux
