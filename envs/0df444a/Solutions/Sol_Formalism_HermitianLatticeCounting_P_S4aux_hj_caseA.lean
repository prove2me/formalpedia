-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.hj_caseA
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:39.816379+00:00
-- url     : https://prove2.me/submissions/46fd61af-9e1a-49f7-9746-57f4c8e0b1a7

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_hj_norm_star
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_det_congrE
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
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] [StarRing E]
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution (hs : ∀ c : F, star (algebraMap F E c) = algebraMap F E c)
    (h2 : Module.finrank F E = 2) (hfix : ∀ y : E, star y = y → ∃ c : F, algebraMap F E c = y)
    (ω : E) (β : Module.Basis (Fin 2) F E) (h0 : β 0 = 1) (h1 : β 1 = ω)
    (hδ : IsUnit (ω - star ω)) (m : ℕ) (A : Matrix (Fin m) (Fin m) E) :
    LinearMap.det (congrHerm F E hs m A) = Algebra.norm F A.det ^ m := by
  classical
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [h2]; norm_num)
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [h2]; norm_num)
  let b := Module.Free.chooseBasis F (hermSub F E hs m)
  let v : Module.Free.ChooseBasisIndex F (hermSub F E hs m) → Matrix (Fin m) (Fin m) E :=
    fun i => (b i : Matrix (Fin m) (Fin m) E)
  have hcoe : ∀ a : Module.Free.ChooseBasisIndex F (hermSub F E hs m) → F,
      ((∑ i, a i • b i : hermSub F E hs m) : Matrix (Fin m) (Fin m) E)
        = ∑ i, algebraMap F E (a i) • v i := by
    intro a
    rw [Submodule.coe_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Submodule.coe_smul, algebraMap_smul]
  have hherm : ∀ Y : hermSub F E hs m, (Y : Matrix (Fin m) (Fin m) E).conjTranspose = Y := fun Y => Y.2
  obtain ⟨u, hu⟩ := hδ
  have hli : LinearIndependent E v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    let H1 : hermSub F E hs m := ∑ i, β.repr (g i) 0 • b i
    let H2 : hermSub F E hs m := ∑ i, β.repr (g i) 1 • b i
    have e1 : (H1 : Matrix (Fin m) (Fin m) E) + ω • (H2 : Matrix (Fin m) (Fin m) E) = 0 := by
      rw [← hg, hcoe, hcoe, Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      conv_rhs => rw [hj_decomp β ω h0 h1 (g i)]
      rw [add_smul, smul_smul, mul_comm ω]
    have e2 : (H1 : Matrix (Fin m) (Fin m) E) + star ω • (H2 : Matrix (Fin m) (Fin m) E) = 0 := by
      have := congrArg Matrix.conjTranspose e1
      rwa [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hherm, hherm,
        Matrix.conjTranspose_zero] at this
    have e3 : (u : E) • (H2 : Matrix (Fin m) (Fin m) E) = 0 := by
      rw [hu, sub_smul]
      have := congrArg₂ (· - ·) e1 e2
      simpa using this
    have e4 : (H2 : Matrix (Fin m) (Fin m) E) = 0 := by
      have := congrArg (fun X => ((u⁻¹ : Eˣ) : E) • X) e3
      simpa [smul_smul] using this
    have e5 : (H1 : Matrix (Fin m) (Fin m) E) = 0 := by
      rw [e4, smul_zero, add_zero] at e1; exact e1
    have hb := Fintype.linearIndependent_iff.1 b.linearIndependent
    have z1 := hb _ (Subtype.ext e5 : H1 = 0)
    have z2 := hb _ (Subtype.ext e4 : H2 = 0)
    intro i
    rw [hj_decomp β ω h0 h1 (g i), z1 i, z2 i]
    simp
  have hmem : ∀ Y : hermSub F E hs m,
      (Y : Matrix (Fin m) (Fin m) E) = ∑ i, algebraMap F E (b.repr Y i) • v i := by
    intro Y
    conv_lhs => rw [← b.sum_repr Y]
    exact hcoe _
  have hmem' : ∀ Y : hermSub F E hs m,
      (Y : Matrix (Fin m) (Fin m) E) ∈ Submodule.span E (Set.range v) := by
    intro Y
    rw [hmem Y]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hstu : star ((u⁻¹ : Eˣ) : E) = -((u⁻¹ : Eˣ) : E) := by
    have a1 : (u : E) * ((u⁻¹ : Eˣ) : E) = 1 := Units.mul_inv u
    have a2 : star (u : E) = -(u : E) := by rw [hu, star_sub, star_star]; ring
    have a3 : star (u : E) * star ((u⁻¹ : Eˣ) : E) = 1 := by rw [← star_mul', a1, star_one]
    rw [a2] at a3
    linear_combination (-((u⁻¹ : Eˣ) : E)) * a3 - (star ((u⁻¹ : Eˣ) : E)) * a1
  have hsp : ⊤ ≤ Submodule.span E (Set.range v) := by
    intro X _
    let X2 : Matrix (Fin m) (Fin m) E := ((u⁻¹ : Eˣ) : E) • (X - X.conjTranspose)
    have hX2 : X2.conjTranspose = X2 := by
      simp only [X2]
      rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose,
        hstu, neg_smul, ← smul_neg, neg_sub]
    have hX1 : (X - ω • X2).conjTranspose = X - ω • X2 := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hX2]
      have a1 : (u : E) • X2 = X - X.conjTranspose := by
        simp only [X2]; rw [smul_smul, Units.mul_inv, one_smul]
      rw [hu, sub_smul] at a1
      rw [sub_eq_sub_iff_add_eq_add]
      have := a1
      rw [sub_eq_sub_iff_add_eq_add] at this
      rw [add_comm, this, add_comm]
    have : X = (X - ω • X2) + ω • X2 := by abel
    rw [this]
    exact Submodule.add_mem _ (hmem' ⟨_, hX1⟩) (Submodule.smul_mem _ _ (hmem' ⟨_, hX2⟩))
  let bE := Module.Basis.mk hli hsp
  have hbE : ∀ i, bE i = v i := fun i => Module.Basis.mk_apply hli hsp i
  have hmat : LinearMap.toMatrix bE bE (rmulE m A ∘ₗ lmulE m A.conjTranspose)
      = (algebraMap F E).mapMatrix (LinearMap.toMatrix b b (congrHerm F E hs m A)) := by
    ext i j
    rw [LinearMap.toMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply]
    have e1 : (rmulE m A ∘ₗ lmulE m A.conjTranspose) (bE j)
        = ∑ i, algebraMap F E (b.repr (congrHerm F E hs m A (b j)) i) • bE i := by
      simp only [hbE]
      rw [← hmem]
      rfl
    rw [e1, Module.Basis.repr_sum_self]
  apply (algebraMap F E).injective
  rw [map_pow, hj_norm_star hs h2 hfix, ← det_congrE, ← LinearMap.det_toMatrix bE, hmat,
    ← RingHom.map_det, LinearMap.det_toMatrix]
end Formalism.HermitianLatticeCounting.P.S4aux
