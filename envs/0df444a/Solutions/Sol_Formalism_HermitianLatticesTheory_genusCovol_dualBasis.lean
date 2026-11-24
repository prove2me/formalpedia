-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.genusCovol_dualBasis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:55:55.919796+00:00
-- url     : https://prove2.me/submissions/2a2fc504-473d-41dc-9ed6-dc3676ff5485

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_DefsCS
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusScale
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovolBound
import Definitions.Def_Formalism_FockGram_FockGramProofs_CovolGram
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovol
import Theorems.Thm_Formalism_E_covolumeEqSqrtDetGram
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovolBound_mem_zmap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (N : ℕ)
    (ι : V →+ EuclideanSpace ℝ (Fin N))
    (hι : ∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ))
    (M : Submodule (𝓞 K) V) [DiscreteTopology (zmap ι M)] [IsZLattice ℝ (zmap ι M)] :
    ∃ bv : Basis (Module.Free.ChooseBasisIndex ℤ (zmap ι M)) ℝ (EuclideanSpace ℝ (Fin N)),
      zmap ι (genusCovol_tdual h M) = Submodule.span ℤ (Set.range bv) ∧
      ZLattice.covolume (zmap ι M) * ZLattice.covolume (Submodule.span ℤ (Set.range bv)) = 1 := by
  classical
  set Λ := zmap ι M with hΛ
  let bz := Module.Free.chooseBasis ℤ Λ
  let bR := bz.ofZLatticeBasis ℝ Λ
  have hmem : ∀ i, ∃ m ∈ M, ι m = (bz i : EuclideanSpace ℝ (Fin N)) := fun i =>
    (genusCovolBound_mem_zmap N ι M _).mp (bz i).2
  choose m hmM hmι using hmem
  set b : V → V → ℚ := fun x y => Algebra.trace ℚ K (h x y) with hbdef
  have hb : ∀ x y, ((b x y : ℚ) : ℝ) = inner ℝ (ι x) (ι y) := fun x y => (hι x y).symm
  have hsymm : ∀ x y, b x y = b y x := fun x y => by
    have e := hb x y
    rw [real_inner_comm, ← hb] at e
    exact_mod_cast e
  set G : Matrix (Module.Free.ChooseBasisIndex ℤ Λ) (Module.Free.ChooseBasisIndex ℤ Λ) ℚ :=
    Matrix.of fun i j => b (m i) (m j) with hG
  have hgram : Matrix.gram ℝ bR = (Rat.castHom ℝ).mapMatrix G := by
    ext i j
    simp only [Matrix.gram_apply, bR, Basis.ofZLatticeBasis_apply, RingHom.mapMatrix_apply,
      Matrix.map_apply, hG, Matrix.of_apply, ← hmι]
    exact (hb _ _).symm
  have hcov : ZLattice.covolume Λ = Real.sqrt ((G.det : ℚ) : ℝ) := by
    have e := Formalism.E.covolumeEqSqrtDetGram (EuclideanSpace ℝ (Fin N)) _ bR
    rw [Basis.ofZLatticeBasis_span] at e
    rw [e, hgram, ← RingHom.map_det]
    rfl
  have hdetpos : 0 < G.det := by
    have := ZLattice.covolume_pos Λ
    rw [hcov, Real.sqrt_pos] at this
    exact_mod_cast this
  have hGsymm : G.transpose = G := by
    ext i j
    simp [hG, hsymm (m j) (m i)]
  have hGunit : IsUnit G.det := (ne_of_gt hdetpos).isUnit
  set Gi := G⁻¹ with hGi
  have hGiT : Gi.transpose = Gi := by rw [hGi, Matrix.transpose_nonsing_inv, hGsymm]
  have hGisymm : ∀ i j, Gi i j = Gi j i := by
    intro i j
    conv_lhs => rw [← hGiT]
    rfl
  set y : Module.Free.ChooseBasisIndex ℤ Λ → V :=
    fun i => ∑ j, (algebraMap ℚ K (Gi i j)) • m j with hy
  have hlin : ∀ x i, b x (y i) = ∑ j, Gi i j * b x (m j) := by
    intro x i
    simp only [hbdef, hy]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.map_smul, smul_eq_mul, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]
  have hdelta : ∀ k i, b (m k) (y i) = (1 : Matrix _ _ ℚ) k i := by
    intro k i
    rw [hlin]
    have e : (G * Gi) k i = (1 : Matrix _ _ ℚ) k i := by rw [hGi, Matrix.mul_nonsing_inv _ hGunit]
    rw [← e, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hGisymm i j, mul_comm]
    rfl
  have hint : ∀ i, ∀ x ∈ M, ∃ z : ℤ, b x (y i) = z := by
    intro i x hx
    have hxΛ : ι x ∈ Λ := (genusCovolBound_mem_zmap N ι M _).mpr ⟨x, hx, rfl⟩
    obtain ⟨c, hc⟩ : ∃ c, c = bz.repr ⟨ι x, hxΛ⟩ := ⟨_, rfl⟩
    refine ⟨c i, ?_⟩
    have hsum : ι x = ∑ k, ((c k : ℤ) : ℝ) • bR k := by
      conv_lhs => rw [← bR.sum_repr (ι x)]
      refine Finset.sum_congr rfl fun k _ => ?_
      have := Basis.ofZLatticeBasis_repr_apply ℝ Λ bz ⟨ι x, hxΛ⟩ k
      simp only at this
      rw [this, hc]
    have e : ((b x (y i) : ℚ) : ℝ) = (((c i : ℤ) : ℚ) : ℝ) := by
      rw [hb, hsum, sum_inner]
      simp_rw [real_inner_smul_left, bR, Basis.ofZLatticeBasis_apply, ← hmι, ← hb, hdelta]
      rw [Finset.sum_eq_single i (fun k _ hk => by simp [Matrix.one_apply, hk]) (by simp)]
      simp [Matrix.one_apply]
    exact_mod_cast e
  have hyy : ∀ i j, b (y i) (y j) = Gi j i := by
    intro i j
    rw [hlin]
    have e : ∀ l, Gi j l * b (y i) (m l) = Gi j l * (1 : Matrix _ _ ℚ) l i := by
      intro l
      rw [hsymm (y i) (m l), hdelta]
    rw [Finset.sum_congr rfl fun l _ => e l]
    simp [Matrix.one_apply]

  set v : Module.Free.ChooseBasisIndex ℤ Λ → EuclideanSpace ℝ (Fin N) := fun i => ι (y i) with hv
  have hRdelta : ∀ k i, inner ℝ (bR k) (v i) = if k = i then (1 : ℝ) else 0 := by
    intro k i
    simp only [bR, Basis.ofZLatticeBasis_apply, ← hmι, hv, ← hb, hdelta, Matrix.one_apply]
    split_ifs <;> simp
  have hli : LinearIndependent ℝ v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc k
    have := congrArg (fun u => inner ℝ (bR k) u) hc
    simp only [inner_sum, real_inner_smul_right, hRdelta, inner_zero_right] at this
    simpa using this
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ Λ) =
      finrank ℝ (EuclideanSpace ℝ (Fin N)) := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ Λ]
  let bv := basisOfLinearIndependentOfCardEqFinrank' v hli hcard
  have hbv : ∀ i, bv i = v i := fun i => by simp [bv, basisOfLinearIndependentOfCardEqFinrank']
  refine ⟨bv, ?_, ?_⟩
  · apply le_antisymm
    · intro u hu
      obtain ⟨w, hw, rfl⟩ := (genusCovolBound_mem_zmap N ι _ _).mp hu
      have hc : ∀ i, ∃ z : ℤ, b (m i) w = z := fun i => hw (m i) (hmM i)
      choose c hc using hc
      have e : ι w = ∑ i, (c i) • bv i := by
        apply InnerProductSpace.ext_inner_left_basis bR
        intro k
        rw [inner_sum]
        simp_rw [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right, hbv, hRdelta]
        simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
        simp only [bR, Basis.ofZLatticeBasis_apply, ← hmι, ← hb, hc]
        simp
      rw [e]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [hbv]
      exact (genusCovolBound_mem_zmap N ι _ _).mpr ⟨y i, hint i, rfl⟩
  · have e := Formalism.E.covolumeEqSqrtDetGram (EuclideanSpace ℝ (Fin N)) _ bv
    have hgv : Matrix.gram ℝ bv = (Rat.castHom ℝ).mapMatrix Gi := by
      ext i j
      simp only [Matrix.gram_apply, hbv, hv, RingHom.mapMatrix_apply, Matrix.map_apply, ← hb, hyy]
      rw [hGisymm]
      rfl
    rw [e, hgv, ← RingHom.map_det, hcov, hGi, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    have h0 : (0 : ℝ) ≤ ((G.det : ℚ) : ℝ) := by exact_mod_cast hdetpos.le
    change Real.sqrt ((G.det : ℚ) : ℝ) * Real.sqrt (((G.det)⁻¹ : ℚ) : ℝ) = 1
    rw [← Real.sqrt_mul h0, Rat.cast_inv, mul_inv_cancel₀ (by exact_mod_cast hdetpos.ne'),
      Real.sqrt_one]
end Formalism.HermitianLatticesTheory
